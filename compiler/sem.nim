#
#
#           The Nim Compiler
#        (c) Copyright 2013 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

# This module implements the semantic checking pass.

import
  ast, options, astalgo, trees,
  wordrecg, ropes, msgs, idents, renderer, types, platform,
  magicsys, nversion, nimsets, semfold, modulepaths, importer,
  procfind, lookups, pragmas, semdata, semtypinst, sigmatch,
  transf, vmdef, vm, aliases, cgmeth, lambdalifting,
  evaltempl, patterns, parampatterns, sempass2, linter, semmacrosanity,
  lowerings, plugins/active, lineinfos, int128,
  isolation_check, typeallowed, modulegraphs, enumtostr, concepts, astmsgs,
  extccomp, layeredtable

import vtables
import icprof
import std/[strtabs, math, tables, intsets, strutils, packedsets]

when not defined(leanCompiler):
  import spawn

when defined(nimVmRoundtripCheck):
  import vmvalue

when defined(nimPreviewSlimSystem):
  import std/[
    formatfloat,
    assertions,
  ]

# implementation

proc semExpr(c: PContext, n: PNode, flags: TExprFlags = {}, expectedType: PType = nil): PNode
proc semExprWithType(c: PContext, n: PNode, flags: TExprFlags = {}, expectedType: PType = nil): PNode
proc semExprNoType(c: PContext, n: PNode): PNode
proc semExprNoDeref(c: PContext, n: PNode, flags: TExprFlags = {}): PNode
proc semProcBody(c: PContext, n: PNode; expectedType: PType = nil): PNode

proc fitNode(c: PContext, formal: PType, arg: PNode; info: TLineInfo): PNode
proc changeType(c: PContext; n: PNode, newType: PType, check: bool)

proc semTypeNode(c: PContext, n: PNode, prev: PType): PType
proc semStmt(c: PContext, n: PNode; flags: TExprFlags): PNode
proc semOpAux(c: PContext, n: PNode)
proc semParamList(c: PContext, n, genericParams: PNode, s: PSym)
proc addParams(c: PContext, n: PNode, kind: TSymKind)
proc maybeAddResult(c: PContext, s: PSym, n: PNode)
proc tryExpr(c: PContext, n: PNode, flags: TExprFlags = {}): PNode
proc activate(c: PContext, n: PNode)
proc semQuoteAst(c: PContext, n: PNode): PNode
proc finishMethod(c: PContext, s: PSym)
proc evalAtCompileTime(c: PContext, n: PNode): PNode
proc indexTypesMatch(c: PContext, f, a: PType, arg: PNode): PNode
proc semStaticExpr(c: PContext, n: PNode; expectedType: PType = nil): PNode
proc semStaticType(c: PContext, childNode: PNode, prev: PType): PType
proc semTypeOf(c: PContext; n: PNode): PNode
proc computeRequiresInit(c: PContext, t: PType): bool
proc defaultConstructionError(c: PContext, t: PType, info: TLineInfo)
proc hasUnresolvedArgs(c: PContext, n: PNode): bool
proc isArrayConstr(n: PNode): bool {.inline.} =
  result = n.kind == nkBracket and
    n.typ.skipTypes(abstractInst).kind == tyArray

template semIdeForTemplateOrGenericCheck(conf, n, requiresCheck) =
  # we check quickly if the node is where the cursor is
  when defined(nimsuggest):
    if n.info.fileIndex == conf.m.trackPos.fileIndex and n.info.line == conf.m.trackPos.line:
      requiresCheck = true

proc declareResult(c: PContext, n: PNode): tuple[resultDeclared: bool, savedResultSym: PSym] =
  result = (false, nil)

  let owner = if not c.p.isNil: c.p.owner else: nil
  let resultType =
    if owner.isNil or owner.kind notin routineKinds:
      nil
    elif owner.kind == skMacro:
      sysTypeFromName(c.graph, n.info, "NimNode")
    elif not owner.typ.isNil and
        not owner.typ.returnType.isNil and
        not owner.typ.isInlineIterator:
      owner.typ.returnType
    else:
      nil

  if resultType.isNil:
    return

  result.savedResultSym = c.p.resultSym

  var res = newSym(skResult, getIdent(c.cache, "result"), c.idgen, owner, n.info)
  res.typ = resultType
  incl(res.flagsImpl, sfUsed)
  c.p.resultSym = res
  addDecl(c, res)
  result.resultDeclared = true

template semIdeForTemplateOrGeneric(c: PContext; n: PNode;
                                    requiresCheck: bool) =
  # use only for idetools support; this is pretty slow so generics and
  # templates perform some quick check whether the cursor is actually in
  # the generic or template.
  when defined(nimsuggest):
    if c.config.ideActive and requiresCheck:
      #if optIdeDebug in gGlobalOptions:
      #  echo "passing to safeSemExpr: ", renderTree(n)
      # Speculatively sem a *copy* of the body in its own scope: `semExpr`
      # rewrites the tree in place, and whatever does not resolve with the
      # generic parameters unbound would turn into error nodes in the stored
      # body that instantiations and `m.ast` lookups (v2 `use`) rely on.
      openScope(c)
      # The pre-pass declares `result` as `skUnknown` so that it stays an
      # identifier in the generic body; give it its real type here, otherwise
      # every `result = f(...)` fails on the left-hand side and the right-hand
      # side (where the cursor usually is) is never analysed.
      let (resultDeclared, savedResultSym) = declareResult(c, n)
      # `ESuggestDone` may escape here; `recoverContext` then resets the
      # scopes and proc-cons, so no `finally` is needed.
      discard safeSemExpr(c, copyTree(n))
      if resultDeclared: c.p.resultSym = savedResultSym
      closeScope(c)

proc fitNodePostMatch(c: PContext, formal: PType, arg: PNode): PNode =
  let x = arg.skipConv
  if (x.kind == nkCurly and formal.kind == tySet and formal.base.kind != tyGenericParam) or
    (x.kind in {nkPar, nkTupleConstr}) and formal.kind notin {tyUntyped, tyBuiltInTypeClass, tyAnything}:
    changeType(c, x, formal, check=true)
  result = arg
  result = skipHiddenSubConv(result, c.graph, c.idgen)
  # Walk through nested statement-list/block expressions to find the innermost
  # value node. Empty containers (e.g. `@[]`) inside `nkStmtListExpr` wrappers
  # need their type resolved to match the formal type, otherwise the C codegen
  # cannot map `tyEmpty` to a concrete type (fixes #25945).
  var tail = result
  while tail.kind in {nkStmtList, nkStmtListExpr, nkBlockStmt, nkBlockExpr, nkPragmaBlock} and tail.len > 0:
    tail = tail.lastSon

  if tail.typ != nil and tail.typ.isEmptyContainer and
        formal.kind notin {tyUntyped, tyBuiltInTypeClass, tyAnything}:
    changeType(c, tail, formal, check=true)

  # mark inserted converter as used:
  var a = result
  if a.kind == nkHiddenDeref: a = a[0]
  if a.kind == nkHiddenCallConv and a[0].kind == nkSym:
    markUsed(c, a.info, a[0].sym)


proc fitNode(c: PContext, formal: PType, arg: PNode; info: TLineInfo): PNode =
  if arg.typ.isNil:
    localError(c.config, arg.info, "expression has no type: " &
               renderTree(arg, {renderNoComments}))
    # error correction:
    result = copyTree(arg)
    result.typ = formal
  elif arg.kind in nkSymChoices and formal.skipTypes(abstractInst).kind == tyEnum:
    # Pick the right 'sym' from the sym choice by looking at 'formal' type:
    # The choice candidates may be wrapped in `var`/`lent` when they come from
    # a loop-local view, but for enum disambiguation only the underlying enum
    # type matters.
    result = nil
    for ch in arg:
      if sameType(ch.typ.skipTypes({tyVar, tyLent}), formal):
        return ch
    typeMismatch(c.config, info, formal, arg.typ, arg)
  else:
    result = indexTypesMatch(c, formal, arg.typ, arg)
    if result == nil:
      typeMismatch(c.config, info, formal, arg.typ, arg)
      # error correction:
      result = copyTree(arg)
      result.typ = formal
    else:
      result = fitNodePostMatch(c, formal, result)

proc fitNodeConsiderViewType(c: PContext, formal: PType, arg: PNode; info: TLineInfo): PNode =
  let a = fitNode(c, formal, arg, info)
  if formal.kind in {tyVar, tyLent}:
    #classifyViewType(formal) != noView:
    result = newNodeIT(nkHiddenAddr, a.info, formal)
    result.add a
    formal.incl tfVarIsPtr
  else:
   result = a

proc inferWithMetatype(c: PContext, formal: PType,
                       arg: PNode, coerceDistincts = false): PNode

template commonTypeBegin*(): PType = PType(kind: tyUntyped)

proc commonType*(c: PContext; x, y: PType): PType =
  # new type relation that is used for array constructors,
  # if expressions, etc.:
  if x == nil: return x
  if y == nil: return y
  var a = skipTypes(x, {tyGenericInst, tyAlias, tySink})
  var b = skipTypes(y, {tyGenericInst, tyAlias, tySink})
  result = x
  if a.kind in {tyUntyped, tyNil}: result = y
  elif b.kind in {tyUntyped, tyNil}: result = x
  elif a.kind == tyTyped: result = a
  elif b.kind == tyTyped: result = b
  elif a.kind == tyTypeDesc:
    # turn any concrete typedesc into the abstract typedesc type
    if not a.hasElementType: result = a
    else:
      result = newType(tyTypeDesc, c.idgen, a.owner)
      rawAddSon(result, newType(tyNone, c.idgen, a.owner))
  elif b.kind in {tyArray, tySet, tySequence} and
      a.kind == b.kind:
    # check for seq[empty] vs. seq[int]
    let idx = ord(b.kind == tyArray)
    if a[idx].kind == tyEmpty: return y
  elif a.kind == tyTuple and b.kind == tyTuple and sameTupleLengths(a, b):
    var nt: PType = nil
    for i, aa, bb in tupleTypePairs(a, b):
      let aEmpty = isEmptyContainer(aa)
      let bEmpty = isEmptyContainer(bb)
      if aEmpty != bEmpty:
        if nt.isNil:
          nt = copyType(a, c.idgen, a.owner)
          copyTypeProps(c.graph, c.idgen.module, nt, a)

        nt[i] = if aEmpty: bb else: aa
    if not nt.isNil: result = nt
    #elif b[idx].kind == tyEmpty: return x
  elif a.kind == tyRange and b.kind == tyRange:
    # consider:  (range[0..3], range[0..4]) here. We should make that
    # range[0..4]. But then why is (range[0..4], 6) not range[0..6]?
    # But then why is (2,4) not range[2..4]? But I think this would break
    # too much code. So ... it's the same range or the base type. This means
    #  typeof(if b: 0 else 1) == int and not range[0..1]. For now. In the long
    # run people expect ranges to work properly within a tuple.
    if not sameType(a, b):
      result = skipTypes(a, {tyRange}).skipIntLit(c.idgen)
    when false:
      if a.kind != tyRange and b.kind == tyRange:
        # XXX This really needs a better solution, but a proper fix now breaks
        # code.
        result = a #.skipIntLit
      elif a.kind == tyRange and b.kind != tyRange:
        result = b #.skipIntLit
      elif a.kind in IntegralTypes and a.n != nil:
        result = a #.skipIntLit
  elif a.kind == tyProc and b.kind == tyProc:
    if a.callConv == ccClosure and b.callConv != ccClosure:
      result = x
    elif compatibleEffects(a, b) != efCompat or
        (b.flags * {tfNoSideEffect, tfGcSafe}) < (a.flags * {tfNoSideEffect, tfGcSafe}):
      result = y
  else:
    var k = tyNone
    if a.kind in {tyRef, tyPtr}:
      k = a.kind
      if b.kind != a.kind: return x
      # bug #7601, array construction of ptr generic
      a = a.elementType.skipTypes({tyGenericInst})
      b = b.elementType.skipTypes({tyGenericInst})
    if a.kind == tyObject and b.kind == tyObject:
      result = commonSuperclass(a, b)
      # this will trigger an error later:
      if result.isNil or result == a: return x
      if result == b: return y
      # bug #7906, tyRef/tyPtr + tyGenericInst of ref/ptr object ->
      # ill-formed AST, no need for additional tyRef/tyPtr
      if k != tyNone and x.kind != tyGenericInst and
          # the base can be an instance of a generic `ref object` (#7955)
          result.skipTypes({tyGenericInst, tyAlias}).kind != k:
        let r = result
        result = newType(k, c.idgen, r.owner)
        result.addSonSkipIntLit(r, c.idgen)

const shouldChckCovered = {tyInt..tyInt64, tyChar, tyEnum, tyUInt..tyUInt64, tyBool}
proc shouldCheckCaseCovered(caseTyp: PType): bool =
  result = false
  case caseTyp.kind
  of shouldChckCovered:
    result = true
  of tyRange:
    if skipTypes(caseTyp[0], abstractInst).kind in shouldChckCovered:
      result = true
  else:
    discard

proc endsInNoReturn(n: PNode): bool

proc commonType*(c: PContext; x: PType, y: PNode): PType =
  # ignore exception raising branches in case/if expressions
  if endsInNoReturn(y): return x
  commonType(c, x, y.typ)

proc newSymS(kind: TSymKind, n: PNode, c: PContext): PSym =
  result = newSym(kind, considerQuotedIdent(c, n), c.idgen, getCurrOwner(c), n.info)
  when defined(nimsuggest):
    suggestDecl(c, n, result)

proc newSymG*(kind: TSymKind, n: PNode, c: PContext): PSym =
  # like newSymS, but considers gensym'ed symbols
  if n.kind == nkSym:
    # and sfGenSym in n.sym.flags:
    result = n.sym
    if result.kind notin {kind, skTemp}:
      localError(c.config, n.info, "cannot use symbol of kind '$1' as a '$2'" %
        [result.kind.toHumanStr, kind.toHumanStr])
    # bug #25693: a local declared inside a template/macro operand (recorded in
    # `shadowDiscardedDefs`) can be captured by a `{.dirty.}` template and
    # re-emitted as a definition more than once. The first emission keeps the
    # original symbol (so a leaked dirty-template name still resolves); every
    # later emission gets a fresh copy, so distinct emissions don't share one
    # symbol - which the destructor/liveness analysis would otherwise miscompile.
    # Unlike a plain redefinition check this is control-flow agnostic, so the
    # common "emit a `typed` body in several mutually-exclusive branches" pattern
    # keeps working. gensym'ed locals (and ones derived from a gensym name) are
    # excluded: the gensym machinery already keeps their names unique, and a
    # fresh copy would reuse the unique name and clash in the same scope.
    if kind in {skVar, skLet, skForVar} and
        {sfGenSym, sfWasGenSym} * result.flags == {} and
        result.id in c.shadowDiscardedDefs:
      if containsOrIncl(c.realizedDefs, result.id):
        let fresh = copySym(result, c.idgen)
        fresh.ast = result.ast
        put(c.p, result, fresh)
        c.hasSymRedefs = true
        result = fresh
    when false:
      if sfGenSym in result.flags and result.kind notin {skTemplate, skMacro, skParam}:
        # declarative context, so produce a fresh gensym:
        result = copySym(result)
        result.ast = n.sym.ast
        put(c.p, n.sym, result)
    if result.state == Sealed:
      # the symbol was loaded from another module's NIF cache (e.g. a param
      # symbol spliced out of an imported proc type by a `typed` macro) and is
      # therefore immutable; the caller re-owns it and assigns its type/flags,
      # so hand back a fresh, mutable copy owned by the current module instead.
      let fresh = copySym(result, c.idgen)
      fresh.ast = result.ast
      result = fresh
    # when there is a nested proc inside a template, semtmpl
    # will assign a wrong owner during the first pass over the
    # template; we must fix it here: see #909
    setOwner(result, getCurrOwner(c))
  else:
    result = newSym(kind, considerQuotedIdent(c, n), c.idgen, getCurrOwner(c), n.info)
    if find(result.name.s, '`') >= 0:
      result.flagsImpl.incl sfWasGenSym
  #if kind in {skForVar, skLet, skVar} and result.owner.kind == skModule:
  #  incl(result.flags, sfGlobal)
  when defined(nimsuggest):
    suggestDecl(c, n, result)

proc semIdentVis(c: PContext, kind: TSymKind, n: PNode,
                 allowed: TSymFlags): PSym
  # identifier with visibility
proc semIdentWithPragma(c: PContext, kind: TSymKind, n: PNode,
                        allowed: TSymFlags, fromTopLevel = false): PSym

proc typeAllowedCheck(c: PContext; info: TLineInfo; typ: PType; kind: TSymKind;
                      flags: TTypeAllowedFlags = {}) =
  let t = typeAllowed(typ, kind, c, flags)
  if t != nil:
    var err: string
    if t == typ:
      err = "invalid type: '$1' for $2" % [typeToString(typ), toHumanStr(kind)]
      if kind in {skVar, skLet, skConst} and taIsTemplateOrMacro in flags:
        err &= ". Did you mean to call the $1 with '()'?" % [toHumanStr(typ.owner.kind)]
    else:
      err = "invalid type: '$1' in this context: '$2' for $3" % [typeToString(t),
              typeToString(typ), toHumanStr(kind)]
    localError(c.config, info, err)

proc paramsTypeCheck(c: PContext, typ: PType) {.inline.} =
  typeAllowedCheck(c, typ.n.info, typ, skProc)

proc semDirectOp(c: PContext, n: PNode, flags: TExprFlags; expectedType: PType = nil): PNode
proc semWhen(c: PContext, n: PNode, semCheck: bool = true): PNode
proc semTemplateExpr(c: PContext, n: PNode, s: PSym,
                     flags: TExprFlags = {}; expectedType: PType = nil): PNode
proc semMacroExpr(c: PContext, n, nOrig: PNode, sym: PSym,
                  flags: TExprFlags = {}; expectedType: PType = nil): PNode

when false:
  proc createEvalContext(c: PContext, mode: TEvalMode): PEvalContext =
    result = newEvalContext(c.module, mode)
    result.getType = proc (n: PNode): PNode =
      result = tryExpr(c, n)
      if result == nil:
        result = newSymNode(errorSym(c, n))
      elif result.typ == nil:
        result = newSymNode(getSysSym"void")
      else:
        result.typ = makeTypeDesc(c, result.typ)

    result.handleIsOperator = proc (n: PNode): PNode =
      result = isOpImpl(c, n)

proc hasCycle(n: PNode): bool =
  result = false
  incl n.flags, nfNone
  for i in 0..<n.safeLen:
    if nfNone in n[i].flags or hasCycle(n[i]):
      result = true
      break
  excl n.flags, nfNone

proc fixupTypeAfterEval(c: PContext, evaluated, eOrig: PNode; producedClosure: var bool): PNode =
  # recompute the types as 'eval' isn't guaranteed to construct types nor
  # that the types are sound:
  when true:
    if eOrig.typ.kind in {tyUntyped, tyTyped, tyTypeDesc}:
      result = semExprWithType(c, evaluated)
    else:
      result = evaluated
      let expectedType = eOrig.typ.skipTypes({tyStatic})
      if hasCycle(result):
        result = localErrorNode(c, eOrig, "the resulting AST is cyclic and cannot be processed further")
      else:
        semmacrosanity.annotateType(result, expectedType, c.config, producedClosure)
  else:
    result = semExprWithType(c, evaluated)
    #result = fitNode(c, e.typ, result) inlined with special case:
    let arg = result
    result = indexTypesMatch(c, eOrig.typ, arg.typ, arg)
    if result == nil:
      result = arg
      # for 'tcnstseq' we support [] to become 'seq'
      if eOrig.typ.skipTypes(abstractInst).kind == tySequence and
         isArrayConstr(arg):
        arg.typ = eOrig.typ

proc resetEvalPosition(n: PNode) =
  # resets the eval position of variables because `tryConstExpr` may be
  # called multiple times on the same node
  case n.kind
  of {nkNone..nkNilLit}-{nkSym}:
    discard
  of nkSym:
    if n.sym.kind in {skVar, skLet} and sfGlobal notin n.sym.flags:
      n.sym.position = 0
  else:
    for i in 0..<n.safeLen:
      resetEvalPosition(n[i])

proc tryConstExpr(c: PContext, n: PNode; expectedType: PType = nil): PNode =
  var e = semExprWithType(c, n, expectedType = expectedType)
  if e == nil: return

  result = getConstExpr(c.module, e, c.idgen, c.graph)
  if result != nil: return

  let oldErrorCount = c.config.errorCounter
  let oldErrorMax = c.config.errorMax
  let oldErrorOutputs = c.config.m.errorOutputs

  c.config.m.errorOutputs = {}
  c.config.errorMax = high(int) # `setErrorMaxHighMaybe` not appropriate here

  when defined(nimsuggest):
    # Remove the error hook so nimsuggest doesn't report errors there
    let tempHook = c.graph.config.structuredErrorHook
    c.graph.config.structuredErrorHook = nil

  try:
    result = evalConstExpr(c.module, c.idgen, c.graph, e, c)
    if result == nil or result.kind == nkEmpty:
      result = nil
    else:
      var producedClosure = false
      result = fixupTypeAfterEval(c, result, e, producedClosure)
      if producedClosure:
        result = nil

  except ERecoverableError:
    result = nil

  when defined(nimsuggest):
    # Restore the error hook
    c.graph.config.structuredErrorHook = tempHook

  resetEvalPosition(n)

  c.config.errorCounter = oldErrorCount
  c.config.errorMax = oldErrorMax
  c.config.m.errorOutputs = oldErrorOutputs

const
  errConstExprExpected = "constant expression expected"

proc semConstExpr(c: PContext, n: PNode; expectedType: PType = nil): PNode =
  var e = semExprWithType(c, n, expectedType = expectedType)
  if e == nil:
    localError(c.config, n.info, errConstExprExpected)
    return n
  if e.kind in nkSymChoices and e[0].typ.skipTypes(abstractInst).kind == tyEnum:
    return e
  result = getConstExpr(c.module, e, c.idgen, c.graph)
  if result == nil:
    #if e.kind == nkEmpty: globalError(n.info, errConstExprExpected)
    result = evalConstExpr(c.module, c.idgen, c.graph, e, c)
    if result == nil or result.kind == nkEmpty:
      if e.info != n.info:
        pushInfoContext(c.config, n.info)
        localError(c.config, e.info, errConstExprExpected)
        popInfoContext(c.config)
      else:
        localError(c.config, e.info, errConstExprExpected)
      # error correction:
      result = e
    else:
      var producedClosure = false
      result = fixupTypeAfterEval(c, result, e, producedClosure)
      if producedClosure:
        result = nil

proc semExprFlagDispatched(c: PContext, n: PNode, flags: TExprFlags; expectedType: PType = nil): PNode =
  if efNeedStatic in flags:
    if efPreferNilResult in flags:
      return tryConstExpr(c, n, expectedType)
    else:
      return semConstExpr(c, n, expectedType)
  else:
    result = semExprWithType(c, n, flags, expectedType)
    if efPreferStatic in flags:
      var evaluated = getConstExpr(c.module, result, c.idgen, c.graph)
      if evaluated != nil: return evaluated
      evaluated = evalAtCompileTime(c, result)
      if evaluated != nil: return evaluated

proc semGenericStmt(c: PContext, n: PNode): PNode

include hlo, seminst, semcall

proc resetSemFlag(n: PNode) =
  if n != nil:
    excl n.flags, nfSem
    for i in 0..<n.safeLen:
      resetSemFlag(n[i])

proc semAfterMacroCall(c: PContext, call, macroResult: PNode,
                       s: PSym, flags: TExprFlags; expectedType: PType = nil): PNode =
  ## Semantically check the output of a macro.
  ## This involves processes such as re-checking the macro output for type
  ## coherence, making sure that variables declared with 'let' aren't
  ## reassigned, and binding the unbound identifiers that the macro output
  ## contains.
  inc(c.config.evalTemplateCounter)
  if c.config.evalTemplateCounter > evalTemplateLimit:
    globalError(c.config, s.info, "template instantiation too nested")
  c.friendModules.add(s.owner.getModule)
  result = macroResult
  resetSemFlag result
  if s.typ.returnType == nil:
    result = semStmt(c, result, flags)
  else:
    var retType = s.typ.returnType
    if retType.kind == tyTypeDesc and tfUnresolved in retType.flags and
        retType.hasElementType:
      # bug #11941: template fails(T: type X, v: auto): T
      # does not mean we expect a tyTypeDesc.
      retType = retType.skipModifier
    case retType.kind
    of tyUntyped, tyAnything:
      # Not expecting a type here allows templates like in ``tmodulealias.in``.
      result = semExpr(c, result, flags, expectedType)
    of tyTyped:
      # More restrictive version.
      result = semExprWithType(c, result, flags, expectedType)
    of tyTypeDesc:
      if result.kind == nkStmtList: result.transitionSonsKind(nkStmtListType)
      var typ = semTypeNode(c, result, nil)
      if typ == nil:
        localError(c.config, result.info, "expression has no type: " &
                   renderTree(result, {renderNoComments}))
        result = newSymNode(errorSym(c, result))
      else:
        result.typ = makeTypeDesc(c, typ)
      #result = symNodeFromType(c, typ, n.info)
    else:
      if s.ast[genericParamsPos] != nil and retType.isMetaType:
        # The return type may depend on the Macro arguments
        # e.g. template foo(T: typedesc): seq[T]
        # We will instantiate the return type here, because
        # we now know the supplied arguments
        var paramTypes = initLayeredTypeMap()
        for param, value in genericParamsInMacroCall(s, call):
          var givenType = value.typ
          # the sym nodes used for the supplied generic arguments for
          # templates and macros leave type nil so regular sem can handle it
          # in this case, get the type directly from the sym
          if givenType == nil and value.kind == nkSym and value.sym.typ != nil:
            givenType = value.sym.typ
          put(paramTypes, param.typ, givenType)

        retType = generateTypeInstance(c, paramTypes,
                                       macroResult.info, retType)

      if retType.kind == tyVoid:
        result = semStmt(c, result, flags)
      else:
        result = semExpr(c, result, flags)
        result = fitNode(c, retType, result, result.info)
      #globalError(s.info, errInvalidParamKindX, typeToString(s.typ.returnType))
  dec(c.config.evalTemplateCounter)
  discard c.friendModules.pop()

proc getLineInfo(n: PNode): TLineInfo =
  case n.kind
  of nkPostfix:
    if len(n) > 1:
      result = getLineInfo(n[1])
    else:
      result = n.info
  of nkAccQuoted, nkPragmaExpr:
    if len(n) > 0:
      result = getLineInfo(n[0])
    else:
      result = n.info
  else:
    result = n.info

const
  errMissingGenericParamsForTemplate = "'$1' has unspecified generic parameters"

proc semMacroExpr(c: PContext, n, nOrig: PNode, sym: PSym,
                  flags: TExprFlags = {}; expectedType: PType = nil): PNode =
  let info = getCallLineInfo(n)
  # the callee identifier's position is the usage site tooling expects (matches
  # `markUsed` below), not the whole-call `nOrig.info`.
  rememberExpansion(c, info, sym)
  pushInfoContext(c.config, nOrig.info, sym.detailedInfo)

  markUsed(c, info, sym)
  onUse(info, sym)
  if sym == c.p.owner:
    globalError(c.config, info, "recursive dependency: '$1'" % sym.name.s)

  let genericParams = sym.ast[genericParamsPos].len
  let suppliedParams = max(n.safeLen - 1, 0)

  if suppliedParams < genericParams:
    globalError(c.config, info, errMissingGenericParamsForTemplate % n.renderTree)

  #if c.evalContext == nil:
  #  c.evalContext = c.createEvalContext(emStatic)
  result = evalMacroCall(c.module, c.idgen, c.graph, c.templInstCounter, n, nOrig, sym, c)
  if efNoSemCheck notin flags:
    result = semAfterMacroCall(c, n, result, sym, flags, expectedType)
  if c.config.macrosToExpand.hasKey(sym.name.s):
    message(c.config, nOrig.info, hintExpandMacro, renderTree(result, {
      renderNonExportedFields, renderDocComments, renderNoComments
    }))
  result = wrapInComesFrom(nOrig.info, sym, result)
  popInfoContext(c.config)

proc forceBool(c: PContext, n: PNode): PNode =
  result = fitNode(c, getSysType(c.graph, n.info, tyBool), n, n.info)
  if result == nil: result = n

proc semConstBoolExpr(c: PContext, n: PNode): PNode =
  result = forceBool(c, semConstExpr(c, n, getSysType(c.graph, n.info, tyBool)))
  if result.kind != nkIntLit:
    localError(c.config, n.info, errConstExprExpected)
proc semConceptBody(c: PContext, n: PNode): PNode

include semtypes

proc setGenericParamsMisc(c: PContext; n: PNode) =
  ## used by call defs (procs, templates, macros, ...) to analyse their generic
  ## params, and store the originals in miscPos for better error reporting.
  let orig = n[genericParamsPos]

  doAssert orig.kind in {nkEmpty, nkGenericParams}

  if n[genericParamsPos].kind == nkEmpty:
    n[genericParamsPos] = newNodeI(nkGenericParams, n.info)
  else:
    # we keep the original params around for better error messages, see
    # issue https://github.com/nim-lang/Nim/issues/1713
    n[genericParamsPos] = semGenericParamList(c, orig)

  if n[miscPos].kind == nkEmpty:
    n[miscPos] = newTree(nkBracket, c.graph.emptyNode, orig)
  else:
    n[miscPos][1] = orig

proc caseBranchMatchesExpr(branch, matched: PNode): bool =
  result = false
  for i in 0 ..< branch.len-1:
    if branch[i].kind == nkRange:
      if overlap(branch[i], matched): return true
    elif exprStructuralEquivalent(branch[i], matched):
      return true

proc pickCaseBranchIndex(caseExpr, matched: PNode): int =
  result = 0
  let endsWithElse = caseExpr[^1].kind == nkElse
  for i in 1..<caseExpr.len - endsWithElse.int:
    if caseExpr[i].caseBranchMatchesExpr(matched):
      return i
  if endsWithElse:
    return caseExpr.len - 1

proc defaultFieldsForTheUninitialized(c: PContext, recNode: PNode, checkDefault: bool): seq[PNode]
proc defaultNodeField(c: PContext, a: PNode, aTyp: PType, checkDefault: bool): PNode
proc defaultNodeField(c: PContext, a: PNode, checkDefault: bool): PNode

const defaultFieldsSkipTypes = {tyGenericInst, tyAlias, tySink}

proc defaultFieldsForTuple(c: PContext, recNode: PNode, hasDefault: var bool, checkDefault: bool): seq[PNode] =
  result = @[]
  case recNode.kind
  of nkRecList:
    for field in recNode:
      result.add defaultFieldsForTuple(c, field, hasDefault, checkDefault)
  of nkSym:
    let field = recNode.sym
    let recType = recNode.typ.skipTypes(defaultFieldsSkipTypes)
    if field.ast != nil: #Try to use default value
      hasDefault = true
      result.add newTree(nkExprColonExpr, recNode, field.ast)
    else:
      if recType.kind in {tyObject, tyArray, tyTuple}:
        let asgnExpr = defaultNodeField(c, recNode, recNode.typ, checkDefault)
        if asgnExpr != nil:
          hasDefault = true
          asgnExpr.flags.incl nfSkipFieldChecking
          result.add newTree(nkExprColonExpr, recNode, asgnExpr)
          return

      let asgnType = newType(tyTypeDesc, c.idgen, recNode.typ.owner)
      rawAddSon(asgnType, recNode.typ)
      let asgnExpr = newTree(nkCall,
                      newSymNode(getSysMagic(c.graph, recNode.info, "zeroDefault", mZeroDefault)),
                      newNodeIT(nkType, recNode.info, asgnType)
                    )
      asgnExpr.flags.incl nfSkipFieldChecking
      asgnExpr.typ = recNode.typ
      result.add newTree(nkExprColonExpr, recNode, asgnExpr)
  else:
    raiseAssert "unreachable"

proc defaultFieldsForTheUninitialized(c: PContext, recNode: PNode, checkDefault: bool): seq[PNode] =
  result = @[]
  case recNode.kind
  of nkRecList:
    for field in recNode:
      result.add defaultFieldsForTheUninitialized(c, field, checkDefault)
  of nkRecCase:
    let discriminator = recNode[0]
    var selectedBranch: int
    var defaultValue = discriminator.sym.ast
    if defaultValue == nil:
      # None of the branches were explicitly selected by the user and no value
      # was given to the discrimator. We can assume that it will be initialized
      # to zero and this will select a particular branch as a result:
      if checkDefault: # don't add defaults when checking whether a case branch has default fields
        return
      defaultValue = newIntNode(nkIntLit#[c.graph]#, 0)
      defaultValue.typ = discriminator.typ
    selectedBranch = recNode.pickCaseBranchIndex defaultValue
    defaultValue.flags.incl nfSkipFieldChecking
    result.add newTree(nkExprColonExpr, discriminator, defaultValue)
    result.add defaultFieldsForTheUninitialized(c, recNode[selectedBranch][^1], checkDefault)
  of nkSym:
    let field = recNode.sym
    let recType = recNode.typ.skipTypes(defaultFieldsSkipTypes)
    if field.ast != nil: #Try to use default value
      result.add newTree(nkExprColonExpr, recNode, field.ast)
    elif recType.kind in {tyObject, tyArray, tyTuple}:
      let asgnExpr = defaultNodeField(c, recNode, recNode.typ, checkDefault)
      if asgnExpr != nil:
        asgnExpr.typ = recNode.typ
        asgnExpr.flags.incl nfSkipFieldChecking
        result.add newTree(nkExprColonExpr, recNode, asgnExpr)
  else:
    raiseAssert "unreachable"

proc defaultNodeField(c: PContext, a: PNode, aTyp: PType, checkDefault: bool): PNode =
  let aTypSkip = aTyp.skipTypes(defaultFieldsSkipTypes)
  case aTypSkip.kind
  of tyObject:
    let child = defaultFieldsForTheUninitialized(c, aTypSkip.n, checkDefault)
    if child.len > 0:
      var asgnExpr = newTree(nkObjConstr, newNodeIT(nkType, a.info, aTyp))
      asgnExpr.typ = aTyp
      asgnExpr.sons.add child
      result = semExpr(c, asgnExpr)
    else:
      result = nil
  of tyArray:
    let child = defaultNodeField(c, a, aTypSkip[1], checkDefault)

    if child != nil:
      let node = newNode(nkIntLit)
      node.intVal = toInt64(lengthOrd(c.graph.config, aTypSkip))
      let typeNode = newNode(nkType)
      typeNode.typ = makeTypeDesc(c, aTypSkip[1])
      result = semExpr(c, newTree(nkCall, newTree(nkBracketExpr, newSymNode(getSysSym(c.graph, a.info, "arrayWithDefault"), a.info), typeNode),
              node
                ))
      result.typ = aTyp
    else:
      result = nil
  of tyTuple:
    var hasDefault = false
    if aTypSkip.n != nil:
      let children = defaultFieldsForTuple(c, aTypSkip.n, hasDefault, checkDefault)
      if hasDefault and children.len > 0:
        result = newNodeI(nkTupleConstr, a.info)
        result.typ = aTyp
        result.sons.add children
        result = semExpr(c, result)
      else:
        result = nil
    else:
      result = nil
  of tyRange:
    if c.graph.config.isDefined("nimPreviewRangeDefault"):
      result = firstRange(c.config, aTypSkip)
    else:
      result = nil
  else:
    result = nil

proc defaultNodeField(c: PContext, a: PNode, checkDefault: bool): PNode =
  result = defaultNodeField(c, a, a.typ, checkDefault)

proc sumTypeBranchCandidates(c: PContext; n: PNode): seq[PSym]

proc isSumTypePattern(c: PContext; n: PNode): bool =
  ## Whether `n`, a pattern of an `of` branch, is `Branch(bindings)` or
  ## `{A, B}(bindings)` of a sum type: the bindings are declarations then.
  if n.kind notin nkCallKinds or n.len < 2: return false
  let head = if n[0].kind == nkCurly and n[0].len > 0: n[0][0] else: n[0]
  result = sumTypeBranchCandidates(c, head).len > 0

include semtempl, semgnrc, semstmts, semexprs

proc addCodeForGenerics(c: PContext, n: PNode) =
  for i in c.lastGenericIdx..<c.generics.len:
    var prc = c.generics[i].inst.sym
    if prc.kind in {skProc, skFunc, skMethod, skConverter} and prc.magic == mNone:
      if prc.ast == nil or prc.ast[bodyPos] == nil:
        internalError(c.config, prc.info, "no code for " & prc.name.s)
      else:
        n.add prc.ast
  c.lastGenericIdx = c.generics.len

proc preparePContext*(graph: ModuleGraph; module: PSym; idgen: IdGenerator): PContext =
  result = newContext(graph, module)
  result.idgen = idgen
  result.enforceVoidContext = newType(tyTyped, idgen, nil)
  result.voidType = newType(tyVoid, idgen, nil)

  if result.p != nil: internalError(graph.config, module.info, "sem.preparePContext")
  result.semConstExpr = semConstExpr
  result.semExpr = semExpr
  result.semExprWithType = semExprWithType
  result.semTryExpr = tryExpr
  result.semTryConstExpr = tryConstExpr
  result.computeRequiresInit = computeRequiresInit
  result.semOperand = semOperand
  result.semConstBoolExpr = semConstBoolExpr
  result.semOverloadedCall = semOverloadedCall
  result.semInferredLambda = semInferredLambda
  result.semGenerateInstance = generateInstance
  result.instantiateOnlyProcType = instantiateOnlyProcType
  result.fitDefaultNode = fitDefaultNode
  result.semTypeNode = semTypeNode
  result.instTypeBoundOp = sigmatch.instTypeBoundOp
  result.hasUnresolvedArgs = hasUnresolvedArgs
  result.semAsgnOpr = semAsgnOpr
  result.templInstCounter = new int

  # `--deferBodies:on`: a top-level `const`/`static:` can reach a body that the
  # body pass has not run yet, and `transformBody` asks for it here. Modules
  # nest (an import is compiled from inside the importer's pass), so keep the
  # enclosing module's hook and put it back in `closePContext`.
  if optDeferBodies in graph.config.globalOptions:
    result.prevDemandRoutineBody = graph.demandRoutineBody
    let ctx = result
    graph.demandRoutineBody = proc (prc: PSym) = demandRoutineBody(ctx, prc)

  pushProcCon(result, module)
  pushOwner(result, result.module)

  result.moduleScope = openScope(result)
  result.moduleScope.addSym(module) # a module knows itself

  if sfSystemModule in module.flags:
    graph.systemModule = module
  result.topLevelScope = openScope(result)

proc isImportSystemStmt(g: ModuleGraph; n: PNode): bool =
  if g.systemModule == nil: return false
  var n = n
  if n.kind == nkStmtList:
    for i in 0..<n.len-1:
      if n[i].kind notin {nkCommentStmt, nkEmpty}:
        n = n[i]
        break
  case n.kind
  of nkImportStmt:
    result = false
    for x in n:
      if x.kind == nkIdent:
        let f = checkModuleName(g.config, x, false)
        if f == g.systemModule.info.fileIndex:
          return true
  of nkImportExceptStmt, nkFromStmt:
    result = false
    if n[0].kind == nkIdent:
      let f = checkModuleName(g.config, n[0], false)
      if f == g.systemModule.info.fileIndex:
        return true
  else: result = false

proc isEmptyTree(n: PNode): bool =
  case n.kind
  of nkStmtList:
    for it in n:
      if not isEmptyTree(it): return false
    result = true
  of nkEmpty, nkCommentStmt: result = true
  else: result = false

proc importSystemOnce(c: PContext, n: PNode) =
  if c.topStmts == 0 and not isImportSystemStmt(c.graph, n):
    if sfSystemModule notin c.module.flags and not isEmptyTree(n):
      assert c.graph.systemModule != nil
      c.moduleScope.addSym c.graph.systemModule # import the "System" identifier
      importAllSymbols(c, c.graph.systemModule)
      inc c.topStmts
  else:
    inc c.topStmts

proc semStmtAndGenerateGenerics(c: PContext, n: PNode): PNode =
  importSystemOnce(c, n)
  if sfNoForward in c.module.flags:
    result = semAllTypeSections(c, n)
  else:
    result = n
  result = semStmt(c, result, {})
  # The body pass (doc/parallel_compiler.md §2.1, stage 1): the module's header
  # is complete, so every unit's declare-before-use view is now the whole
  # top-level scope. It runs BEFORE `hloStmt`/`trackStmt` so the module's own
  # top-level statements still see their callees' inferred effects — deferring
  # past that point would make every top-level call pessimistic, which is a
  # bigger change than this stage is trying to make.
  if c.bodyTasks.len > 0:
    drainBodyTasks(c)
  when false:
    # Code generators are lazy now and can deal with undeclared procs, so these
    # steps are not required anymore and actually harmful for the upcoming
    # destructor support.
    # BUGFIX: process newly generated generics here, not at the end!
    if c.lastGenericIdx < c.generics.len:
      var a = newNodeI(nkStmtList, n.info)
      addCodeForGenerics(c, a)
      if a.len > 0:
        # a generic has been added to `a`:
        if result.kind != nkEmpty: a.add result
        result = a
  result = hloStmt(c, result)
  if c.config.cmd == cmdInteractive and not isEmptyType(result.typ):
    result = buildEchoStmt(c, result)
  if c.config.ideActive:
    appendToModule(c.module, result)
  trackStmt(c, c.module, result, isTopLevel = true)
  if optMultiMethods notin c.config.globalOptions and
      c.config.selectedGC in {gcArc, gcOrc, gcAtomicArc, gcYrc} and
      Feature.vtables in c.config.features:
    sortVTableDispatchers(c.graph)

    if sfMainModule in c.module.flags:
      collectVTableDispatchers(c.graph)

proc recoverContext(c: PContext) =
  # clean up in case of a semantic error: We clean up the stacks, etc. This is
  # faster than wrapping every stack operation in a 'try finally' block and
  # requires far less code.
  c.currentScope = c.topLevelScope
  while getCurrOwner(c).kind != skModule: popOwner(c)
  while c.p != nil and c.p.owner.kind != skModule: c.p = c.p.next

proc semWithPContext*(c: PContext, n: PNode): PNode =
  # no need for an expensive 'try' if we stop after the first error anyway:
  if c.config.errorMax <= 1:
    result = semStmtAndGenerateGenerics(c, n)
  else:
    let oldContextLen = msgs.getInfoContextLen(c.config)
    let oldInGenericInst = c.inGenericInst
    try:
      result = semStmtAndGenerateGenerics(c, n)
    except ERecoverableError, ESuggestDone:
      recoverContext(c)
      c.inGenericInst = oldInGenericInst
      msgs.setInfoContextLen(c.config, oldContextLen)
      if getCurrentException() of ESuggestDone:
        c.suggestionsMade = true
        result = nil
      else:
        result = newNodeI(nkEmpty, n.info)
      #if c.config.ideActive: findSuggest(c, n)

type
  CyclePhase* = enum
    ## The phases a module of an `import m {.cyclic.}` group runs through
    ## before its remaining statements are checked by `semWithPContext`.
    ## Every phase runs for all modules of the group before the next phase
    ## starts, so the modules see each other's declarations regardless of
    ## their order.
    cpImports      ## the module's top-level imports
    cpTypesLeft    ## registers the names of all top-level types
    cpTypesRight   ## the type definitions themselves
    cpTypesFinal   ## resolves the remaining forward type references
    cpUnnamedImports ## converters, term rewriting patterns and pure enums of
                     ## the other modules: they were imported before they
                     ## were declared
    cpDecls        ## the leading declarations of the module; their routine
                   ## bodies are deferred

proc demandCycleBody*(group: seq[PContext]; prc: PSym) =
  ## Runs the deferred body of `prc` if it belongs to a module of the group.
  ## A body that is already running is left alone: that is a recursion via the
  ## modules of the group, which effect tracking treats pessimistically.
  for c in group:
    let idx = c.bodyTaskIndex.getOrDefault(prc.itemId, -1)
    if idx >= 0:
      runBodyTask(c, idx)
      break

proc hasPendingBodies(c: PContext): bool =
  result = false
  for t in c.bodyTasks:
    if t.state == btPending: return true

proc isCycleDecl(c: PContext; n: PNode): bool =
  ## The declaration phase covers the module's leading declarations. It stops
  ## at the first statement that does something else, as that statement could
  ## depend on the order in which the modules of the group are checked.
  case n.kind
  of nkCommentStmt, nkEmpty, nkPragma, nkExportStmt,
     nkProcDef, nkFuncDef, nkMethodDef, nkIteratorDef, nkConverterDef,
     nkTemplateDef, nkMacroDef:
    result = true
  of nkImportStmt, nkImportExceptStmt, nkFromStmt, nkTypeSection:
    result = nfSem in n.flags
  of nkDiscardStmt:
    # a `discard """..."""` comment:
    result = n.len == 0 or n[0].kind in {nkEmpty, nkStrLit..nkTripleStrLit}
  of nkConstSection:
    # a constant can call a routine and the VM needs its body, so it must
    # not see a deferred one:
    result = not hasPendingBodies(c)
    for p in c.cyclePartners:
      if hasPendingBodies(p): result = false
  else:
    result = false

proc neededConsts(n: PNode; roots: IntSet): IntSet =
  ## the indices of the top-level const sections of `n` that the identifiers
  ## `roots` refer to, directly or through other constants
  result = initIntSet()
  var wanted = roots
  var changed = true
  while changed:
    changed = false
    for i in 0..<n.len:
      if n[i].kind == nkConstSection and not result.contains(i):
        var names: seq[PIdent] = @[]
        declaredNames(n[i], names)
        for id in names:
          if wanted.contains(id.id):
            result.incl i
            collectIdents(n[i], wanted)
            changed = true
            break

proc scheduleTypesAndConsts(c: PContext; n: PNode) =
  ## `--experimental:noForwardDecls`: the right sides of the type sections
  ## and the constants they need, in dependency order: a type like
  ## `array[N, int]` needs the constant `N`, which can need the fields of an
  ## enum type. The names of the types themselves are already known
  ## (`typeSectionLeftSidePass`). A constant that needs a routine is left to
  ## `hoistDecls`; what remains is checked in source order.
  var typeIdents = initIntSet()
  for it in n:
    if it.kind == nkTypeSection: collectIdents(it, typeIdents)
  let needed = neededConsts(n, typeIdents)
  var items: seq[int] = @[]
  for i in 0..<n.len:
    if (n[i].kind == nkTypeSection and nfSem in n[i].flags) or
        (n[i].kind == nkConstSection and nfSem notin n[i].flags and needed.contains(i)) or
        (isPragmaTemplate(n[i]) and nfSem notin n[i].flags):
      # (a custom pragma that `noForwardImports` could not declare yet)
      items.add i
  var pending = initCountTable[int]()
  var names = newSeq[seq[PIdent]](items.len)
  var exempt = newSeq[seq[PIdent]](items.len)
  var allTypeNames: seq[PIdent] = @[]
  for k, i in items:
    if n[i].kind == nkTypeSection:
      enumFieldNames(n[i], names[k])
      typeNames(n[i], allTypeNames)
    else:
      declaredNames(n[i], names[k])
    for id in names[k]: pending.inc id.id
  # the routines of the module are not available yet:
  for it in n:
    if it.kind in routineDefs and not isPragmaTemplate(it):
      let id = declName(it[namePos])
      if id != nil: pending.inc id.id
  # a type section waits for the other type sections it mentions, a
  # constant needs the types to be complete:
  var typePending = initCountTable[int]()
  for k, i in items:
    exempt[k] = names[k]
    if n[i].kind == nkTemplateDef:
      # the parameters of a custom pragma only need the names of the types
      exempt[k].add allTypeNames
    elif n[i].kind == nkTypeSection:
      typeNames(n[i], exempt[k])
      var tn: seq[PIdent] = @[]
      typeNames(n[i], tn)
      for id in tn: typePending.inc id.id
  var done = newSeq[bool](items.len)
  proc ready(c: PContext; it: PNode; k: int): bool =
    var p = pending
    for key, v in typePending: p.inc(key, v)
    result = not mentionsPendingRefs(if it.kind == nkTemplateDef: hoistDeps(it) else: it,
                                     p, exempt[k])
  proc check(c: PContext; k: int) =
    let i = items[k]
    if n[i].kind == nkTypeSection:
      inc c.inTypeContext
      typeSectionRightSidePass(c, n[i])
      dec c.inTypeContext
      var tn: seq[PIdent] = @[]
      typeNames(n[i], tn)
      for id in tn: typePending.inc(id.id, -1)
    else:
      n[i] = semStmt(c, n[i], {})
      n[i].flags.incl nfSem
    done[k] = true
    for id in names[k]: pending.inc(id.id, -1)
  while true:
    var progress = true
    while progress:
      progress = false
      for k in 0..<items.len:
        if not done[k] and ready(c, n[items[k]], k):
          check(c, k)
          progress = true
    # a cycle (or a type that needs a routine): the first remaining type
    # section in source order, constants are left to `hoistDecls`
    var next = -1
    for k in 0..<items.len:
      if not done[k] and n[items[k]].kind == nkTypeSection:
        next = k
        break
    if next < 0: break
    check(c, next)

proc isImportOnlyWhen(n: PNode): bool =
  ## `when defined(nimPreviewSlimSystem): import std/syncio`
  result = n.kind == nkWhenStmt
  if result:
    for br in n:
      let body = br[^1]
      let stmts = if body.kind == nkStmtList: body else: newTree(nkStmtList, body)
      for it in stmts:
        case it.kind
        of nkImportStmt, nkImportExceptStmt, nkFromStmt, nkExportStmt,
           nkCommentStmt, nkEmpty: discard
        of nkWhenStmt:
          if not isImportOnlyWhen(it): return false
        else: return false

proc importsOnlyStdlib(c: PContext; n: PNode): bool =
  ## Whether all the modules that the import statement (or import-only
  ## `when`) `n` refers to are part of the standard library, which cannot be
  ## part of an import cycle with the current module.
  case n.kind
  of nkImportStmt, nkImportExceptStmt, nkFromStmt:
    let lib = c.config.libpath.string
    var paths: seq[PNode] = @[]
    if n.kind == nkImportStmt:
      for x in n: paths.add x
    else:
      paths.add n[0]
    result = true
    for x in paths:
      var x = x
      if x.kind == nkInfix and x.len == 3 and x[0].kind == nkIdent and x[0].ident.s == "as":
        x = x[1]
      if x.kind in {nkInfix, nkPrefix} and x[^1].kind == nkBracket:
        # `std/[a, b]`
        let prefix = x.copyTree
        for y in x[^1]:
          prefix[^1] = y
          let f = checkModuleName(c.config, prefix, doLocalError = false)
          if f == InvalidFileIdx or not toFullPath(c.config, f).startsWith(lib):
            return false
      else:
        let f = checkModuleName(c.config, x, doLocalError = false)
        if f == InvalidFileIdx or not toFullPath(c.config, f).startsWith(lib):
          return false
  of nkWhenStmt:
    result = true
    for br in n:
      let body = br[^1]
      let stmts = if body.kind == nkStmtList: body else: newTree(nkStmtList, body)
      for it in stmts:
        if it.kind in {nkImportStmt, nkImportExceptStmt, nkFromStmt, nkWhenStmt} and
            not importsOnlyStdlib(c, it):
          return false
  else:
    result = false

proc noForwardImports(c: PContext; n: PNode) =
  ## `--experimental:noForwardDecls`: the imports of the module, including
  ## the ones guarded by a `when` that only contains imports, in source order.
  ## The constants that such a `when` condition or a user pragma
  ## (`{.pragma: lib, header: dir & "/lib.h".}`) can depend on, and the user
  ## pragmas, are checked first if they do not depend on the module's types or
  ## routines.
  var pending = initCountTable[int]()
  for it in n:
    var names: seq[PIdent] = @[]
    case it.kind
    of nkTypeSection:
      typeNames(it, names)
      enumFieldNames(it, names)
    of nkConstSection: declaredNames(it, names)
    of routineDefs: declaredNames(it, names)
    else: discard
    for id in names: pending.inc id.id
  var conds = initIntSet()
  for it in n:
    if isImportOnlyWhen(it):
      for br in it:
        if br.len > 1: collectIdents(br[0], conds)
    elif isUserPragmaDef(it):
      collectIdents(it, conds)
  let needed = neededConsts(n, conds)
  var preamble = true
  var early = true # no import that stays in place came before
  for i in 0..<n.len:
    let it = n[i]
    if early and it.kind == nkConstSection and needed.contains(i):
      # a constant that a `when` condition or a user pragma needs
      var names: seq[PIdent] = @[]
      declaredNames(it, names)
      if not mentionsPending(it, pending, names):
        n[i] = semStmt(c, it, {})
        n[i].flags.incl nfSem
        for id in names: pending.inc(id.id, -1)
      continue
    if early and (isUserPragmaDef(it) or isPragmaTemplate(it)):
      # the pragmas of the types are applied when their names are declared,
      # before the declarations are hoisted (`typeSectionLeftSidePass`)
      var names: seq[PIdent] = @[]
      declaredNames(it, names)
      if not mentionsPending(hoistDeps(it), pending, names):
        n[i] = semStmt(c, it, {})
        n[i].flags.incl nfSem
      continue
    if not preamble:
      # an import that follows the module's first declarations stays where it
      # is, it can be part of an import cycle that relies on it; unless it
      # only imports modules of the standard library:
      if (it.kind in {nkImportStmt, nkImportExceptStmt, nkFromStmt} or
          isImportOnlyWhen(it)) and importsOnlyStdlib(c, it):
        n[i] = semStmt(c, it, {})
        n[i].flags.incl nfSem
      elif it.kind in {nkImportStmt, nkImportExceptStmt, nkFromStmt, nkIncludeStmt} or
          isImportOnlyWhen(it):
        early = false
      continue
    case it.kind
    of nkTypeSection, nkProcDef, nkFuncDef, nkMethodDef, nkIteratorDef,
       nkConverterDef:
      preamble = false
    of nkImportStmt, nkImportExceptStmt, nkFromStmt, nkExportStmt:
      n[i] = semStmt(c, it, {})
      n[i].flags.incl nfSem
    of nkWhenStmt:
      if isImportOnlyWhen(it):
        n[i] = semStmt(c, it, {})
        n[i].flags.incl nfSem
    else: discard

proc topLevelNames(n: PNode): IntSet =
  ## everything that the top-level statements of `n` declare by themselves
  result = initIntSet()
  for it in n:
    var names: seq[PIdent] = @[]
    case it.kind
    of nkTypeSection:
      typeNames(it, names)
      enumFieldNames(it, names)
    of nkConstSection, routineDefs: declaredNames(it, names)
    of nkVarSection, nkLetSection:
      for def in it:
        if def.kind in {nkIdentDefs, nkVarTuple}:
          for j in 0..<def.len-2:
            let id = declName(def[j])
            if id != nil: names.add id
    else: discard
    for id in names: result.incl id.id

proc binderNames(n: PNode; result: var IntSet) =
  ## the generic parameters and concept parameters of the type section `n`
  case n.kind
  of nkGenericParams:
    for it in n:
      if it.kind == nkIdentDefs:
        for j in 0..<it.len-2:
          let id = declName(it[j])
          if id != nil: result.incl id.id
  of nkTypeClassTy:
    if n.len > 0:
      for it in n[0]:
        let id = declName(it)
        if id != nil: result.incl id.id
    for i in 1..<n.len: binderNames(n[i], result)
  of nkIdent, nkSym, nkCharLit..nkTripleStrLit, nkNilLit, nkEmpty, nkCommentStmt:
    discard
  else:
    for it in n: binderNames(it, result)

proc mentionsUnknown(c: PContext; n: PNode; known: IntSet): bool =
  ## Whether the type section `n` mentions a name that is neither in scope nor
  ## declared by the module's top-level statements (`known`): it is produced
  ## by a macro or template of the module.
  case n.kind
  of nkIdent:
    var amb = false
    result = not known.contains(n.ident.id) and searchInScopes(c, n.ident, amb) == nil
  of nkAccQuoted:
    result = n.len == 1 and mentionsUnknown(c, n[0], known)
  of nkSym, nkCharLit..nkTripleStrLit, nkNilLit, nkEmpty, nkCommentStmt:
    result = false
  of nkIdentDefs:
    # the names of fields and parameters are not lookups:
    result = mentionsUnknown(c, n[^2], known) or mentionsUnknown(c, n[^1], known)
  of nkEnumTy:
    result = false
    for f in n:
      if f.kind == nkEnumFieldDef and mentionsUnknown(c, f[1], known): return true
  of nkDotExpr:
    result = mentionsUnknown(c, n[0], known)
  of nkPragma:
    # pragma names are not looked up like other names, their values are:
    result = false
    for it in n:
      if it.kind in nkPragmaCallKinds:
        for j in 1..<it.len:
          if mentionsUnknown(c, it[j], known): return true
  of nkTypeDef:
    result = (n[0].kind == nkPragmaExpr and mentionsUnknown(c, n[0][1], known)) or
      mentionsUnknown(c, n[1], known) or mentionsUnknown(c, n[2], known)
  else:
    result = false
    for it in n:
      if mentionsUnknown(c, it, known): return true

proc macroTypeSections(c: PContext; n: PNode): IntSet =
  ## `--experimental:noForwardDecls`: the type sections that need what a
  ## macro or template of the module produces, directly or through another
  ## such type section. They are checked in order, like without
  ## noForwardDecls.
  result = initIntSet()
  var known = topLevelNames(n)
  # the modules of an import cycle see each other's declarations:
  for p in c.cyclePartners:
    if p.noForwardList != nil:
      for id in topLevelNames(p.noForwardList): known.incl id
  var changed = true
  var deferredTypes = initIntSet()
  while changed:
    changed = false
    for i in 0..<n.len:
      if n[i].kind != nkTypeSection or nfSem in n[i].flags or result.contains(i):
        continue
      var k = known
      binderNames(n[i], k)
      var mentioned = initIntSet()
      collectIdents(n[i], mentioned)
      if mentionsUnknown(c, n[i], k) or not disjoint(mentioned, deferredTypes):
        result.incl i
        var names: seq[PIdent] = @[]
        typeNames(n[i], names)
        enumFieldNames(n[i], names)
        for id in names: deferredTypes.incl id.id
        changed = true

proc semCyclePhaseImpl(c: PContext; n: PNode; phase: CyclePhase) =
  if phase == cpImports and c.noForward:
    importSystemOnce(c, n)
    noForwardImports(c, n)
    return
  if phase == cpTypesRight and c.noForward:
    scheduleTypesAndConsts(c, n)
  case phase
  of cpImports:
    importSystemOnce(c, n)
    for i in 0..<n.len:
      if n[i].kind in {nkImportStmt, nkImportExceptStmt, nkFromStmt}:
        # the result is flagged with `nfSem`, so the final pass skips it:
        n[i] = semStmt(c, n[i], {})
        n[i].flags.incl nfSem
  of cpTypesLeft, cpTypesRight, cpTypesFinal:
    let later = if phase == cpTypesLeft and c.noForward: macroTypeSections(c, n)
                else: initIntSet()
    for i in 0..<n.len:
      if n[i].kind == nkTypeSection:
        if phase == cpTypesLeft and later.contains(i): continue
        if phase != cpTypesLeft and nfSem notin n[i].flags:
          continue # a type section of `macroTypeSections`
        inc c.inTypeContext
        case phase
        of cpTypesLeft:
          n[i].flags.incl nfSem
          typeSectionLeftSidePass(c, n[i])
        of cpTypesRight:
          if c.noForward: continue # see `scheduleTypesAndConsts`
          typeSectionRightSidePass(c, n[i])
        else: typeSectionFinalPass(c, n[i])
        dec c.inTypeContext
  of cpUnnamedImports:
    var partners: seq[PSym] = @[]
    for p in c.cyclePartners: partners.add p.module
    reimportUnnamed(c, partners)
  of cpDecls:
    if c.noForward:
      hoistDecls(c, n, 0)
      return
    c.deferAllBodies = true
    for i in 0..<n.len:
      if not isCycleDecl(c, n[i]): break
      if nfSem notin n[i].flags:
        n[i] = semStmt(c, n[i], {})
        n[i].flags.incl nfSem
    c.deferAllBodies = false

proc semCyclePhase*(c: PContext; n: PNode; phase: CyclePhase) =
  if c.config.errorMax <= 1:
    semCyclePhaseImpl(c, n, phase)
  else:
    let oldContextLen = msgs.getInfoContextLen(c.config)
    let oldInGenericInst = c.inGenericInst
    try:
      semCyclePhaseImpl(c, n, phase)
    except ERecoverableError:
      recoverContext(c)
      c.inGenericInst = oldInGenericInst
      msgs.setInfoContextLen(c.config, oldContextLen)

proc reportUnusedModules(c: PContext) =
  if c.config.cmd == cmdM: return
  for (s, info) in c.unusedImports:
    if sfUsed notin s.flags:
      message(c.config, info, warnUnusedImportX, s.name.s)

proc closePContext*(graph: ModuleGraph; c: PContext, n: PNode): PNode =
  # Belt and braces: `semStmtAndGenerateGenerics` has already drained, but a
  # module whose sem was cut short (an error, `ESuggestDone`) can still hold
  # units, and their scopes are detached from `PContext` — nothing else would
  # ever close them.
  if c.bodyTasks.len > 0:
    drainBodyTasks(c)
  if optDeferBodies in c.config.globalOptions:
    graph.demandRoutineBody = c.prevDemandRoutineBody
  if c.config.ideActive and not c.suggestionsMade:
    suggestSentinel(c)
  closeScope(c)         # close module's scope
  rawCloseScope(c)      # imported symbols; don't check for unused ones!
  reportUnusedModules(c)
  result = newNode(nkStmtList)
  if n != nil:
    internalError(c.config, n.info, "n is not nil") #result := n;
  addCodeForGenerics(c, result)
  if c.module.ast != nil:
    result.add(c.module.ast)
  popOwner(c)
  popProcCon(c)
  sealRodFile(c)
