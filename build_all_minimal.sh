#!/bin/sh
# minimal version of build_all.sh: only builds bin/nim and bin/nimble.
# no LTO, no integrity check (2 compiler builds instead of 3), no `koch tools`.
# arguments can be passed, e.g.:
# CC=gcc ucpu=amd64 uos=darwin

set -u # error on undefined variables
set -e # exit on first error

. ci/funs.sh
nimBuildCsourcesIfNeeded "$@"

echo_run bin/nim c --noNimblePath --skipUserCfg --skipParentCfg --hints:off koch
echo_run ./koch --skipIntegrityCheck boot -d:danger --skipUserCfg --skipParentCfg --hints:off
echo_run ./koch nimble --skipUserCfg --skipParentCfg --hints:off
