#!/usr/bin/env bash
# lean-temper's commit-boundary gate (.exophial/config.yaml gate.command). exophial runs it
# inside the image of .exophial/gate/Dockerfile. Each step either passes or ends the gate
# with exit 1. It lives under .exophial/gate/ because exophial counts that directory as
# the judging environment (exophial completion.py, _classify_commit).
#
# Scope: the gate builds the tool and its tests executable. It does not run the tests,
# because the tests need an armada-lean checkout and a built Lean REPL, and the gate image
# has neither. A test run outside the gate is still required for each change (see README).
set -euo pipefail
cd "$(dirname "$0")/../.."
export PATH="$HOME/.elan/bin:$PATH"

# `lake build` builds the package's default target (the tool's executable). The gate
# does not name it: on its first run exophial grades the tree before this environment
# existed, whose executable had another name.
echo "== lake build"
lake build
echo "== lake build tests"
lake build tests
echo "== gate passed"
