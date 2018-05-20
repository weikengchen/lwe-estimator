#!/usr/bin/env bash
###############################################################################
#                         Build Sphinx Documentation
###############################################################################
SAGE_ROOT=$(sage -c "import os; print os.environ['SAGE_ROOT']")
export SAGE_ROOT="$SAGE_ROOT"

# shellcheck source=/dev/null
source "$SAGE_ROOT/local/bin/sage-env"
PYTHONIOENCODING=UTF-8 PYTHONPATH=$(pwd) make html
