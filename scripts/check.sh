#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build InfiniteZero.Verification
python3 scripts/update_status.py
python3 scripts/blueprint_index.py
