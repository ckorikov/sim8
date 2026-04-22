#!/usr/bin/env bash
# Auto-format file after Edit/Write tool use.
# Reads Claude Code PostToolUse JSON from stdin.

set -euo pipefail

FILE=$(python3 -c "import sys,json; d=json.load(sys.stdin); print(d.get('tool_input',{}).get('file_path',''))")

[ -z "$FILE" ] && exit 0
[ -f "$FILE" ] || exit 0

case "$FILE" in
  *.py)
    cd /Users/ck/dev/sim8/pysim8
    uv run ruff format --quiet "$FILE" 2>/dev/null || true
    ;;
  *.js|*.css|*.html)
    cd /Users/ck/dev/sim8/web
    npx prettier --write --log-level silent "$FILE" 2>/dev/null || true
    ;;
esac
