#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -lt 1 ]; then
  echo "usage: $0 FILE.i [sparrow args...]" >&2
  exit 2
fi

input="$1"
shift

if [ ! -f "$input" ]; then
  echo "error: input file not found: $input" >&2
  exit 2
fi

input_dir="$(cd "$(dirname "$input")" && pwd)"
input_base="$(basename "$input")"

docker run --rm \
  -v "$input_dir:/work:ro" \
  attack-sparrow \
  "$@" "/work/$input_base"
