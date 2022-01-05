#!/usr/bin/env bash
set -e

MODEL="$1"

TMPDIR="$(mktemp -d -p /tmp)"

echo $TMPDIR
echo -e "\e[1m⚙ Compiling . . .\e[0m"
make
make coq
make -s "$MODEL" > "$TMPDIR/z3"


echo
echo -e "\e[1m💻 Running z3 . . .\e[0m"
time \
    z3 'fp.engine=bmc' 'fp.print-answer=true'  "$TMPDIR/z3" -v:1 \
    1> "$TMPDIR/stdout" 2> "$TMPDIR/stderr" \
   & tail -f "$TMPDIR/stderr" --pid "$!" \
      | sed 's/\(.*level.*\)/\x1b[7;35;1m\1\x1b[0m/'

echo -e "\e[1m🆗 Output:\e[0m $TMPDIR/stdout"

echo -e "\e[1m🔎 Trace:\e[0m ↳"
sed -i 's/sat//' "$TMPDIR/stdout"

{ utop scripts/display_trace.ml "$TMPDIR/stdout" 2>&3 \
      | sed 's/\([0-9]\+\)/\x1b[32;1m\1\x1b[0m/g' \
      | sed 's/Build_\([^ ]*\)/\x1b[2mBuild_\x1b[1m\1\x1b[0m/g' \
      | sed 's/\(None[^ ]*\|Some[^ ]*\)/\x1b[2m\1\x1b[0m/g' \
      | sed 's/\(Ev[^ ]*\)/\x1b[35;1m\1\x1b[0m/g' \
      | sed 's/\(Emitter[^ ]*\)/\x1b[36;1m\1\x1b[0m/g'
} 3>&1 1>&2 | plantuml -pipe -tutxt


