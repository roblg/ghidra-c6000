#!/usr/bin/env bash
#
# Run the execute-packet / delay-slot emulator test in both endian modes
# against an installed build of this extension.
#
# Usage: tools/test_packet_semantics.sh
# Environment: GHIDRA_INSTALL_DIR, JAVA_HOME (as for tools/build.sh);
#              DEBUG=1 keeps the headless logs on success.
#
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
GHIDRA="${GHIDRA_INSTALL_DIR:?set GHIDRA_INSTALL_DIR}"
# Ghidra rejects project paths with dot-prefixed elements, so work in a
# temporary directory rather than under the checkout.
WORK="${PACKET_TEST_WORK:-$(mktemp -d)}"
mkdir -p "$WORK"

status=0
for endian in le be; do
  lang="C6000:LE:32:default"
  [ "$endian" = be ] && lang="C6000:BE:32:default"
  python3 "$ROOT/tests/fixtures/packet-semantics.py" "$WORK/image_$endian.bin" "$endian"
  log="$WORK/$endian.log"
  "$GHIDRA/support/analyzeHeadless" "$WORK" "ps_$endian" \
    -import "$WORK/image_$endian.bin" -overwrite -deleteProject \
    -loader BinaryLoader -loader-baseAddr 0x1000 -processor "$lang" \
    -scriptPath "$ROOT/ghidra_scripts" \
    -preScript C6000SetEntry.java 1000 \
    -postScript C6000PacketSemanticsTest.java >"$log" 2>&1 || true
  if grep -q C6000_PACKET_SEMANTICS_OK "$log"; then
    echo "$endian: ok"
    [ -n "${DEBUG:-}" ] || rm -f "$log"
  else
    echo "$endian: FAILED (see $log)"
    grep -hE 'AssertionError|ERROR' "$log" | head -5 || true
    status=1
  fi
done
exit $status
