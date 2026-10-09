#!/usr/bin/env bash
# Desk only: Palomar's core-notation audit of the Challenge, run inside one of the two lane build slots
# (it needs ~4 GB). Usage: bash scripts/audit-slot.sh > .scratch/audit.json
LOCKDIR=/c/GitHub_Files/Claude-Repos/hk-heterogeneous-lean/.lanes-lock
mkdir -p "$LOCKDIR"
slot=""
for _ in $(seq 1 720); do
  for s in slot1 slot2; do
    if mkdir "$LOCKDIR/$s" 2>/dev/null; then slot="$s"; break; fi
  done
  [ -n "$slot" ] && break
  sleep 5
done
[ -z "$slot" ] && { echo "no slot" >&2; exit 2; }
trap 'rmdir "$LOCKDIR/$slot" 2>/dev/null; rm -f /c/GitHub_Files/Claude-Repos/BOX-LOCK' EXIT
echo "audit: $(date) in $slot" > /c/GitHub_Files/Claude-Repos/BOX-LOCK
args=(Challenge)
for t in $(awk '/^theorem /{print $2}' Challenge.lean); do args+=(theorem "HK.$t"); done
for d in $(awk '/^def /{print $2} /^noncomputable def /{print $3}' Challenge.lean); do args+=(def "HK.$d"); done
echo "audit: ${#args[@]} args" >&2
lake env lean --run scripts/core_notation_audit.lean "${args[@]}"
