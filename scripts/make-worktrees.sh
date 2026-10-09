#!/usr/bin/env bash
# Desk only. Cut one worktree per lane under C:/GitHub_Files/Claude-Repos/wt/hk-<lane> on branch
# desk/<lane>, junction the Mathlib cache and copy the built skeleton so a lane's first build replays.
set -u
ROOT=/c/GitHub_Files/Claude-Repos/hk-heterogeneous-lean
WT=/c/GitHub_Files/Claude-Repos/wt
mkdir -p "$WT"
for lane in "$@"; do
  dir="$WT/hk-$lane"
  if [ -d "$dir" ]; then echo "exists: $dir"; continue; fi
  (cd "$ROOT" && git worktree add -q -b "desk/$lane" "$dir" main) || { echo "worktree failed: $lane"; continue; }
  mkdir -p "$dir/.lake" "$dir/.scratch"
  powershell.exe -NoProfile -Command "New-Item -ItemType Junction -Path '$(cygpath -w "$dir/.lake/packages")' -Target 'C:\GitHub_Files\Claude-Repos\l2-lean\.lake\packages' | Out-Null"
  cp -r "$ROOT/.lake/build" "$dir/.lake/build"
  cp "$ROOT/.lake/config"* "$dir/.lake/" 2>/dev/null
  echo "ready: $dir (desk/$lane)"
done
