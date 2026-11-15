#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"

# The audit reads compiled environments, so refresh them before loading modules.
lake build --iofail

audit_workdir="$(mktemp -d)"
trap 'rm -rf -- "$audit_workdir"' EXIT
audit_revision=46024e005996495c65ef609368e11ab39c4222e3
git -c advice.detachedHead=false clone --quiet --depth 1 --branch v0.1.2 \
  https://github.com/leanprover-community/axiom-audit.git "$audit_workdir/tool"
if [[ "$(git -C "$audit_workdir/tool" rev-parse HEAD)" != "$audit_revision" ]]; then
  echo 'axiom-audit tag does not match the pinned revision' >&2
  exit 1
fi
cp lean-toolchain "$audit_workdir/tool/lean-toolchain"
(
  cd "$audit_workdir/tool"
  lake build --quiet
)

# The root module contains the algebraic core, while hand-level proofs import it.
# Import every library module explicitly so those later proofs are audited too.
lake env "$audit_workdir/tool/.lake/build/bin/axiom-audit" \
  --root MeldSizeObstruction \
  --modules-from MeldSizeObstruction \
  --allow propext,Classical.choice,Quot.sound \
  --json
