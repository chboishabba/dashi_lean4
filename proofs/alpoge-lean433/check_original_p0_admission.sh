#!/usr/bin/env bash
# One local admission runner for the original author fork and the licensed
# compact/readable rewritings. No CI and no cross-version OLean reuse.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SIDECAR="$ROOT/proofs/alpoge-lean433"
SOURCE="${GRH_P0_SOURCE:-original}"
case "$SOURCE" in
  original) DEFAULT="$ROOT/.local/alpoge-rh-v4331"; PROJECT=""; VERSION=4.33.1; REPLAY=0; CACHE=0 ;;
  compact) DEFAULT="$ROOT/.local/alpoge-grh-v4350"; PROJECT=grh-compact; VERSION=4.35.0; REPLAY=1; CACHE=1 ;;
  readable) DEFAULT="$ROOT/.local/alpoge-grh-v4350"; PROJECT=grh; VERSION=4.35.0; REPLAY=1; CACHE=1 ;;
  *) echo "Unknown GRH_P0_SOURCE: $SOURCE" >&2; exit 2 ;;
esac
if [[ "$SOURCE" != original && "${GRH_P0_CHECK_DIRECTIONAL:-0}" == 1 ]]; then
  echo 'BLOCKED: original RowSrc donor imports exist only in the original author layout.' >&2
  exit 15
fi
if ! command -v lake >/dev/null 2>&1; then
  echo 'BLOCKED: local pinned Lean/lake toolchain unavailable; no kernel receipt.' >&2
  exit 12
fi
if ! command -v python3 >/dev/null 2>&1; then
  echo 'BLOCKED: Python 3 needed for pin and axiom audits.' >&2
  exit 13
fi
CHECKOUT="$(python3 -c 'import pathlib,sys; print(pathlib.Path(sys.argv[1]).resolve())' "${1:-$DEFAULT}")"
REPORT_BASE="${GRH_P0_REPORT_DIR:-$ROOT/.local/grh-p0-admission/$SOURCE}"
if [[ "$REPORT_BASE" != /* ]]; then REPORT_BASE="$ROOT/$REPORT_BASE"; fi
mkdir -p "$REPORT_BASE"
REPORT_DIR="$(mktemp -d "$REPORT_BASE/run.XXXXXXXX")"
REPORT_DIR="$(cd "$REPORT_DIR" && pwd)"
echo "Run logs: $REPORT_DIR"
export GRH_P0_SOURCE="$SOURCE"
unset ELAN_TOOLCHAIN LEAN_PATH LEAN_SRC_PATH
bash "$SIDECAR/checkout_fork_source.sh" "$CHECKOUT" | tee "$REPORT_DIR/source-pin.log"
(
  cd "$CHECKOUT/$PROJECT"
  lake env lean --version 2>&1 | tee "$REPORT_DIR/lean-version.log"
  grep -Fq "version $VERSION," "$REPORT_DIR/lean-version.log" || {
    echo 'BLOCKED: actual Lean version mismatch' >&2; exit 4;
  }
  if [[ "${GRH_P0_CACHE_GET:-$CACHE}" == 1 ]]; then
    lake exe cache get 2>&1 | tee "$REPORT_DIR/cache.log"
  fi
  lake build Main 2>&1 | tee "$REPORT_DIR/main-build.log"

  # Check actual package commits, not only the declared manifest.
  python3 - <<'PY' | tee "$REPORT_DIR/dependency-pins.log"
import json, pathlib, subprocess
manifest = json.loads(pathlib.Path("lake-manifest.json").read_text())
base = pathlib.Path(manifest.get("packagesDir", ".lake/packages"))
for p in manifest["packages"]:
    if p["type"] != "git":
        raise SystemExit("BLOCKED: unexpected non-Git package: " + p["name"])
    path = base / p["name"]
    def git(*args):
        return subprocess.check_output(["git", "-C", str(path), *args], text=True).strip()
    if git("rev-parse", "HEAD") != p["rev"] or git("status", "--porcelain", "--untracked-files=all"):
        raise SystemExit("BLOCKED: package revision/working-tree mismatch: " + p["name"])
    if any(s[:1] == "S" or s[:1].islower() for s in git("ls-files", "-v").splitlines()):
        raise SystemExit("BLOCKED: hidden package source paths: " + p["name"])
    print(p["name"], p["rev"])
PY

  if [[ "$SOURCE" != original ]]; then
    lake env lean scripts/PrintAxioms.lean 2>&1 | tee "$REPORT_DIR/upstream-axioms.log"
    python3 "$SIDECAR/audit_p0_axioms.py" upstream "$REPORT_DIR/upstream-axioms.log" |
      tee "$REPORT_DIR/upstream-axiom-audit.log"
  fi
  lake env lean "$SIDECAR/RHAdmission.lean" 2>&1 | tee "$REPORT_DIR/adapter-lean.log"
  python3 "$SIDECAR/audit_p0_axioms.py" adapter "$REPORT_DIR/adapter-lean.log" |
    tee "$REPORT_DIR/adapter-axiom-audit.log"

  if [[ "${GRH_P0_FRESH_REPLAY:-$REPLAY}" == 1 ]]; then
    # v4.35.0 LeanChecker.lean: --fresh Main replays all imported and
    # defined constants into a fresh kernel environment, not just Main.
    lake env leanchecker --fresh --verbose Main 2>&1 | tee "$REPORT_DIR/fresh-kernel.log"
  fi
  if [[ "${GRH_P0_CLAY:-$REPLAY}" == 1 ]]; then
    # Consume the existing exact target vendor, not a restatement of RH.
    VENDOR="$(python3 -c 'import pathlib,sys; print(pathlib.Path(sys.argv[1]).resolve())' "${GRH_P0_CLAY_VENDOR:-$ROOT/vendor/LeanMillenniumPrizeProblems}")"
    if [[ ! -e "$VENDOR" ]]; then
      bash "$ROOT/scripts/vendor_millennium_targets.sh" "$VENDOR"
    fi
    CLAY_PIN=603053dc267cf3efe422f438eb78098c0ececd6f
    CLAY_TREE=b7c2004c0e8cb192d3dc7d740551a2de04068b61
    CLAY_BLOB=26356e8fecc91562eb2af2564e852e1b33c63005
    TARGET=Problems/RiemannHypothesis/Millennium.lean
    [[ "$(git -C "$VENDOR" rev-parse HEAD)" == "$CLAY_PIN" ]]
    [[ "$(git -C "$VENDOR" rev-parse 'HEAD^{tree}')" == "$CLAY_TREE" ]]
    [[ "$(git -C "$VENDOR" rev-parse "HEAD:$TARGET")" == "$CLAY_BLOB" ]]
    [[ "$(git hash-object --no-filters "$VENDOR/$TARGET")" == "$CLAY_BLOB" ]]
    [[ -z "$(git -C "$VENDOR" status --porcelain --untracked-files=all)" ]]
    BUILD="$REPORT_DIR/clay-olean"
    mkdir -p "$BUILD/Problems/RiemannHypothesis"
    # Compile the unmodified upstream target in THIS Mathlib environment.
    # It has a final unused challenge sorry; the actual exported proof
    # below must not depend on sorryAx or any nonstandard axiom.
    lake env lean --root="$VENDOR" -o "$BUILD/Problems/RiemannHypothesis/Millennium.olean" "$VENDOR/$TARGET" 2>&1 |
      tee "$REPORT_DIR/clay-target-build.log"
    lake env bash -c 'export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"; exec lean --root="$3" -o "$1/RHClayAdmission.olean" "$2"' \
      _ "$BUILD" "$SIDECAR/RHClayAdmission.lean" "$SIDECAR" 2>&1 |
      tee "$REPORT_DIR/clay-admission.log"
    python3 "$SIDECAR/audit_p0_axioms.py" clay "$REPORT_DIR/clay-admission.log" |
      tee "$REPORT_DIR/clay-axiom-audit.log"
  fi

  if [[ "${GRH_P0_CHECK_DIRECTIONAL:-0}" == 1 ]]; then
    lake env lean "$SIDECAR/RHGRHP0DirectionalSourceCut.lean" 2>&1 |
      tee "$REPORT_DIR/directional-donor-lean.log"
  fi
)
# Detect modifications made during the build. This is still a local trusted
# toolchain receipt, not independent checker or Agda/cross-version admission.
GRH_P0_VERIFY_ONLY=1 bash "$SIDECAR/checkout_fork_source.sh" "$CHECKOUT" | tee "$REPORT_DIR/source-pin-after.log"
if [[ "${GRH_P0_FRESH_REPLAY:-$REPLAY}" == 1 ]]; then
  printf 'LOCAL SOURCE ADMISSION + FRESH KERNEL REPLAY: %s Lean %s\n' "$SOURCE" "$VERSION"
else
  printf 'LOCAL SOURCE BUILD + ADAPTER AXIOM AUDIT ONLY (fresh replay not requested): %s Lean %s\n' "$SOURCE" "$VERSION"
fi
printf 'Receipts: %s\n' "$REPORT_DIR"
if [[ "${GRH_P0_CLAY:-$REPLAY}" == 1 ]]; then
  printf 'SAME-KERNEL PINNED CLAY RH AND XI ADAPTER CHECKED (isolated %s).\n' "$VERSION"
fi
printf 'Still separate: root-package proof import, Agda same-object transport, independent external checker acceptance.\n'
