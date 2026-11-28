#!/usr/bin/env bash
# One local admission runner for the original author fork and the licensed
# compact/readable rewritings. No CI and no cross-version OLean reuse.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SIDECAR="$ROOT/proofs/alpoge-lean433"
SOURCE="${GRH_P0_SOURCE:-compact}"
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
# Bind the local semantic source to the actual Git revision. A dirty
# unrelated file is harmless; an altered theorem or audit input is not.
DASHI_HEAD="$(git -C "$ROOT" rev-parse HEAD)"
verify_local_source() {
  [[ "$(git -C "$ROOT" rev-parse HEAD)" == "$DASHI_HEAD" ]] || {
    echo 'BLOCKED: DASHI HEAD changed during admission' >&2; return 1;
  }
  local path want got
  for path in proofs/alpoge-lean433/check_original_p0_admission.sh \
      proofs/alpoge-lean433/checkout_fork_source.sh \
      proofs/alpoge-lean433/fork_pin.json \
      proofs/alpoge-lean433/licensed_rewrite_pin.json \
      proofs/alpoge-lean433/audit_p0_axioms.py \
      proofs/alpoge-lean433/RHAdmission.lean \
      proofs/alpoge-lean433/RHClayAdmission.lean \
      MillenniumExternal/AlpogeRHBoundaryExact.lean \
      MillenniumExternal/AlpogeRHUniversalXiZetaBidiExact.lean; do
    want="$(git -C "$ROOT" rev-parse "$DASHI_HEAD:$path")"
    got="$(git hash-object --no-filters "$ROOT/$path")"
    [[ "$want" == "$got" ]] || {
      echo "BLOCKED: modified local admission input: $path" >&2; return 1;
    }
    printf '%s %s\n' "$got" "$path"
  done
  printf 'DASHI source revision: %s\n' "$DASHI_HEAD"
}
verify_local_source | tee "$REPORT_DIR/dashi-source-before.log"
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
  verify_dependency_pins() {
  python3 - <<'PY'
import json, pathlib, subprocess
import hashlib
manifest_bytes=pathlib.Path("lake-manifest.json").read_bytes()
print("manifest sha256",hashlib.sha256(manifest_bytes).hexdigest())
manifest = json.loads(manifest_bytes)
base = pathlib.Path(manifest.get("packagesDir", ".lake/packages"))
for p in sorted(manifest["packages"],key=lambda p:p["name"]):
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
  }
  verify_dependency_pins | tee "$REPORT_DIR/dependency-pins.log"

  if [[ "$SOURCE" != original ]]; then
    lake env lean scripts/PrintAxioms.lean 2>&1 | tee "$REPORT_DIR/upstream-axioms.log"
    python3 "$SIDECAR/audit_p0_axioms.py" upstream "$REPORT_DIR/upstream-axioms.log" |
      tee "$REPORT_DIR/upstream-axiom-audit.log"
  fi
  # Persist the exact checked adapter in a unique per-run module directory.
  BUILD="$REPORT_DIR/admission-olean"
  mkdir -p "$BUILD"
  lake env lean --root="$SIDECAR" -o "$BUILD/RHAdmission.olean" "$SIDECAR/RHAdmission.lean" 2>&1 |
    tee "$REPORT_DIR/adapter-lean.log"
  REPLAY_TARGET=RHAdmission
  python3 "$SIDECAR/audit_p0_axioms.py" adapter "$REPORT_DIR/adapter-lean.log" |
    tee "$REPORT_DIR/adapter-axiom-audit.log"

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
    mkdir -p "$BUILD/Problems/RiemannHypothesis"
    # Compile the unmodified upstream target in THIS Mathlib environment.
    # It has a final unused challenge sorry; the actual exported proof
    # below must not depend on sorryAx or any nonstandard axiom.
    lake env lean --root="$VENDOR" -o "$BUILD/Problems/RiemannHypothesis/Millennium.olean" "$VENDOR/$TARGET" 2>&1 |
      tee "$REPORT_DIR/clay-target-build.log"
    # Compile the actual root adapter from this checkout, not a duplicate
    # cross-version theorem or a supplied root .olean.
    ROOT_ADAPTER="$ROOT/MillenniumExternal/AlpogeRHBoundaryExact.lean"
    ROOT_ADAPTER_BLOB="$(git -C "$ROOT" rev-parse HEAD:MillenniumExternal/AlpogeRHBoundaryExact.lean)"
    [[ "$(git hash-object --no-filters "$ROOT_ADAPTER")" == "$ROOT_ADAPTER_BLOB" ]]
    mkdir -p "$BUILD/MillenniumExternal"
    lake env bash -c 'export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"; exec lean --root="$3" -o "$1/MillenniumExternal/AlpogeRHBoundaryExact.olean" "$2"' \
      _ "$BUILD" "$ROOT_ADAPTER" "$ROOT" 2>&1 | tee "$REPORT_DIR/root-boundary.log"
    python3 "$SIDECAR/audit_p0_axioms.py" root "$REPORT_DIR/root-boundary.log" |
      tee "$REPORT_DIR/root-boundary-axioms.log"
    XI_ADAPTER="$ROOT/MillenniumExternal/AlpogeRHUniversalXiZetaBidiExact.lean"
    XI_BLOB="$(git -C "$ROOT" rev-parse HEAD:MillenniumExternal/AlpogeRHUniversalXiZetaBidiExact.lean)"
    [[ "$(git hash-object --no-filters "$XI_ADAPTER")" == "$XI_BLOB" ]]
    lake env bash -c 'export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"; exec lean --root="$3" -o "$1/MillenniumExternal/AlpogeRHUniversalXiZetaBidiExact.olean" "$2"' \
      _ "$BUILD" "$XI_ADAPTER" "$ROOT" 2>&1 | tee "$REPORT_DIR/xi-bidi.log"
    python3 "$SIDECAR/audit_p0_axioms.py" xi "$REPORT_DIR/xi-bidi.log" | tee "$REPORT_DIR/xi-bidi-axioms.log"
    lake env bash -c 'export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"; exec lean --root="$3" -o "$1/RHClayAdmission.olean" "$2"' \
      _ "$BUILD" "$SIDECAR/RHClayAdmission.lean" "$SIDECAR" 2>&1 |
      tee "$REPORT_DIR/clay-admission.log"
    python3 "$SIDECAR/audit_p0_axioms.py" clay "$REPORT_DIR/clay-admission.log" |
      tee "$REPORT_DIR/clay-axiom-audit.log"
    REPLAY_TARGET=RHClayAdmission
  fi

  if [[ "${GRH_P0_FRESH_REPLAY:-$REPLAY}" == 1 ]]; then
    # Fresh replay of the deepest emitted endpoint includes Main and
    # RHAdmission; with Clay enabled it also includes the exact Clay adapter.
    # Axiom audits remain necessary: replay is not an axiom allowlist.
    lake env bash -c 'export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"; exec leanchecker --fresh --verbose "$2"' \
      _ "$BUILD" "$REPLAY_TARGET" 2>&1 | tee "$REPORT_DIR/fresh-kernel.log"
    grep -Fxq "replaying $REPLAY_TARGET with --fresh" "$REPORT_DIR/fresh-kernel.log" || {
      echo 'BLOCKED: missing exact terminal fresh-replay marker' >&2; exit 16;
    }
  fi

  if [[ "${GRH_P0_CHECK_DIRECTIONAL:-0}" == 1 ]]; then
    lake env lean "$SIDECAR/RHGRHP0DirectionalSourceCut.lean" 2>&1 |
      tee "$REPORT_DIR/directional-donor-lean.log"
  fi
  verify_dependency_pins | tee "$REPORT_DIR/dependency-pins-after.log"
  cmp "$REPORT_DIR/dependency-pins.log" "$REPORT_DIR/dependency-pins-after.log"
)
# Detect modifications made during the build. This is still a local trusted
# toolchain receipt, not independent checker or Agda/cross-version admission.
GRH_P0_VERIFY_ONLY=1 bash "$SIDECAR/checkout_fork_source.sh" "$CHECKOUT" | tee "$REPORT_DIR/source-pin-after.log"
verify_local_source | tee "$REPORT_DIR/dashi-source-after.log"
cmp "$REPORT_DIR/dashi-source-before.log" "$REPORT_DIR/dashi-source-after.log"
if [[ "${GRH_P0_FRESH_REPLAY:-$REPLAY}" == 1 ]]; then
  printf 'LOCAL SOURCE ADMISSION + FRESH KERNEL REPLAY: %s Lean %s\n' "$SOURCE" "$VERSION"
else
  printf 'LOCAL SOURCE BUILD + ADAPTER AXIOM AUDIT ONLY (fresh replay not requested): %s Lean %s\n' "$SOURCE" "$VERSION"
fi
printf 'Receipts: %s\n' "$REPORT_DIR"
if [[ "${GRH_P0_CLAY:-$REPLAY}" == 1 ]]; then
  printf 'SAME-KERNEL PINNED CLAY RH AND XI ADAPTER CHECKED (isolated %s).\n' "$VERSION"
fi
printf 'Still separate: root v4.28 compiled-environment proof import, Agda same-object transport, independent external checker acceptance.\n'
