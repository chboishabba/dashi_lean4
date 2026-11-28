#!/usr/bin/env python3
"""Local forced C/D admission: original source pin, actual version, fresh
direct theorem axiom log, no external acceptance claim. No network fallback.
Reuse the existing SubmissionAudit and nested project, not another endpoint.
"""
import pathlib, subprocess, tempfile, shutil, json, re, os, sys, hashlib

ROOT=pathlib.Path(__file__).resolve().parent
PIN="f9e8bc5b38b6e212696e8a30e3e91517af887bbd"
VERSION="4.34.0-rc2"
PREFIX="DASHILiteralClayNS.SubmissionAudit."
TARGETS=("NavierStokesR3.theorem_1_1","NavierStokesR3.comparator_of_breakdown",
         PREFIX+"directComparatorC",PREFIX+"directClayC",PREFIX+"directClayC_roundTrip",
         "PeriodicPaper.periodic_corollary","NavierStokes.ComparatorBridge.option_D_of_paper_candidate",
         PREFIX+"directComparatorD",PREFIX+"directClayD",PREFIX+"directClayD_roundTrip",
         PREFIX+"dualRouteReceipt")
CANONICAL=("DASHILiteralClayNS.dashiDirectExactFeffermanC","DASHILiteralClayNS.dashiDirectExactFeffermanD")
ALLOWED={"propext","Classical.choice","Quot.sound"}
SOURCE_BLOBS={
    "NavierStokes/R3/Theorem.lean":"4151e7c90a9de31d8454fc49932b066d475bed08",
    "NavierStokes/R3/ComparatorBridge.lean":"386c0981a0bdd32b68386f89113180d7f7666ea9",
    "NavierStokes/PeriodicPaperTheorem.lean":"e7cdc29594f635a0eebf6967352a148be1b818e9",
    "NavierStokes/PeriodicPaperComparator.lean":"8362165515d86500f55404382e3cf11689b0a584",
    "lean-toolchain":"b814d987e0c93cb99938be934d9b277778495ba1",
}

def audit(log,targets=TARGETS):
    out={}
    for name in targets:
        pat=(r"(?m)^(?:[^\r\n]*:\d+:\d+:[ \t]*info:[ \t]*|info:[ \t]*)?'"+
             re.escape(name)+r"' (?:depends on axioms:[ \t]*\[([^\]]*)\]|does not depend on any axioms)[ \t]*\r?$")
        matches=list(re.finditer(pat,log))
        if len(matches)!=1:raise ValueError(f"{name}: expected one receipt, got {len(matches)}")
        raw=matches[0].group(1)
        axioms=[] if raw is None else [v.strip() for v in raw.split(",")]
        if any(not a for a in axioms) or len(axioms)!=len(set(axioms)) or set(axioms)-ALLOWED:
            raise ValueError(f"{name}: nonstandard or malformed axioms {axioms}")
        out[name]=sorted(axioms)
    return out

def git(path,*args):
    return subprocess.check_output(["git","-C",str(path),*args],text=True).strip()

def clean(path,expected=None):
    head=git(path,"rev-parse","HEAD")
    if expected is not None and head!=expected:raise ValueError(f"revision drift: {path}")
    if git(path,"status","--porcelain","--untracked-files=all"):
        raise ValueError(f"dirty source checkout: {path}")
    if any(s[:1]=="S" or s[:1].islower() for s in git(path,"ls-files","-v").splitlines()):
        raise ValueError(f"hidden tracked sources: {path}")
    return head

def local_source():
    head=git(ROOT,"rev-parse","HEAD")
    files=git(ROOT,"ls-files","--",".").splitlines()
    tracked=set(files)
    for f in files:
        if (f.endswith((".lean",".py",".toml")) or f=="lean-toolchain") and not (ROOT/f).is_file():
            raise ValueError(f"deleted admission input: {f}")
    # A newly introduced .lean module could otherwise be loaded by Lake
    # without appearing in the recorded tracked-source hash set.
    for p in ROOT.rglob("*.lean"):
        rel=p.relative_to(ROOT)
        if any(part in (".lake",".git","vendor") for part in rel.parts):continue
        if rel.as_posix() not in tracked:
            raise ValueError(f"untracked Lean admission input: {rel}")
    blobs={}
    for f in files:
        p=ROOT/f
        if p.is_file() and (p.suffix in (".lean",".py",".toml") or p.name=="lean-toolchain"):
            got=git(ROOT,"hash-object","--no-filters",str(p))
            want=git(ROOT,"rev-parse",f"HEAD:ExternalClayNS/{f}")
            if got!=want:raise ValueError(f"dirty admission input: {f}")
            blobs[f]=got
    for f in ("SubmissionAudit.lean","LeanDojoExactTerminal.lean","ClaySpec.lean","Gap.lean","ClauseAudit.lean","lakefile.toml","lean-toolchain","check_direct_admission.py"):
        if f not in blobs:raise ValueError("missing tracked source "+f)
    if (ROOT/"lean-toolchain").read_text().strip()!="leanprover/lean4:v"+VERSION:
        raise ValueError("nested toolchain mismatch")
    if PIN not in (ROOT/"lakefile.toml").read_text():raise ValueError("declared pin mismatch")
    return dict(head=head,blobs=blobs)

def packages():
    manifest_bytes=(ROOT/"lake-manifest.json").read_bytes()
    manifest=json.loads(manifest_bytes)
    base=ROOT/manifest.get("packagesDir",".lake/packages")
    heads={}
    for p in manifest["packages"]:
        if p["type"]!="git":raise ValueError("unexpected non-git package "+p["name"])
        heads[p["name"]]=clean(base/p["name"],p["rev"])
    if heads.get("NavierStokesAndEuler")!=PIN:raise ValueError("upstream pin mismatch")
    upstream=base/"NavierStokesAndEuler"
    for f,blob in SOURCE_BLOBS.items():
        if git(upstream,"rev-parse",f"HEAD:{f}")!=blob or git(upstream,"hash-object","--no-filters",str(upstream/f))!=blob:
            raise ValueError("source blob drift: "+f)
    return dict(heads=heads,manifest_sha256=hashlib.sha256(manifest_bytes).hexdigest())

def run():
    if not shutil.which("lake"):raise ValueError("pinned Lean/lake unavailable")
    if not (ROOT/"lake-manifest.json").is_file():raise ValueError("local manifest absent; install pinned dependencies first")
    before=local_source();deps=packages()
    env=dict(os.environ)
    for k in ("ELAN_TOOLCHAIN","LEAN_PATH","LEAN_SRC_PATH","LEAN_SYSROOT","LEAN_CC"):env.pop(k,None)
    report=pathlib.Path(tempfile.mkdtemp(prefix="ns-direct-admission-"))
    def cmd(name,*args):
        p=subprocess.run(args,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        (report/name).write_text(p.stdout);print(p.stdout,end="")
        if p.returncode:raise ValueError(f"{name} failed; logs {report}")
        return p.stdout
    v=cmd("version.log","lake","env","lean","--version")
    if f"version {VERSION}," not in v:raise ValueError("actual Lean version mismatch")
    cmd("build.log","lake","build")
    # Force elaboration of this source; cached build alone gives no axiom receipt.
    build=report/"admission-olean";build.mkdir()
    log=cmd("direct.log","lake","env","lean",f"--root={ROOT}","-o",str(build/"SubmissionAudit.olean"),"SubmissionAudit.lean")
    result=audit(log)
    # A successful source elaboration and clean axiom log are not a
    # fresh kernel replay. Fail closed if the pinned toolchain cannot
    # replay the isolated terminal and all of its dependencies.
    canonical=cmd("canonical.log","lake","env","bash","-c",
              'export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"; exec lean --root="$2" -o "$1/LeanDojoExactTerminal.olean" "$2/LeanDojoExactTerminal.lean"',
              "_",str(build),str(ROOT))
    result.update(audit(canonical,CANONICAL))
    fresh=cmd("fresh-kernel.log","lake","env","bash","-c",
              'export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"; exec leanchecker --fresh --verbose LeanDojoExactTerminal',
              "_",str(build))
    if "replaying LeanDojoExactTerminal with --fresh" not in fresh.splitlines():
        raise ValueError("missing exact canonical terminal fresh-replay marker")
    if before!=local_source() or deps!=packages():raise ValueError("source drift during run")
    (report/"receipt.json").write_text(json.dumps(dict(source=before,packages=deps,axioms=result,fresh_replay="LeanDojoExactTerminal"),indent=2))
    print("PASS direct C/D pinned native admission + fresh replay",report)
    print("Independent physical/manuscript verification remains separate.")

if __name__=="__main__":
    try:run()
    except (ValueError,OSError,subprocess.CalledProcessError,KeyError) as exc:
        print("BLOCKED:",exc,file=sys.stderr);raise SystemExit(1)
