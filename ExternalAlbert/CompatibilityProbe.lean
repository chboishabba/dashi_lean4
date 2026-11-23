import Jordan.AlbertAlgebra

/-!
This file is intentionally outside the normal DASHI rollup.  CI exposes the
pinned external package on `LEAN_PATH` and attempts to compile these checks
under the DASHI toolchain.  Failure is a compatibility result, not a reason to
weaken either package's native toolchain.
-/

#check Octonion.AlbertAlgebra
#check Octonion.albertEquiv
#check Octonion.ofAlbert
#check Octonion.trace
#check Octonion.det
#check Octonion.detTrace
