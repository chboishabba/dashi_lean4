#!/usr/bin/env python3
"""Why 883/8 is close to 888/8 in the SELECTED rational Albert triality map.

Original owners: Griess (1990) homogeneous Albert multiplication and
the Lean native rational-octonion multiplication. A source/target
512-component CUBIC comparison in one selected Peirce basis yields
R=||S-T||²=883/8. This is NOT a coordinate-independent invariant.
Do not infer Monster, RH, 369 or physics from this near-integer.
"""
from fractions import Fraction as F
from pathlib import Path
import runpy
p=runpy.run_path(str(Path(__file__).with_name(
 "check_griess1990_native_albert_rational_peirce_isometry.py")))
S01,S12,S02=p["S01"],p["S12"],p["S02"]
X01,X12,X02=p["X01"],p["X12"],p["X02"]
prod,B,octmul=p["prod"],p["B"],p["octmul"]
source_norm=target_norm=overlap=F(0)
for i in range(8):
 for j in range(8):
  ab=prod(S01[i],S12[j])
  uv=octmul(X01[i],X12[j])
  for k in range(8):
   sv=F(3*B(ab,S02[k])[0])
   tv=sum((x*y for x,y in zip(uv,X02[k])),F(0))
   source_norm+=sv*sv
   target_norm+=tv*tv
   overlap+=sv*tv
assert source_norm==F(251,4)
assert target_norm==F(507,8)
assert overlap==F(63,8)
R=source_norm+target_norm-2*overlap
assert R==F(883,8)
assert source_norm+target_norm+2*overlap==F(1135,8)
R888=F(888,8)
desired_overlap=(source_norm+target_norm-R888)/2
assert desired_overlap==F(121,16)
assert desired_overlap-overlap==-F(5,16)
print('SOURCE tensor norm square',source_norm)
print('TARGET tensor norm square',target_norm)
print('SOURCE-TARGET overlap',overlap)
print('SELECTED squared discrepancy',R)
print('HYPOTHETICAL 888/8',R888)
print('OVERLAP required with fixed norms',desired_overlap)
print('CHANGE needed in overlap',desired_overlap-overlap)
print('Conclusion: 888/8 would be another nonzero, map-dependent residual, not full triality.')
