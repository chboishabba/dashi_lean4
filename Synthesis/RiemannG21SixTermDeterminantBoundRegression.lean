import Synthesis.RiemannG21SixTermDeterminantBound

namespace Synthesis

example {r ta1 ta2 tp1 tp2 ea1 ea2 ep1 ep2 aa1 aa2 ap1 ap2 ca cp : ℝ}
    (hr0 : 0 <= r) (hr1 : r <= 1)
    (haa1 : 0 <= aa1) (haa2 : 0 <= aa2)
    (hap1 : 0 <= ap1) (hap2 : 0 <= ap2)
    (hca : 0 <= ca) (hcp : 0 <= cp)
    (hta1 : |ta1| <= r*aa1) (hta2 : |ta2| <= r*aa2)
    (htp1 : |tp1| <= r*ap1) (htp2 : |tp2| <= r*ap2)
    (hea1 : |ea1| <= r^5*ca) (hea2 : |ea2| <= 32*r^5*ca)
    (hep1 : |ep1| <= r^5*cp) (hep2 : |ep2| <= 32*r^5*cp) :
    |sixTermDetError ta1 ta2 tp1 tp2 ea1 ea2 ep1 ep2| <=
      r^6 * determinantErrorConstant aa1 aa2 ap1 ap2 ca cp := by
  exact sixTermDetError_le_coefficient hr0 hr1 haa1 haa2 hap1 hap2 hca hcp
    hta1 hta2 htp1 htp2 hea1 hea2 hep1 hep2

end Synthesis
