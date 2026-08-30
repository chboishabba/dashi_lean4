/-
Regenerates the spectrum picture of the twenty-six sporadic groups as a function of `s`:

```
lake env lean scripts/GenerateSporadicSpectrum.lean
```
-/
import RequestProject.SporadicSpectrumSvg

#eval show IO Unit from do
  IO.FS.createDirAll "visualization"
  IO.FS.writeFile "visualization/sporadic-zeta-spectrum.svg"
    SporadicSpectrumSvg.sporadicSpectrumSvg
  IO.FS.writeFile "visualization/sporadic_zeta_spectrum.csv"
    SporadicSpectrumSvg.sporadicSpectrumCsv
  IO.println "wrote 2 files to visualization/"
