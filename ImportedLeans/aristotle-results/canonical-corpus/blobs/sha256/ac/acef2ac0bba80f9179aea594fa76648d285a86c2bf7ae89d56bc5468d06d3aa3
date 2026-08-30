/-
Regenerates just the six-prime wave pictures.

Run from the project root with:

```
lake env lean scripts/GenerateWavesSix.lean
```
-/
import RequestProject.TauWavesSixSvg

#eval show IO Unit from do
  IO.FS.createDirAll "visualization"
  IO.FS.writeFile "visualization/monster-tau-waves-six.svg" TauWavesSixSvg.wavesSixSvg
  IO.FS.writeFile "visualization/monster-tau-waves-six.html" TauWavesSixSvg.wavesSixHtml
  IO.FS.writeFile "visualization/monster_tau_waves_six.csv" TauWavesSixSvg.wavesSixCsv
  IO.println "wrote 3 files to visualization/"
