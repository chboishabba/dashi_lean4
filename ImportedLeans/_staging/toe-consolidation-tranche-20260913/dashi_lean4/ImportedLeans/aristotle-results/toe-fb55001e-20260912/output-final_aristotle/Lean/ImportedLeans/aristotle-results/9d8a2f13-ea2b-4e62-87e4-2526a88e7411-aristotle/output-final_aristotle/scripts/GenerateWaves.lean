/-
Regenerates only the three-dimensional wave/interference views (fast path):

```
lake env lean scripts/GenerateWaves.lean
```
-/
import RequestProject.TauWavesSvg

#eval show IO Unit from do
  IO.FS.createDirAll "visualization"
  IO.FS.writeFile "visualization/modular-tau-waves-3d.svg" TauWavesSvg.wavesSvg
  IO.FS.writeFile "visualization/modular-tau-waves-3d.html" TauWavesSvg.wavesHtml
  IO.FS.writeFile "visualization/modular_tau_waves.csv" TauWavesSvg.wavesCsv
  IO.println "wrote 3 files to visualization/"
