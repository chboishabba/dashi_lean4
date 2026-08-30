/-
Regenerates the zeta-ladder picture of the twenty-six sporadic groups:

```
lake env lean scripts/GenerateSporadicZeta.lean
```
-/
import RequestProject.SporadicZetaSvg

#eval show IO Unit from do
  IO.FS.createDirAll "visualization"
  IO.FS.writeFile "visualization/sporadic-zeta-ladder.svg"
    SporadicZetaSvg.sporadicZetaLadderSvg
  IO.FS.writeFile "visualization/sporadic_zeta_masses.csv" SporadicZetaSvg.sporadicZetaCsv
  IO.println "wrote 2 files to visualization/"
