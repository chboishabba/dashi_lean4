/-
Regenerates the closure picture — the twenty-six sporadic groups, their lcm, the sporadic
ceiling and `ζ`:

```
lake env lean scripts/GenerateSporadicClosure.lean
```
-/
import RequestProject.SporadicClosureSvg

#eval show IO Unit from do
  IO.FS.createDirAll "visualization"
  IO.FS.writeFile "visualization/sporadic-zeta-closure.svg"
    SporadicClosureSvg.sporadicClosureSvg
  IO.FS.writeFile "visualization/sporadic_zeta_closure.csv"
    SporadicClosureSvg.sporadicClosureCsv
  IO.println "wrote 2 files to visualization/"
