/-
Regenerates only the three-dimensional views (fast path for iterating on them):

```
lake env lean scripts/Generate3d.lean
```
-/
import RequestProject.MonsterSpiral3DSvg

#eval show IO Unit from do
  IO.FS.createDirAll "visualization"
  IO.FS.writeFile "visualization/monster-spiral-3d.svg" MonsterSpiral3DSvg.monsterSpiral3dSvg
  IO.FS.writeFile "visualization/monster-spiral-3d.html" MonsterSpiral3DSvg.monsterSpiral3dHtml
  IO.FS.writeFile "visualization/monster-spiral-3d.obj" MonsterSpiral3DSvg.monsterSpiral3dObj
  IO.FS.writeFile "visualization/monster_spiral_3d.csv" MonsterSpiral3DSvg.monsterSpiral3dCsv
  IO.println "wrote 4 files to visualization/"
