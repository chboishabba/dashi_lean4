/-
Regenerates the six zoomed-in animated panels and the page that holds them:

```
lake env lean scripts/GenerateAnim.lean
```
-/
import RequestProject.MonsterSpiral3DAnim

#eval show IO Unit from do
  IO.FS.createDirAll "visualization"
  for (name, body) in MonsterSpiral3DAnim.panelAnimFiles do
    IO.FS.writeFile ("visualization/" ++ name) body
    IO.println ("wrote visualization/" ++ name)
  IO.FS.writeFile "visualization/monster-spiral-3d-panels.html"
    MonsterSpiral3DAnim.panelAnimHtml
  IO.println "wrote visualization/monster-spiral-3d-panels.html"
