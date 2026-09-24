import RequestProject.Visualization
import RequestProject.ScanVisualization
import RequestProject.EyeCandy
import RequestProject.Heatmap3D
import RequestProject.RepairVisualization
import RequestProject.Repair3D
import RequestProject.RepairAtlas3D
import RequestProject.TwistSeriesViz
import RequestProject.PivotLadderViz
import RequestProject.StudentGallery
import RequestProject.PascalAtlasViz

/-!
Writes the pictures of `RequestProject/Visualization.lean`,
`RequestProject/ScanVisualization.lean`, `RequestProject/EyeCandy.lean`,
`RequestProject/Heatmap3D.lean`, `RequestProject/RepairVisualization.lean`,
`RequestProject/Repair3D.lean`, `RequestProject/RepairAtlas3D.lean` and
`RequestProject/TwistSeriesViz.lean`, `RequestProject/PivotLadderViz.lean` and the atlas sheet and the six student
posters of `RequestProject/StudentGallery.lean` into `svg/`,
together with the gallery page `svg/index.html`.

Run from the project root with

```
lake env lean --run scripts/GenerateSvg.lean
```
-/

def outputs : List (String × String) :=
  [ ("svg/frobenius-orbits.svg", GF27Viz.orbitsSvg),
    ("svg/frobenius-norm-retraction.svg", GF27Viz.normSvg),
    ("svg/center-retraction.svg", CenterViz.centerSvg),
    ("svg/field-size-scan.svg", ScanViz.scanSvg),
    ("svg/field-size-scan-degrees.svg", ScanViz.degreeSvg),
    ("svg/frobenius-clock.svg", ClockViz.clockSvg),
    ("svg/frobenius-defect-heatmap.svg", HeatViz.heatSvg),
    ("svg/frobenius-defect-3d.svg", Heat3DViz.heat3dSvg),
    ("svg/gf9-error-repair.svg", RepairViz.repairSvg),
    ("svg/repair-wheel-3d.svg", Repair3D.wheelSvg),
    ("svg/repair-gears-3d.svg", Repair3D.gearsSvg),
    ("svg/repair-atlas-3d.svg", AtlasViz.atlasSvg),
    ("svg/retraction-analogy.svg", HeroViz.analogySvg),
    ("svg/twist-1-dead-dial.svg", TwistViz.act1Svg),
    ("svg/twist-2-still-onto.svg", TwistViz.act2Svg),
    ("svg/twist-3-the-twist.svg", TwistViz.act3Svg),
    ("svg/twist-4-repaired-map.svg", TwistViz.act4Svg),
    ("svg/twist-5-nine-twists.svg", TwistViz.act5Svg),
    ("svg/twist-6-census.svg", TwistViz.act6Svg),
    ("svg/twist-7-pivot-ladder.svg", PivotViz.act7Svg),
    ("svg/student-0-atlas.svg", PascalAtlas.atlasSvg),
    ("svg/student-1-freshmans-dream.svg", StudentViz.dreamSvg),
    ("svg/student-2-cyclotomic-clocks.svg", StudentViz.clocksSvg),
    ("svg/student-3-subfield-tower.svg", StudentViz.towerSvg),
    ("svg/student-4-dictionary.svg", StudentViz.dictionarySvg),
    ("svg/student-5-orbit-spiral.svg", StudentViz.spiralSvg),
    ("svg/student-6-exercise-ladder.svg", StudentViz.ladderSvg),
    ("svg/index.html", Gallery.indexHtml) ]

def main : IO Unit := do
  IO.FS.createDirAll "svg"
  for (file, contents) in outputs do
    IO.FS.writeFile file contents
    IO.println ("wrote " ++ file)
