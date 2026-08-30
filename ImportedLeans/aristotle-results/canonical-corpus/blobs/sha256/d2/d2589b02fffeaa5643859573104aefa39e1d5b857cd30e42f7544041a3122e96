/-
Regenerates the SVG pictures in `visualization/` from the verified colouring.

Run from the project root with:

```
lake env lean scripts/GenerateSvg.lean
```
-/
import RequestProject.FiberSvg
import RequestProject.ModularSvg
import RequestProject.FiberSumSvg
import RequestProject.SporadicSvg
import RequestProject.ZetaExponentSvg
import RequestProject.ModularZetaSvg
import RequestProject.ExtendedPrimesSvg
import RequestProject.ZetaMoonshineSvg
import RequestProject.MoonshineBridgeSvg
import RequestProject.MoonshineZoomSvg
import RequestProject.MonsterSpiralSvg
import RequestProject.MonsterSpiral3DSvg
import RequestProject.TauWavesSvg
import RequestProject.SmallPrimeFibersSvg
import RequestProject.TauWavesSixSvg
import RequestProject.HeckeShapeSvg
import RequestProject.SporadicZetaSvg
import RequestProject.SporadicSpectrumSvg
import RequestProject.SporadicClosureSvg

open PrimeFibers

#eval show IO Unit from do
  IO.FS.createDirAll "visualization"
  IO.FS.writeFile "visualization/fibers-2-and-3.svg" twoThreeSvg
  IO.FS.writeFile "visualization/fibers-first-20-primes.svg" firstTwentySvg
  IO.FS.writeFile "visualization/modular-tau-fibers.svg" ModularGraph.tauGraphSvg
  IO.FS.writeFile "visualization/modular-tau-2-and-3.svg" ModularGraph.tauGraphTwoThreeSvg
  IO.FS.writeFile "visualization/fiber-abs-sums.svg" FiberSums.fiberSumsSvg
  IO.FS.writeFile "visualization/prime_fiber_sums.csv" FiberSums.fiberSumsCsv
  IO.FS.writeFile "visualization/sporadic-prime-grid.svg" SporadicSvg.sporadicGridSvg
  IO.FS.writeFile "visualization/sporadic-two-exponents.svg" SporadicSvg.twoFiberSvg
  IO.FS.writeFile "visualization/monster-zeta-euler.svg" SporadicSvg.monsterZetaSvg
  IO.FS.writeFile "visualization/sporadic_groups.csv" SporadicSvg.sporadicCsv
  IO.FS.writeFile "visualization/zeta-exponent-scale.svg" ZetaExponentSvg.zetaExponentSvg
  IO.FS.writeFile "visualization/sporadic_logloglog.csv" ZetaExponentSvg.lllCsv
  IO.FS.writeFile "visualization/modular-zeta.svg" ModularZetaSvg.modularZetaSvg
  IO.FS.writeFile "visualization/modular_zeta.csv" ModularZetaSvg.modularZetaCsv
  IO.FS.writeFile "visualization/fibers-first-50-primes.svg" ExtendedSvg.fiftyPrimeGridSvg
  IO.FS.writeFile "visualization/zeta-euler-50-primes.svg" ExtendedSvg.zetaEulerFiftySvg
  IO.FS.writeFile "visualization/extended_primes.csv" ExtendedSvg.extendedPrimesCsv
  IO.FS.writeFile "visualization/zeta-moonshine.svg" ZetaMoonshineSvg.zetaMoonshineSvg
  IO.FS.writeFile "visualization/zeta_moonshine.csv" ZetaMoonshineSvg.zetaMoonshineCsv
  IO.FS.writeFile "visualization/moonshine-domain-coloring.svg" MoonshineSvg.domainColoringSvg
  IO.FS.writeFile "visualization/moonshine-trajectories.svg" MoonshineSvg.trajectorySvg
  IO.FS.writeFile "visualization/moonshine_trajectories.csv" MoonshineSvg.trajectoryCsv
  IO.FS.writeFile "visualization/moonshine-trajectories-zoom.svg" MoonshineZoomSvg.zoomSvg
  IO.FS.writeFile "visualization/moonshine_zoom_spiral.csv" MoonshineZoomSvg.zoomCsv
  IO.FS.writeFile "visualization/monster-spiral.svg" MonsterSpiralSvg.monsterSpiralSvg
  IO.FS.writeFile "visualization/monster_spiral.csv" MonsterSpiralSvg.monsterSpiralCsv
  IO.FS.writeFile "visualization/monster-spiral-3d.svg" MonsterSpiral3DSvg.monsterSpiral3dSvg
  IO.FS.writeFile "visualization/monster-spiral-3d.html" MonsterSpiral3DSvg.monsterSpiral3dHtml
  IO.FS.writeFile "visualization/monster-spiral-3d.obj" MonsterSpiral3DSvg.monsterSpiral3dObj
  IO.FS.writeFile "visualization/monster_spiral_3d.csv" MonsterSpiral3DSvg.monsterSpiral3dCsv
  IO.FS.writeFile "visualization/modular-tau-waves-3d.svg" TauWavesSvg.wavesSvg
  IO.FS.writeFile "visualization/modular-tau-waves-3d.html" TauWavesSvg.wavesHtml
  IO.FS.writeFile "visualization/modular_tau_waves.csv" TauWavesSvg.wavesCsv
  IO.FS.writeFile "visualization/sporadic-small-prime-fibers.svg" SmallFiberSvg.smallFibersSvg
  IO.FS.writeFile "visualization/small_prime_fibers.csv" SmallFiberSvg.smallFibersCsv
  IO.FS.writeFile "visualization/monster-tau-waves-six.svg" TauWavesSixSvg.wavesSixSvg
  IO.FS.writeFile "visualization/monster-tau-waves-six.html" TauWavesSixSvg.wavesSixHtml
  IO.FS.writeFile "visualization/monster_tau_waves_six.csv" TauWavesSixSvg.wavesSixCsv
  IO.FS.writeFile "visualization/hecke-shape-efficiency.svg" HeckeShapeSvg.efficiencySvg
  IO.FS.writeFile "visualization/monster-shape-primes.svg" HeckeShapeSvg.monsterPrimesSvg
  IO.FS.writeFile "visualization/hecke_shapes.csv" HeckeShapeSvg.shapesCsv
  IO.FS.writeFile "visualization/sporadic-zeta-ladder.svg"
    SporadicZetaSvg.sporadicZetaLadderSvg
  IO.FS.writeFile "visualization/sporadic_zeta_masses.csv" SporadicZetaSvg.sporadicZetaCsv
  IO.FS.writeFile "visualization/sporadic-zeta-spectrum.svg"
    SporadicSpectrumSvg.sporadicSpectrumSvg
  IO.FS.writeFile "visualization/sporadic_zeta_spectrum.csv"
    SporadicSpectrumSvg.sporadicSpectrumCsv
  IO.FS.writeFile "visualization/sporadic-zeta-closure.svg"
    SporadicClosureSvg.sporadicClosureSvg
  IO.FS.writeFile "visualization/sporadic_zeta_closure.csv"
    SporadicClosureSvg.sporadicClosureCsv
  IO.println "wrote 47 files to visualization/"
