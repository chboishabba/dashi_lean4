# Literal Clay Navier–Stokes terminal project

This nested project is pinned to Lean 4.34.0-rc2, matching the released
OpenAI Navier–Stokes proof, so it does not perturb the parent dashi_lean4
Lean 4.28 environment.

It vendors the independent semantic-gap audit's frozen `ClaySpec.lean`,
`Gap.lean`, and `Adapter.lean` with provenance, then adds
`LiteralABCD.lean`.

Terminal declarations:

- `DASHILiteralClayNS.ClayOptionA`
- `DASHILiteralClayNS.ClayOptionB`
- `DASHILiteralClayNS.ClayOptionC`
- `DASHILiteralClayNS.ClayOptionD`
- `DASHILiteralClayNS.literalClayC`
- `DASHILiteralClayNS.literalClayD`
- `DASHILiteralClayNS.literalAnyOneClayResolution`

Run:

```bash
cd ExternalClayNS
lake update
lake exe cache get
lake build
```

Pinned proof: openai/NavierStokesAndEuler@f9e8bc5b38b6e212696e8a30e3e91517af887bbd

Semantic bridge source:
francescoantoniodeluca/navier-stokes-formal-audit@c2e4f438f7af8bbf222a59801696aca2c3c15b6f
