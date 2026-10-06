# Millennium external verification commands

```bash
python3 scripts/test_audit_millennium_external_targets.py
python3 scripts/check_millennium_external_source.py
bash scripts/check_millennium_external_trust.sh

# Requires network access:
bash scripts/vendor_millennium_targets.sh
python3 scripts/audit_millennium_external_targets.py

# Requires the DASHI Lean environment:
lake env lean MillenniumExternal/All.lean
```

The exact-head GitHub Actions workflow additionally builds the pinned upstream
repository under its own Lean 4.31 package graph before building the DASHI
terminal census under DASHI's graph.
