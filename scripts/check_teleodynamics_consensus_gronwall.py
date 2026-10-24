#!/usr/bin/env python3
"""Dependency-free numerical preflight for the scalar consensus Gronwall cut.

This is not Lean/kernel evidence.  It stress-tests the exact scalar implication
used by Integration/TeleodynamicsConsensusGronwall.lean on analytically soluble
trajectories E(t)=E0 exp(-a t) with a >= 2 lambda, hence
E'(t) <= -2 lambda E(t).
"""

import json
import math
import random

SEED = 7
CASES = 10_000


def main() -> None:
    random.seed(SEED)
    max_ratio = 0.0
    max_excess = float("-inf")

    for _ in range(CASES):
        lam = 10.0 ** random.uniform(-3.0, 2.0)
        e0 = 10.0 ** random.uniform(-3.0, 3.0)
        decay = (2.0 * lam) * random.uniform(1.0, 10.0)
        t = random.uniform(0.0, 20.0 / lam)

        energy = e0 * math.exp(-decay * t)
        bound = e0 * math.exp(-2.0 * lam * t)

        tolerance = 1e-12 * max(1.0, bound)
        assert energy <= bound + tolerance

        if bound > 0.0:
            max_ratio = max(max_ratio, energy / bound)
        max_excess = max(max_excess, energy - bound)

    print(json.dumps({
        "seed": SEED,
        "cases": CASES,
        "tested_implication": "E' <= -2 lambda E => E(t) <= E0 exp(-2 lambda t)",
        "all_passed": True,
        "maximum_energy_to_bound_ratio": max_ratio,
        "maximum_energy_minus_bound": max_excess,
        "kernel_evidence": False,
    }, indent=2))


if __name__ == "__main__":
    main()
