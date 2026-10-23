"""Fail-closed TimesFM receipt regression tests (stdlib only)."""
import unittest
from dataclasses import replace
from integration.timesfm3_candidate_receipt import (
    ForecastReceipt, shadow_summary, ns_screen_summary,
)

def fixture():
    return ForecastReceipt(
        model_id="google/timesfm", model_version="3.0",
        model_source_commit="pinned-commit-fixture",
        checkpoint_digest="sha256:fixture", dataset_id="fixture",
        dataset_digest="sha256:dataset",
        as_of="2026-10-23T08:00:00Z",
        input_cutoff="2026-10-23T08:00:00+00:00",
        normalization_end="2026-10-23T07:59:00+00:00",
        target_names=("energy",), target_times=("2026-10-23T08:01:00Z",),
        point=((2.0,),),
        quantiles=(((1.,1.2,1.4,1.6,2.,2.4,2.6,2.8,3.),),),
    )

class ReceiptTests(unittest.TestCase):
    def test_candidate_digest_and_shadow(self):
        a=fixture()
        self.assertEqual(a.digest(), a.digest())
        self.assertEqual(shadow_summary(a)["allowed_to_trade"], False)
        self.assertEqual(shadow_summary(a)["quantile_crossings"], 0)

    def test_nonpromotion(self):
        for field in ("allowed_to_trade", "theorem_authority", "physical_validation"):
            with self.subTest(field=field), self.assertRaises(ValueError):
                replace(fixture(), **{field: True}).validate()

    def test_temporal_leakage(self):
        for variant in (
            {"input_cutoff": "2026-10-23T08:01:00Z"},
            {"normalization_end": "2026-10-23T08:01:00Z"},
            {"target_times": ("2026-10-23T07:59:00Z",)},
            {"known_future_names": ("calendar",),
             "known_future_availability": ("2026-10-23T09:00:00Z",)},
            {"as_of": "2026-10-23T08:00:00"},
        ):
            with self.subTest(variant=variant), self.assertRaises(ValueError):
                replace(fixture(), **variant).validate()

    def test_quantile_crossing_diagnostic_not_authority(self):
        a=replace(fixture(), quantiles=(((2.,1.,1.4,1.6,2.,2.4,2.6,2.8,3.),),))
        self.assertEqual(a.quantile_crossings(), 1)
        self.assertFalse(shadow_summary(a)["allowed_to_trade"])

    def test_ns_empirical_evaluation(self):
        result=ns_screen_summary(fixture(), observed=((3.0,),))
        self.assertEqual(result["mse"], 1.0)
        self.assertFalse(result["theorem_authority"])
        self.assertFalse(result["clay_authority"])

    def test_shapes(self):
        with self.assertRaises(ValueError):
            replace(fixture(), point=((1.0,2.0),)).validate()

if __name__ == "__main__":
    unittest.main()
