"""TimesFM candidate forecast receipt. No model execution or policy authority."""
from __future__ import annotations
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from math import isfinite
import hashlib
import json

LEVELS = tuple(i / 10 for i in range(1, 10))

def _utc(value: str) -> datetime:
    parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    if parsed.tzinfo is None or parsed.utcoffset() is None:
        raise ValueError("timezone-aware timestamp required")
    return parsed.astimezone(timezone.utc)

@dataclass(frozen=True)
class ForecastReceipt:
    model_id: str
    model_version: str
    model_source_commit: str
    checkpoint_digest: str
    dataset_id: str
    dataset_digest: str
    as_of: str
    input_cutoff: str
    target_names: tuple[str, ...]
    target_times: tuple[str, ...]
    point: tuple[tuple[float, ...], ...]
    quantiles: tuple[tuple[tuple[float, ...], ...], ...]
    known_future_names: tuple[str, ...] = ()
    known_future_availability: tuple[str, ...] = ()
    normalization_end: str = ""
    policy_mode: str = "shadow"
    allowed_to_trade: bool = False
    theorem_authority: bool = False
    physical_validation: bool = False

    def validate(self) -> None:
        asof, cutoff = _utc(self.as_of), _utc(self.input_cutoff)
        if cutoff > asof:
            raise ValueError("input cutoff exceeds as-of")
        if not self.normalization_end or _utc(self.normalization_end) > cutoff:
            raise ValueError("normalization leakage or missing window")
        if not self.model_id or not self.model_version or not self.model_source_commit:
            raise ValueError("model provenance required")
        if not self.dataset_id or not self.dataset_digest or not self.checkpoint_digest:
            raise ValueError("source/checkpoint provenance required")
        if not self.target_names or len(set(self.target_names)) != len(self.target_names):
            raise ValueError("distinct target names required")
        if not self.target_times or any(_utc(t) <= asof for t in self.target_times):
            raise ValueError("forecast times must be future")
        if list(map(_utc, self.target_times)) != sorted(map(_utc, self.target_times)):
            raise ValueError("forecast times out of order")
        if len(set(self.target_times)) != len(self.target_times):
            raise ValueError("duplicate forecast times")
        if len(self.known_future_names) != len(self.known_future_availability):
            raise ValueError("future covariate metadata mismatch")
        if len(set(self.known_future_names)) != len(self.known_future_names):
            raise ValueError("duplicate future covariates")
        if any(_utc(t) > asof for t in self.known_future_availability):
            raise ValueError("future covariate not known as-of prediction")
        if len(self.point) != len(self.target_names) or len(self.quantiles) != len(self.point):
            raise ValueError("variate shape mismatch")
        for values, qs in zip(self.point, self.quantiles):
            if len(values) != len(self.target_times) or len(qs) != len(values):
                raise ValueError("horizon shape mismatch")
            for x, row in zip(values, qs):
                if not isfinite(x) or len(row) != 9 or not all(isfinite(v) for v in row):
                    raise ValueError("nonfinite or malformed quantiles")
        if self.policy_mode != "shadow" or self.allowed_to_trade or self.theorem_authority or self.physical_validation:
            raise ValueError("candidate receipt cannot be promoted")

    def quantile_crossings(self) -> int:
        self.validate()
        return sum(a > b for series in self.quantiles for row in series
                   for a, b in zip(row, row[1:]))

    def canonical(self) -> str:
        self.validate()
        return json.dumps(asdict(self), sort_keys=True, separators=(",", ":"), allow_nan=False)

    def digest(self) -> str:
        return hashlib.sha256(self.canonical().encode("utf-8")).hexdigest()

def shadow_summary(receipt: ForecastReceipt) -> dict:
    receipt.validate()
    return {"receipt_sha256": receipt.digest(), "mode": "shadow",
            "allowed_to_trade": False, "quantile_crossings": receipt.quantile_crossings(),
            "targets": len(receipt.target_names), "horizon": len(receipt.target_times)}

def ns_screen_summary(receipt: ForecastReceipt, *, observed: tuple[tuple[float, ...], ...]) -> dict:
    receipt.validate()
    if len(observed) != len(receipt.point) or any(len(x) != len(receipt.target_times) for x in observed):
        raise ValueError("observation shape mismatch")
    if not all(isfinite(v) for row in observed for v in row):
        raise ValueError("nonfinite observation")
    n = sum(map(len, observed))
    mse = sum((a-b)**2 for left, right in zip(observed, receipt.point)
              for a, b in zip(left, right)) / n
    return {"receipt_sha256": receipt.digest(), "mse": mse,
            "empirical_only": True, "theorem_authority": False, "clay_authority": False}
