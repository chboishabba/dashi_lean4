#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
files = [
    ROOT / "Dashi/Biology/GABANeuroAIContextSnowballExact.lean",
    ROOT / "Dashi/Biology/GABANeuroAIContextSnowballRegression.lean",
    ROOT / "Dashi/Biology/GABANeuroAIContextParetoSnowballExact.lean",
    ROOT / "Dashi/Biology/GABANeuroAIContextParetoSnowballRegression.lean",
    ROOT / "Dashi/Biology/NeuralPredictionDirectionExact.lean",
    ROOT / "Dashi/Biology/NeuralPredictionDirectionRegression.lean",
    ROOT / "Dashi/Biology/NeuralPredictionAcquisitionParetoExact.lean",
    ROOT / "Dashi/Biology/NeuralPredictionAcquisitionParetoRegression.lean",
]
text = "\n".join(p.read_text(encoding="utf-8") for p in files)
required = [
    "metaTRIBEv2Receipt",
    "metaBrain2QwertyReceipt",
    "scholz2017ViralityReceipt",
    "chan2023SharingReceipt",
    "neuralink2026CalibrationReceipt",
    "stimulusToBrainEncoding",
    "brainToLanguageDecoding",
    "brainToActionDecoding",
    "brainResponseToPopulationOutcome",
    "canonicalBrainModelMechanismBoundary",
    "canonicalNeuralinkProvenanceSplit",
    "10.1016/j.intmar.2020.06.003",
    "canonicalPeripheralCentralPKDesignBridge",
    "canonicalCrossParticipantBCIDesignMap",
    "canonicalAcquisitionFrontier",
    "canonicalPredictionAcquisitionFrontier",
    "canonicalMultimodalInterfaceBoundary",
    "crossParticipantBCIAcquisition",
    "neuralinkIndependentReplicationAcquisition",
]
missing = [x for x in required if x not in text]
if missing:
    raise SystemExit("missing required neuro-AI snowball surface: " + ", ".join(missing))
forbidden = [
    "metaViralityIsMetaAuthored :",
    "fMRIProvesMindReading :",
    "serumGABAEqualsBrainGABA :",
    "weeklyCalibrationUniversal :",
    "encodingEqualsDecoding :",
    "representationSimilarityEqualsMechanism :",
]
found = [x for x in forbidden if x in text]
if found:
    raise SystemExit("forbidden overclaim declaration found: " + ", ".join(found))
print("Lean GABA/neuro-AI Pareto snowball source surface: OK")
