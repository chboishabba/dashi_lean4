#!/usr/bin/env python3
"""Render Klüver form-constant geometry as deterministic SVG artifacts.

This is a visualization surface, not a theorem generator.  The classifier is
the four-case Agda surface:

    openLoop=false, radialRing=0     -> cobweb
    openLoop=false, radialRing=suc _ -> lattice
    openLoop=true,  radialRing=0     -> tunnel
    openLoop=true,  radialRing=suc _ -> spiral

The spiral and ring/tunnel curves follow the Lean log-polar equations in
FormConstantGeometry.lean.  The lattice panel uses the six M6 wavevectors from
the Lean `hexWave` definition.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Literal

FormConstant = Literal["lattice", "tunnel", "spiral", "cobweb"]

SVG_NS = "http://www.w3.org/2000/svg"
DEFAULT_OUT = Path("artifacts/form_constants")


@dataclass(frozen=True)
class Geometry:
    radial_ring: int
    angular_sector: int
    open_loop: bool


@dataclass(frozen=True)
class RenderSpec:
    name: FormConstant
    geometry: Geometry
    title: str
    subtitle: str
    accent: str


SPECS: dict[FormConstant, RenderSpec] = {
    "cobweb": RenderSpec(
        "cobweb",
        Geometry(radial_ring=0, angular_sector=12, open_loop=False),
        "Cobweb",
        "Agda: openLoop=false, radialRing=zero",
        "#f59e0b",
    ),
    "lattice": RenderSpec(
        "lattice",
        Geometry(radial_ring=5, angular_sector=6, open_loop=False),
        "Lattice / honeycomb",
        "Lean: six M6 wavevectors on |k|=k0",
        "#14b8a6",
    ),
    "tunnel": RenderSpec(
        "tunnel",
        Geometry(radial_ring=0, angular_sector=16, open_loop=True),
        "Tunnel",
        "Lean: m=0 log-polar ring fronts",
        "#60a5fa",
    ),
    "spiral": RenderSpec(
        "spiral",
        Geometry(radial_ring=5, angular_sector=9, open_loop=True),
        "Spiral",
        "Lean: r=exp((c - m theta) / f)",
        "#f472b6",
    ),
}


def classify_geometry(geometry: Geometry) -> FormConstant:
    """Mirror Ontology.Brain.BrainVisualFormConstantSurface.classifyGeometry."""
    if not geometry.open_loop and geometry.radial_ring == 0:
        return "cobweb"
    if not geometry.open_loop:
        return "lattice"
    if geometry.radial_ring == 0:
        return "tunnel"
    return "spiral"


def esc(value: str) -> str:
    return (
        value.replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
    )


def fmt(value: float) -> str:
    return f"{value:.2f}".rstrip("0").rstrip(".")


def polar(cx: float, cy: float, r: float, theta: float) -> tuple[float, float]:
    return cx + r * math.cos(theta), cy + r * math.sin(theta)


def polyline(points: Iterable[tuple[float, float]], **attrs: str) -> str:
    attr = " ".join(f'{key.replace("_", "-")}="{esc(value)}"' for key, value in attrs.items())
    pts = " ".join(f"{fmt(x)},{fmt(y)}" for x, y in points)
    return f'<polyline points="{pts}" {attr}/>'


def circle(cx: float, cy: float, r: float, **attrs: str) -> str:
    attr = " ".join(f'{key.replace("_", "-")}="{esc(value)}"' for key, value in attrs.items())
    return f'<circle cx="{fmt(cx)}" cy="{fmt(cy)}" r="{fmt(r)}" {attr}/>'


def line(x1: float, y1: float, x2: float, y2: float, **attrs: str) -> str:
    attr = " ".join(f'{key.replace("_", "-")}="{esc(value)}"' for key, value in attrs.items())
    return f'<line x1="{fmt(x1)}" y1="{fmt(y1)}" x2="{fmt(x2)}" y2="{fmt(y2)}" {attr}/>'


def panel_frame(spec: RenderSpec, width: int, height: int, body: str) -> str:
    source = (
        "sources: dashi_lean4/DASHI/Klüver's Form Constants_aristotle/"
        "FormConstantGeometry.lean; dashi_agda/Ontology/Brain/"
        "BrainVisualFormConstantSurface.agda"
    )
    return f'''<svg xmlns="{SVG_NS}" width="{width}" height="{height}" viewBox="0 0 {width} {height}" role="img" aria-labelledby="title desc">
  <title id="title">{esc(spec.title)} form constant</title>
  <desc id="desc">{esc(spec.subtitle)}; {esc(source)}</desc>
  <defs>
    <radialGradient id="bg" cx="50%" cy="45%" r="70%">
      <stop offset="0%" stop-color="#182033"/>
      <stop offset="72%" stop-color="#0b1020"/>
      <stop offset="100%" stop-color="#05070d"/>
    </radialGradient>
    <filter id="soft-glow" x="-30%" y="-30%" width="160%" height="160%">
      <feGaussianBlur stdDeviation="1.8" result="blur"/>
      <feMerge>
        <feMergeNode in="blur"/>
        <feMergeNode in="SourceGraphic"/>
      </feMerge>
    </filter>
  </defs>
  <rect width="100%" height="100%" fill="url(#bg)"/>
  <g transform="translate(0 20)">
    {body}
  </g>
  <text x="28" y="{height - 48}" fill="#e5eefc" font-family="Inter, Arial, sans-serif" font-size="24" font-weight="700">{esc(spec.title)}</text>
  <text x="28" y="{height - 22}" fill="#9aa8bf" font-family="Inter, Arial, sans-serif" font-size="13">{esc(spec.subtitle)}</text>
</svg>
'''


def render_cobweb(spec: RenderSpec, width: int, height: int) -> str:
    cx, cy = width / 2, height / 2 - 6
    max_r = min(width, height) * 0.36
    parts: list[str] = []
    for i in range(1, 10):
        r = max_r * i / 9
        parts.append(circle(cx, cy, r, fill="none", stroke="#f8d184", stroke_width="1.1", opacity=str(0.18 + i * 0.045)))
    for j in range(24):
        theta = 2 * math.pi * j / 24
        x, y = polar(cx, cy, max_r, theta)
        parts.append(line(cx, cy, x, y, stroke="#f59e0b", stroke_width="0.9", opacity="0.42"))
    for offset in (0.0, math.pi / 24):
        pts = []
        for j in range(241):
            theta = 2 * math.pi * j / 240
            r = max_r * (0.28 + 0.68 * j / 240)
            wobble = 1 + 0.04 * math.sin(12 * theta + offset)
            pts.append(polar(cx, cy, r * wobble, theta + offset))
        parts.append(polyline(pts, fill="none", stroke=spec.accent, stroke_width="2", opacity="0.75", filter="url(#soft-glow)"))
    parts.append(circle(cx, cy, 4, fill="#fff7cc", opacity="0.9"))
    return panel_frame(spec, width, height, "\n    ".join(parts))


def render_tunnel(spec: RenderSpec, width: int, height: int) -> str:
    cx, cy = width / 2, height / 2 - 4
    max_r = min(width, height) * 0.42
    parts: list[str] = []
    for i in range(15):
        t = i / 14
        r = max_r * (t**1.75)
        opacity = 0.18 + 0.62 * t
        stroke_width = 0.8 + 2.2 * t
        parts.append(circle(cx, cy, r + 5, fill="none", stroke=spec.accent, stroke_width=fmt(stroke_width), opacity=fmt(opacity), filter="url(#soft-glow)"))
    for j in range(32):
        theta = 2 * math.pi * j / 32
        x0, y0 = polar(cx, cy, 8, theta)
        x1, y1 = polar(cx, cy, max_r + 8, theta)
        parts.append(line(x0, y0, x1, y1, stroke="#93c5fd", stroke_width="0.7", opacity="0.24"))
    parts.append(circle(cx, cy, 10, fill="#dbeafe", opacity="0.85"))
    return panel_frame(spec, width, height, "\n    ".join(parts))


def render_spiral(spec: RenderSpec, width: int, height: int) -> str:
    cx, cy = width / 2, height / 2 - 2
    max_r = min(width, height) * 0.42
    parts: list[str] = []
    for arm in range(6):
        pts = []
        phase = arm * 2 * math.pi / 6
        for i in range(520):
            theta = 0.03 * i
            # Lean shape: r = exp(alpha - beta theta), rescaled into panel space.
            r = 5.0 * math.exp(0.115 * theta)
            if r > max_r:
                break
            pts.append(polar(cx, cy, r, theta + phase))
        parts.append(polyline(pts, fill="none", stroke=spec.accent, stroke_width="2.1", opacity="0.78", filter="url(#soft-glow)"))
    for arm in range(6):
        pts = []
        phase = arm * 2 * math.pi / 6 + math.pi / 6
        for i in range(520):
            theta = 0.03 * i
            r = 6.5 * math.exp(0.105 * theta)
            if r > max_r:
                break
            pts.append(polar(cx, cy, r, -theta + phase))
        parts.append(polyline(pts, fill="none", stroke="#fbcfe8", stroke_width="0.9", opacity="0.35"))
    parts.append(circle(cx, cy, 5, fill="#fdf2f8", opacity="0.9"))
    return panel_frame(spec, width, height, "\n    ".join(parts))


def render_lattice(spec: RenderSpec, width: int, height: int) -> str:
    cx, cy = width / 2, height / 2 - 4
    spacing = 30
    radius = min(width, height) * 0.39
    parts: list[str] = []
    dy = spacing * math.sqrt(3) / 2
    rows = int((2 * radius) / dy) + 3
    cols = int((2 * radius) / spacing) + 3
    for row in range(-rows, rows + 1):
        y = cy + row * dy
        x_shift = (row % 2) * spacing / 2
        for col in range(-cols, cols + 1):
            x = cx + col * spacing + x_shift
            if (x - cx) ** 2 + (y - cy) ** 2 > radius**2:
                continue
            amp = 0.0
            for j in range(6):
                angle = j * math.pi / 3
                amp += math.cos(0.105 * (math.cos(angle) * (x - cx) + math.sin(angle) * (y - cy)))
            opacity = 0.18 + 0.12 * max(0.0, amp)
            parts.append(circle(x, y, 9.2, fill="none", stroke=spec.accent, stroke_width="1.3", opacity=fmt(min(opacity, 0.9))))
            if col % 2 == 0:
                parts.append(circle(x, y, 2.2, fill="#ccfbf1", opacity="0.75"))
    for j in range(6):
        angle = j * math.pi / 3
        x, y = polar(cx, cy, radius + 9, angle)
        parts.append(line(cx, cy, x, y, stroke="#99f6e4", stroke_width="1", opacity="0.22"))
    parts.append(circle(cx, cy, radius + 14, fill="none", stroke="#2dd4bf", stroke_width="1.1", opacity="0.34"))
    return panel_frame(spec, width, height, "\n    ".join(parts))


def render(spec: RenderSpec, width: int, height: int) -> str:
    if classify_geometry(spec.geometry) != spec.name:
        raise ValueError(f"spec {spec.name} does not match classifier")
    if spec.name == "cobweb":
        return render_cobweb(spec, width, height)
    if spec.name == "lattice":
        return render_lattice(spec, width, height)
    if spec.name == "tunnel":
        return render_tunnel(spec, width, height)
    if spec.name == "spiral":
        return render_spiral(spec, width, height)
    raise AssertionError(spec.name)


def render_contact_sheet(names: list[FormConstant], width: int, height: int) -> str:
    panel_w = width // 2
    panel_h = height // 2
    panels = []
    positions = [(0, 0), (panel_w, 0), (0, panel_h), (panel_w, panel_h)]
    for name, (x, y) in zip(names, positions):
        href = f"form_constant_{name}.svg"
        panels.append(
            f'<image href="{href}" x="{x}" y="{y}" width="{panel_w}" height="{panel_h}" preserveAspectRatio="xMidYMid meet"/>'
        )
    return f'''<svg xmlns="{SVG_NS}" width="{width}" height="{height}" viewBox="0 0 {width} {height}" role="img" aria-label="Kluver form constants contact sheet">
  <rect width="100%" height="100%" fill="#05070d"/>
  {"".join(panels)}
</svg>
'''


def write_manifest(out_dir: Path, files: list[Path], width: int, height: int) -> None:
    manifest = {
        "schema": "dashi.form_constants.renderer.v0_1",
        "renderer": "scripts/render_form_constants.py",
        "claim_boundary": "visualization-only; no qualia, V1/V2 recovery, fMRI validation, or brain-closure claim",
        "sources": [
            "DASHI/Klüver's Form Constants_aristotle/FormConstantGeometry.lean",
            "../dashi_agda/Ontology/Brain/BrainVisualFormConstantSurface.agda",
            "../dashi_agda/DASHI/Biology/RetinalPerturbationObservationBridge.agda",
        ],
        "classifier": {
            "openLoop=false, radialRing=0": "cobweb",
            "openLoop=false, radialRing>0": "lattice",
            "openLoop=true, radialRing=0": "tunnel",
            "openLoop=true, radialRing>0": "spiral",
        },
        "canvas": {"width": width, "height": height},
        "artifacts": [str(path) for path in files],
    }
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Render DASHI/Klüver form constants to SVG.")
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--width", type=int, default=720)
    parser.add_argument("--height", type=int, default=720)
    parser.add_argument(
        "--only",
        choices=sorted(SPECS),
        action="append",
        help="Render only this form constant; repeatable. Defaults to all four.",
    )
    parser.add_argument("--contact-sheet", action="store_true", help="Also render form_constants_contact_sheet.svg.")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    out_dir: Path = args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    names: list[FormConstant] = args.only or ["cobweb", "lattice", "tunnel", "spiral"]
    files: list[Path] = []
    for name in names:
        path = out_dir / f"form_constant_{name}.svg"
        path.write_text(render(SPECS[name], args.width, args.height), encoding="utf-8")
        files.append(path)
    if args.contact_sheet:
        path = out_dir / "form_constants_contact_sheet.svg"
        path.write_text(render_contact_sheet(["cobweb", "lattice", "tunnel", "spiral"], args.width * 2, args.height * 2), encoding="utf-8")
        files.append(path)
    write_manifest(out_dir, files, args.width, args.height)
    for path in files:
        print(path)
    print(out_dir / "manifest.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
