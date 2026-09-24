# -*- coding: utf-8 -*-
"""A very small SVG writer, shared by the poster generators in `docs/`."""

FONT = "DejaVu Sans, Segoe UI, Helvetica, Arial, sans-serif"
MONO = "DejaVu Sans Mono, Consolas, monospace"

# rough advance widths, as a fraction of the font size
_W_SANS = 0.55
_W_MONO = 0.60


def esc(s):
    return (s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
             .replace('"', "&quot;"))


def width_of(s, size, family=FONT):
    f = _W_MONO if family == MONO else _W_SANS
    return f * size * len(s)


def wrap_lines(s, size, width, family=FONT, max_lines=None):
    """Greedy word wrap of `s` to a pixel `width`; the lines, without drawing them."""
    words, line, out = s.split(), "", []
    for wd in words:
        trial = (line + " " + wd).strip()
        if width_of(trial, size, family) > width and line:
            out.append(line)
            line = wd
        else:
            line = trial
    if line:
        out.append(line)
    return out[:max_lines] if max_lines else out


class Canvas:
    def __init__(self, width, background="#f1f5f9", title="", defs=""):
        self.w = width
        self.bg = background
        self.title = title
        self.defs = defs
        self.parts = []

    # -- primitives ---------------------------------------------------------
    def add(self, s):
        self.parts.append(s)

    def text(self, x, y, s, size=16, fill="#0f172a", weight="normal",
             anchor="start", family=FONT, opacity=None):
        op = f' fill-opacity="{opacity}"' if opacity is not None else ""
        self.add(f'<text x="{x:.1f}" y="{y:.1f}" font-family="{family}" font-size="{size}" '
                 f'fill="{fill}" font-weight="{weight}" text-anchor="{anchor}"{op}>{esc(s)}</text>')

    def rect(self, x, y, w, h, fill, rx=10, stroke=None, stroke_width=1, opacity=None):
        st = f' stroke="{stroke}" stroke-width="{stroke_width}"' if stroke else ""
        op = f' fill-opacity="{opacity}"' if opacity is not None else ""
        self.add(f'<rect x="{x:.1f}" y="{y:.1f}" width="{w:.1f}" height="{h:.1f}" rx="{rx}" '
                 f'fill="{fill}"{st}{op}/>')

    def circle(self, cx, cy, r, fill, stroke=None, stroke_width=1):
        st = f' stroke="{stroke}" stroke-width="{stroke_width}"' if stroke else ""
        self.add(f'<circle cx="{cx:.1f}" cy="{cy:.1f}" r="{r:.1f}" fill="{fill}"{st}/>')

    def line(self, x1, y1, x2, y2, stroke="#94a3b8", width=2, dash=None, marker=None):
        d = f' stroke-dasharray="{dash}"' if dash else ""
        m = f' marker-end="url(#{marker})"' if marker else ""
        self.add(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
                 f'stroke="{stroke}" stroke-width="{width}"{d}{m}/>')

    def path(self, d, stroke="#94a3b8", width=2, fill="none", marker=None, dash=None):
        m = f' marker-end="url(#{marker})"' if marker else ""
        da = f' stroke-dasharray="{dash}"' if dash else ""
        self.add(f'<path d="{d}" fill="{fill}" stroke="{stroke}" stroke-width="{width}"{m}{da}/>')

    # -- composites ---------------------------------------------------------
    def chip(self, x, y, label, fill="#e0f2fe", stroke="#7dd3fc", colour="#075985",
             size=13, height=28, pad=16, family=FONT):
        w = 2 * pad + width_of(label, size, family)
        self.rect(x, y, w, height, fill, rx=height / 2, stroke=stroke)
        self.text(x + w / 2, y + height / 2 + size * 0.36, label, size, colour,
                  anchor="middle", family=family)
        return w

    def chip_row(self, x0, y, labels, right, gap=9, **kw):
        """Lay chips out left to right, wrapping at `right`.  Returns the y below."""
        x, yy = x0, y
        h = kw.get("height", 28)
        for lab in labels:
            w = 2 * kw.get("pad", 16) + width_of(lab, kw.get("size", 13),
                                                 kw.get("family", FONT))
            if x + w > right:
                x, yy = x0, yy + h + 8
            self.chip(x, yy, lab, **kw)
            x += w + gap
        return yy + h

    def wrap(self, x, y, s, size, width, fill="#475569", leading=None, family=FONT,
             weight="normal", max_lines=None):
        """Greedy word wrap to a pixel width.  Returns the y below the block."""
        leading = leading or size + 5
        out = wrap_lines(s, size, width, family=family, max_lines=max_lines)
        for i, ln in enumerate(out):
            self.text(x, y + i * leading, ln, size, fill, weight=weight, family=family)
        return y + len(out) * leading

    # -- output -------------------------------------------------------------
    def render(self, height):
        head = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{self.w}" height="{height}" '
                f'viewBox="0 0 {self.w} {height}" role="img" aria-label="{esc(self.title)}">',
                f'<title>{esc(self.title)}</title>',
                f'<defs>{self.defs}</defs>',
                f'<rect x="0" y="0" width="{self.w}" height="{height}" fill="{self.bg}"/>']
        return "\n".join(head + self.parts + ["</svg>"])

    def write(self, path, height):
        with open(path, "w", encoding="utf-8") as f:
            f.write(self.render(height))
        return height
