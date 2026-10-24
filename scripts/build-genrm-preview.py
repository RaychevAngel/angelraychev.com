#!/usr/bin/env python3
"""Build the 1200x630 research-link preview using vectors and Poppler.

No inference, network access, fabricated chart data or image synthesis is used.
Requires ReportLab and Poppler's pdftoppm on PATH. Intermediate PDF output is
kept outside public/; only the final RGB PNG is intended for website serving.
"""

from __future__ import annotations

import argparse
import shutil
import subprocess
import tempfile
from pathlib import Path

from reportlab.lib.colors import HexColor
from reportlab.pdfbase.pdfmetrics import stringWidth
from reportlab.pdfgen import canvas


WIDTH, HEIGHT = 1200, 630
INK = "#121212"
MUTED = "#555555"
RULE = "#D8D8D8"
FILL = "#FAFAFA"


def text(c, x, y, value, size, *, bold=False, color=INK, align="left"):
    font = "Helvetica-Bold" if bold else "Helvetica"
    measured = stringWidth(value, font, size)
    left = x - measured / 2 if align == "center" else x
    if left < 0 or left + measured > WIDTH:
        raise ValueError(f"Text exceeds image width: {value}")
    c.setFillColor(HexColor(color))
    c.setFont(font, size)
    (c.drawCentredString if align == "center" else c.drawString)(x, y, value)


def arrow(c, start, end, color=INK, width=2):
    x0, y0 = start
    x1, y1 = end
    c.setStrokeColor(HexColor(color))
    c.setFillColor(HexColor(color))
    c.setLineWidth(width)
    c.line(x0, y0, x1, y1)
    if y0 == y1:
        direction = 1 if x1 > x0 else -1
        points = [(x1, y1), (x1 - direction * 9, y1 + 4.5),
                  (x1 - direction * 9, y1 - 4.5)]
    elif x0 == x1:
        direction = 1 if y1 > y0 else -1
        points = [(x1, y1), (x1 - 4.5, y1 - direction * 9),
                  (x1 + 4.5, y1 - direction * 9)]
    else:
        raise ValueError("Only horizontal and vertical arrows are used")
    path = c.beginPath()
    path.moveTo(*points[0])
    for point in points[1:]:
        path.lineTo(*point)
    path.close()
    c.drawPath(path, stroke=0, fill=1)


def build(pdf_path):
    c = canvas.Canvas(str(pdf_path), pagesize=(WIDTH, HEIGHT), invariant=1,
                      pageCompression=1)
    c.setTitle("Scaling Laws for Generative Reward Models")
    c.setAuthor("Angel Raychev, Nathan Lile, Rafael Rafailov")
    c.setFillColor(HexColor("#FFFFFF"))
    c.rect(0, 0, WIDTH, HEIGHT, fill=1, stroke=0)

    text(c, 72, 576, "RESEARCH  /  LLM POST-TRAINING", 19, color=MUTED)
    text(c, 72, 507, "Scaling Laws for", 62, bold=True)
    text(c, 72, 438, "Generative Reward Models", 62, bold=True)
    text(c, 72, 393, "Angel Raychev  ·  Nathan Lile  ·  Rafael Rafailov", 25)
    text(c, 72, 355, "Custom distributed Online DPO with generative judges", 23,
         color=MUTED)

    c.setStrokeColor(HexColor(RULE))
    c.setLineWidth(1.2)
    c.line(72, 331, 1128, 331)

    boxes = [
        (72, 194, 286, 102, "Current policy", "Generate fresh response pairs"),
        (457, 194, 286, 102, "Generative judge", "Compare both response orders"),
        (842, 194, 286, 102, "Online DPO update", "Learn from chosen / rejected"),
    ]
    for x, y, width, height, title, detail in boxes:
        c.setStrokeColor(HexColor(RULE))
        c.setFillColor(HexColor(FILL))
        c.setLineWidth(1.4)
        c.rect(x, y, width, height, stroke=1, fill=1)
        text(c, x + width / 2, y + 61, title, 24, bold=True, align="center")
        text(c, x + width / 2, y + 30, detail, 18, color=MUTED, align="center")

    arrow(c, (377, 245), (438, 245))
    arrow(c, (762, 245), (823, 245))
    c.setStrokeColor(HexColor(MUTED))
    c.setLineWidth(1.8)
    c.line(985, 194, 985, 155)
    c.line(985, 155, 215, 155)
    arrow(c, (215, 155), (215, 192), color=MUTED, width=1.8)
    text(c, 600, 125, "Refresh policy weights", 18, color=MUTED, align="center")

    text(c, 72, 72, "Static accuracy need not identify the best online rewarder.",
         28, bold=True)
    text(c, 72, 39, "Creative-writing policy quality assessed by a fixed, learned 32B Gold judge.",
         19, color=MUTED)
    c.save()


def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=root / "public/assets/genrm/research-preview.png")
    parser.add_argument("--intermediate-dir", type=Path,
                        help="Optionally retain the intermediate vector PDF here")
    args = parser.parse_args()
    renderer = shutil.which("pdftoppm")
    if not renderer:
        raise SystemExit("Poppler pdftoppm is required on PATH")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    def render(intermediate):
        intermediate.mkdir(parents=True, exist_ok=True)
        pdf_path = intermediate / "research-preview.pdf"
        build(pdf_path)
        stem = args.output.with_suffix("")
        subprocess.run([renderer, "-singlefile", "-r", "72", "-png", str(pdf_path),
                        str(stem)], check=True)

    if args.intermediate_dir:
        render(args.intermediate_dir)
    else:
        with tempfile.TemporaryDirectory(prefix="genrm-research-preview-") as directory:
            render(Path(directory))
    print(f"Created {args.output} ({WIDTH}x{HEIGHT})")


if __name__ == "__main__":
    main()
