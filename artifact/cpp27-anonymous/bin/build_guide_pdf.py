#!/usr/bin/env python3
"""Render the artifact README as a compact reviewer-facing PDF."""

from __future__ import annotations

import argparse
from html import escape
from pathlib import Path
import re

from reportlab import rl_config
from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
from reportlab.lib.units import mm
from reportlab.pdfgen import canvas
from reportlab.platypus import Paragraph, Preformatted, SimpleDocTemplate, Spacer


rl_config.invariant = 1

INK = colors.HexColor("#1c252b")
MUTED = colors.HexColor("#56656f")
BLUE = colors.HexColor("#08627c")
LINE = colors.HexColor("#d5dce1")
SOFT = colors.HexColor("#f4f7f8")


def pdf_link(path: str) -> str:
    if path.startswith(("http://", "https://")):
        return path
    if path.startswith("docs/"):
        return path.removeprefix("docs/")
    return f"../{path}"


def inline_markup(text: str) -> str:
    pieces: list[str] = []
    position = 0
    pattern = re.compile(r"(`[^`]+`|\[[^\]]+\]\([^)]+\))")
    for match in pattern.finditer(text):
        pieces.append(escape(text[position : match.start()]))
        token = match.group(0)
        if token.startswith("`"):
            pieces.append(
                f'<font name="Courier" color="#263238">{escape(token[1:-1])}</font>'
            )
        else:
            label, target = re.fullmatch(r"\[([^\]]+)\]\(([^)]+)\)", token).groups()
            if label.startswith("`") and label.endswith("`"):
                label_markup = (
                    f'<font name="Courier">{escape(label[1:-1])}</font>'
                )
            else:
                label_markup = escape(label)
            pieces.append(
                f'<link href="{escape(pdf_link(target), quote=True)}" '
                f'color="#08627c"><u>{label_markup}</u></link>'
            )
        position = match.end()
    pieces.append(escape(text[position:]))
    return "".join(pieces)


def styles():
    sheet = getSampleStyleSheet()
    sheet.add(
        ParagraphStyle(
            name="ArtifactTitle",
            parent=sheet["Title"],
            fontName="Helvetica-Bold",
            fontSize=19.5,
            leading=23,
            alignment=TA_CENTER,
            textColor=INK,
            spaceAfter=10,
        )
    )
    sheet.add(
        ParagraphStyle(
            name="ArtifactHeading",
            parent=sheet["Heading2"],
            fontName="Helvetica-Bold",
            fontSize=12.2,
            leading=15,
            textColor=INK,
            spaceBefore=11,
            spaceAfter=5,
            keepWithNext=True,
        )
    )
    sheet.add(
        ParagraphStyle(
            name="ArtifactBody",
            parent=sheet["BodyText"],
            fontName="Helvetica",
            fontSize=9.4,
            leading=13.2,
            textColor=INK,
            spaceAfter=5.5,
        )
    )
    sheet.add(
        ParagraphStyle(
            name="ArtifactBullet",
            parent=sheet["BodyText"],
            fontName="Helvetica",
            fontSize=9.4,
            leading=13.2,
            leftIndent=16,
            firstLineIndent=-8,
            bulletIndent=4,
            textColor=INK,
            spaceAfter=3,
        )
    )
    sheet.add(
        ParagraphStyle(
            name="ArtifactCode",
            parent=sheet["Code"],
            fontName="Courier",
            fontSize=8.2,
            leading=10.7,
            leftIndent=9,
            rightIndent=9,
            borderColor=LINE,
            borderWidth=0.7,
            borderPadding=7,
            backColor=SOFT,
            spaceBefore=3,
            spaceAfter=7,
        )
    )
    return sheet


def markdown_story(path: Path):
    sheet = styles()
    lines = path.read_text(encoding="utf-8").splitlines()
    story = []
    paragraph: list[str] = []
    code: list[str] = []
    in_code = False

    def flush_paragraph() -> None:
        if paragraph:
            story.append(
                Paragraph(
                    inline_markup(" ".join(part.strip() for part in paragraph)),
                    sheet["ArtifactBody"],
                )
            )
            paragraph.clear()

    for line in lines:
        if line.startswith("```"):
            if in_code:
                story.append(Preformatted("\n".join(code), sheet["ArtifactCode"]))
                code.clear()
                in_code = False
            else:
                flush_paragraph()
                in_code = True
            continue
        if in_code:
            code.append(line)
            continue
        if line.startswith("# "):
            flush_paragraph()
            story.append(Paragraph(inline_markup(line[2:]), sheet["ArtifactTitle"]))
            story.append(Spacer(1, 1 * mm))
        elif line.startswith("## "):
            flush_paragraph()
            story.append(Paragraph(inline_markup(line[3:]), sheet["ArtifactHeading"]))
        elif line.startswith("- "):
            flush_paragraph()
            story.append(
                Paragraph(inline_markup(line[2:]), sheet["ArtifactBullet"], bulletText="-")
            )
        elif not line.strip():
            flush_paragraph()
        else:
            paragraph.append(line)
    flush_paragraph()
    return story


class ArtifactCanvas(canvas.Canvas):
    def __init__(self, *args, **kwargs):
        kwargs["invariant"] = 1
        super().__init__(*args, **kwargs)
        self.setAuthor("Anonymous")
        self.setCreator("PolCert artifact documentation")
        self.setTitle("PolCert Supplementary Artifact")
        self.setSubject("Compiler, proof, evaluation, and reproduction guide")


def page_footer(page_canvas, document) -> None:
    width, height = A4
    page_canvas.saveState()
    page_canvas.setFillColor(MUTED)
    page_canvas.setFont("Helvetica", 8.2)
    page_canvas.drawRightString(width - 18 * mm, 11 * mm, f"Page {document.page}")
    page_canvas.restoreState()


def later_page_decoration(page_canvas, document) -> None:
    width, height = A4
    page_canvas.saveState()
    page_canvas.setStrokeColor(LINE)
    page_canvas.setLineWidth(0.5)
    page_canvas.line(18 * mm, height - 15 * mm, width - 18 * mm, height - 15 * mm)
    page_canvas.setFillColor(MUTED)
    page_canvas.setFont("Helvetica", 8.2)
    page_canvas.drawString(18 * mm, height - 11.5 * mm, "PolCert Supplementary Artifact")
    page_canvas.restoreState()
    page_footer(page_canvas, document)


def build(source: Path, destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    document = SimpleDocTemplate(
        str(destination),
        pagesize=A4,
        leftMargin=21 * mm,
        rightMargin=21 * mm,
        topMargin=19 * mm,
        bottomMargin=16 * mm,
        title="PolCert Supplementary Artifact",
        author="Anonymous",
        subject="Compiler, proof, evaluation, and reproduction guide",
        creator="PolCert artifact documentation",
    )
    document.build(
        markdown_story(source),
        onFirstPage=page_footer,
        onLaterPages=later_page_decoration,
        canvasmaker=ArtifactCanvas,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    build(args.source.resolve(), args.destination.resolve())
    print(args.destination)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
