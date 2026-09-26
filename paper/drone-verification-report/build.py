from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent
with (root / "evidence" / "tex-build.log").open("w") as log:
    for name in ("example", "flat", "plateau", "hill", "ridges"):
        subprocess.run(
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", f"{name}.tex"],
            cwd=root / "figures", stdout=log, stderr=subprocess.STDOUT, check=True,
        )
    for command in (
        ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
        ["bibtex", "main"],
        ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
        ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
    ):
        subprocess.run(command, cwd=root, stdout=log, stderr=subprocess.STDOUT, check=True)
print(root / "main.pdf")
