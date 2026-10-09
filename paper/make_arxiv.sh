#!/bin/bash
# Build paper/paper.pdf twice with pdflatex, then an arXiv source tarball (inline bibliography, no .bbl).
set -euo pipefail
cd "$(dirname "$0")"
pdflatex -interaction=nonstopmode paper.tex >/dev/null && pdflatex -interaction=nonstopmode paper.tex > build.log
grep -E "^!|Output written|LaTeX Warning: (Reference|Citation)" build.log || true
rm -rf arxiv && mkdir -p arxiv && cp paper.tex arxiv/
grep -q '^\\pdfoutput=1' arxiv/paper.tex || sed -i.bak '1s/^/\\pdfoutput=1\n/' arxiv/paper.tex && rm -f arxiv/paper.tex.bak
tar -czf arxiv.tar.gz -C arxiv . && rm -rf arxiv
echo "wrote paper/paper.pdf and paper/arxiv.tar.gz"
