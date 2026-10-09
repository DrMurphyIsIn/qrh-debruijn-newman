# arXiv submission sheet

Everything the arXiv form asks for, ready to paste. The source package is `paper/arxiv.tar.gz`
(one file, `paper.tex`, with `\pdfoutput=1` on line 1 and an inline bibliography; no figures, no
.bbl). It was test-compiled from a clean directory with two passes of pdflatex (TeX Live 2025):
17 pages, no errors, no undefined references.

## Upload

- **File:** `paper/arxiv.tar.gz` (rebuild with `paper/make_arxiv.sh`).
- **Processing:** pdflatex (arXiv autodetects from `\pdfoutput=1`).

## Metadata

- **Title:** A kernel-checked bound Lambda <= 9/32 for the de Bruijn-Newman constant from OpenAI's quasi-Riemann hypothesis
  (TeX form: `A kernel-checked bound $\Lambda \le 9/32$ for the de Bruijn--Newman constant from OpenAI's quasi-Riemann hypothesis`)
- **Authors:** Peter W. Murphy
- **Primary category:** math.NT (Number Theory)
- **Cross-list:** cs.LO (Logic in Computer Science)
- **MSC classes:** 11M26 (primary); 03B35, 11Y35 (secondary)
- **ACM classes:** F.4.1
- **Comments:** 17 pages. Lean 4 sources, verification scripts, audit records and Comparator transcripts at
  https://github.com/DrMurphyIsIn/qrh-debruijn-newman (v1.0.0), archived at Zenodo, doi:10.5281/zenodo.23269135
  (concept doi:10.5281/zenodo.23269134). The zero-free half-plane Re s > 7/8 is OpenAI's theorem (openai/math,
  commit adc7f124, Apache-2.0); this paper composes it with de Bruijn's theorem and verifies the composition.
  Not a proof of the Riemann Hypothesis.
- **License:** CC BY 4.0 (matches `paper/`'s licence in `LICENSING.md`).
- **Report number / journal ref / DOI fields:** leave blank (the Zenodo DOI is the dataset, not the paper).

## Abstract (plain text with light TeX, as arXiv renders it)

In October 2026 OpenAI released a Lean 4 proof that the Riemann zeta function has no zero with real part greater than 7/8. We compose that theorem with de Bruijn's 1950 heat-flow theorem, as formalized on the Arda project's dbn island, inside a single Lean environment pinned to OpenAI's toolchain and Mathlib revision. The result is the theorem: for every real $t \ge 9/32$ and every complex $z$, if $H_t(z) = 0$ then $z$ is real. This is the classical statement $\Lambda \le 9/32$ for the de Bruijn-Newman constant, and its proof term depends only on propext, Classical.choice and Quot.sound. It is the first bound on $\Lambda$ below de Bruijn's $1/2$ that is checked by a proof kernel end to end. It was re-checked by a second kernel (nanoda) through openai/ten-proofs Comparator against a challenge that imports only Mathlib, with a tampered challenge rejected; independently audited by a second session from a fresh checkout; and judged in continuous integration against a registered statement before it was granted. We also document the obstacle that had to be removed first: the two theorems were born under Mathlib revisions six weeks apart, and although the statement "riemannZeta s $\ne$ 0" is syntactically identical at both revisions, 267 definitions in its meaning closure differ. Composing across that seam would have been a mathematical identification rather than a kernel check; porting the de Bruijn machinery to OpenAI's revision (seventeen of nineteen modules byte-identical, two one-line proof repairs) removed the seam. The bound is weaker than the numerical bounds $\Lambda \le 0.22$ (Polymath15) and $\Lambda \le 0.2$ (Platt-Trudgian), and it is not the Riemann Hypothesis, which is $\Lambda = 0$. The mathematics is a one-line composition of two known theorems; the contribution is the verification, and this paper is its record.

## After the identifier is assigned

1. Add `arXiv:XXXX.XXXXX` to `README.md` (paper section), `CITATION.cff` (an `identifiers` entry of type
   `other` with value `arXiv:XXXX.XXXXX`), `.zenodo.json` (`related_identifiers`: `arxiv:XXXX.XXXXX`,
   relation `isSupplementTo`), and the `\date` line of `paper/paper.tex`.
2. Rebuild (`paper/make_arxiv.sh`), commit, tag `v1.0.1`, and publish a new Zenodo version by the recorded
   procedure (new version on deposition 23269135, replace the two files, PUT metadata with the
   `related_identifiers` written explicitly, publish).
