# Design: paper and public release of the Lambda <= 9/32 bound (approved 2026-10-09)

Decisions (operator): new public repo DrMurphyIsIn/qrh-debruijn-newman; Peter W. Murphy sole author, OpenAI credited
by their BibTeX, commit and licence, AI assistance acknowledged; full paper 15-25 pages; Zenodo via the BG procedure
(one-time token supplied by the operator, deleted after use).

Framing: the mathematics is a one-line composition (OpenAI's 7/8 half-plane into de Bruijn's theorem); the contribution
is verification: first bound below 1/2 kernel-checked end to end, second kernel, independent audit, registry judge, the
cross-pin seam analysed and then removed by a single-pin port. Weaker than 0.22; not RH; conjecture1_proved = False.

Repository: paper/ (tex, pdf, make_arxiv.sh), lean/ (bridge, dbn port, Lc shim, patches, fidelity, judge bundle, OAI_PIN),
scripts/materialize.sh (self-contained), logs/, docs/ (design, audit, review, this spec), provenance/ (registry records,
Arda source commit, Arda CI workflow), .github/workflows/verify.yml, README/LICENSING/NOTICE/CITATION/.zenodo.json.

Paper outline: 1 Introduction (Lambda, the ladder 1/2 -> 0.2, where 9/32 sits); 2 The two theorems (statements as
formalized); 3 The composition (sInf-free form, H_0 = xi/8, strip, heat flow); 4 The seam and the single-pin port
(fidelity analysis, 27 root causes, two patches); 5 Verification (Comparator, nanoda, negative control, audit, CI,
registry chain; trust table); 6 What it does and does not advance (lossy conversion, 0.83 threshold); appendices
(statements, reproduction, logs). Inline bibliography; pdflatex; BG preamble.

Release: build PDF, tag v1.0.0, Zenodo deposit (software), write DOI back into README/CITATION/paper, Arda follow-up PR.
