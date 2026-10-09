# Licensing

- **Lean sources, scripts and data** (`lean/`, `scripts/`, `logs/`, `provenance/`): [Apache License 2.0](LICENSE).
  The nineteen `lean/dbn/*.lean` modules and `lean/bridge/*.lean` come from the Arda repository's research
  islands, which Arda licenses under Apache-2.0 (see `provenance/ARDA_SOURCE`). `lean/Lc/` is a trimmed copy of
  LiCriterion (Apache-2.0; `lean/Lc/NOTICE`).
- **The paper and the prose documents** (`paper/`, `docs/`, `README.md`): [CC-BY-4.0](https://creativecommons.org/licenses/by/4.0/).
- **OpenAI's theorem.** The proof of `riemannZeta s ≠ 0` for `Re s > 7/8` is OpenAI's, from
  <https://github.com/openai/math> at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, licensed under Apache-2.0.
  No OpenAI file is vendored here; `scripts/materialize.sh` checks their `lean/` directory out unmodified and
  builds this repository's files inside it. `lean/bridge/ArdaQRHBridge.lean` adds one line to their theorem.
- **Lean 4 and Mathlib** are Apache-2.0. No part of the Telperion engine is vendored here.
