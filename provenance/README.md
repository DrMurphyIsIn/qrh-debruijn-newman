# Provenance records

Copied verbatim from the Arda repository at the commit in `ARDA_SOURCE`.

- `registry/*.toml`: the four missions-registry node records. Each carries `[author]` (the registering
  session), `[readback]` (the operator's independent read-back, 2026-10-09), `[grant]` (the verify-gate grant with
  artifact and statement digests) and `[comparator]` (the CI judge pass: run 37955041118, verdict read from the
  job log, artifact hashed at the judged commit, nanoda as second kernel).
- `registry/*.statement.lean`: the registered statements, which the judge used verbatim as the TYPE of each
  challenge (`lean/judge/MissionChallenges/`).
- `arda-oai-qrh-bridge.yml`: the Arda CI workflow that builds the island, re-elaborates the artifacts, checks the
  axiom guards and runs the three Comparator configs on every push (first green run 37728388605).
- The audit (`docs/QRH_DBN_AUDIT_2026-10-07_e9.md`) and the judge review (`docs/JUDGE_OAI_BRIDGE_REVIEW_2026-10-08_e9.md`)
  are the independent session's records; the design document (`docs/QRH_DBN_BRIDGE_2026-10-07.md`) is the author
  session's, with its final status section.
