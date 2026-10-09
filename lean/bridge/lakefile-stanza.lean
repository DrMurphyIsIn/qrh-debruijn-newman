
-- ===== Arda oai_qrh_bridge (appended by telperion/examples/oai_qrh_bridge/materialize.sh) =====
lean_lib ArdaQRHBridge where
  roots := #[`ArdaQRHBridge]
lean_lib AxiomGuardQRHBridge where
  roots := #[`AxiomGuardQRHBridge]
-- Single-pin port of the dbn island closure of `dbn_real_zeros_of_qrh` (19 modules, copied
-- byte-identically from telperion/examples/dbn/lean, then dbn_port/patches applied).  The dbn
-- island builds with Lean's default `autoImplicit := true`; OpenAI's package sets it false, so
-- the port restores the island default.
lean_lib ArdaDBNPort where
  roots := #[`DBNZeroFreeHalfplane, `DBNRealZerosIffFinal, `DBNRealZerosIff, `DBNDefs, `DBNXi,
    `DBNXiIBP, `DBNGKernel, `DBNXiCos, `DBNXiRiemann, `DBNM1Parametric, `DBNM1Approx,
    `DBNHadamard, `DBNHadamardLinear, `DBNHadamardMean, `DBNHadamardProduct,
    `DBNHadamardCount, `DBNStep, `DBNHeatApprox, `DBNHurwitz]
  leanOptions := #[⟨`autoImplicit, true⟩]
-- The two LiCriterion modules the closure needs (Lc/XiZeros.lean verbatim, Lc/LiCriterion/Basic.lean
-- trimmed to three verbatim declarations), with the LiCriterion package's own options.
lean_lib ArdaLiCriterionShim where
  roots := #[`Lc.XiZeros, `Lc.LiCriterion.Basic]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`maxSynthPendingDepth, .ofNat 3⟩]
lean_lib ArdaDBNUnconditional where
  roots := #[`ArdaDBNUnconditional, `AxiomGuardDBNUnconditional]
lean_lib ArdaDBNChallenge where
  roots := #[`ArdaDBNChallenge]
-- Negative control: the challenge with Φ altered (e^{9u} -> e^{8u}); Comparator must reject it.
lean_lib ArdaDBNNegativeControl where
  roots := #[`ArdaDBNChallengeTampered]
