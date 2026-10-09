/-
  TRIMMED shim of `Lc/LiCriterion/Basic.lean` from
  https://github.com/nicholasbulka/li-criterion-rh-equivalence-lean at commit
  35df682f3b709ffe5fbcfdd452dfa964bd622b87 (Apache License 2.0, LICENSE in that repository).

  The Arda dbn island imports that 5,159-line module (plus its Hadamard / genus-one closure, about
  23k lines) but uses exactly three of its declarations: `LiCriterion.NontrivialZero`,
  `LiCriterion.riemannXi` and `LiCriterion.xi_zeros_are_nontrivial_zeros`.  This file keeps the
  module name, so every DBN module ports byte-identically, and copies those three declarations
  VERBATIM (upstream lines 100-101, 1236-1237, 1559-1564), with the same `open` lines and the
  same namespace.  The third is proved, as upstream, from `Lc/XiZeros.lean`, which is copied
  unmodified.  Nothing else from upstream is included.  Modification notice (Apache-2.0 sec. 4b):
  all other content of the upstream file was removed.
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Lc.XiZeros

open Complex Real Set Function Filter
open scoped Topology ComplexConjugate

namespace LiCriterion

-- Nontrivial zeros in the critical strip.
--
-- NOTE: this is placed near the top so it can be used by early analytic/M-test lemmas.
noncomputable def NontrivialZero : Type :=
  {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- The Riemann xi function in an entire form: ξ(s) = 1 / 2 · s(s-1) · Λ₀(s) + 1 / 2. -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + (1 / 2 : ℂ)

theorem xi_zeros_are_nontrivial_zeros :
  ∀ s : ℂ, riemannXi s = 0 ↔ ∃ ρ : NontrivialZero, s = ρ.val := by
  intro s
  simpa [LiCriterion.riemannXi, XiZeros.riemannXi,
    LiCriterion.NontrivialZero, XiZeros.NontrivialZero] using
    (XiZeros.xi_zeros_are_nontrivial_zeros (s := s))

end LiCriterion
