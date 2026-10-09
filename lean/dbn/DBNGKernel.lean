/-
  DBNGKernel -- module C of the C2 design memo
  (telperion/docs/DESIGN_RH_dbn_H0_eq_xi_2026-09-22.md: section 5 row C, section 2 steps (5)
  and (6), section 3.3 items N3 and N5, section 5 risk notes C and D).

  The kernel of Riemann's symmetric integral in the Polymath15 variable `u` (`x = e^{4u}`),
  with `θ_k(u) := thetaMoment k u` and `ψ(x) = ∑_{n ≥ 1} e^{−πn²x}`:

    g(u)   = e^{u} ψ(e^{4u}) = e^{u} (θ₀(u) − 1)/2,
    g'(u)  = e^{u} (θ₀(u) − 1)/2 − 2π e^{5u} θ₁(u),
    g''(u) = e^{u} (θ₀(u) − 1)/2 − 12π e^{5u} θ₁(u) + 8π² e^{9u} θ₂(u).

  The closed forms come from the island's termwise derivative `hasDerivAt_thetaMoment`; no
  `tsum` is ever interchanged with an integral in this file.

  What IS proved here (axiom-clean, see AxiomGuardDBN.lean):
    * N5: `θ₀(u) − 1 = 2 ∑_{n ≥ 1} e^{−πn²e^{4u}}` (the `k = 0` sibling of
      `thetaMoment_eq_two_mul_pnat`), hence `θ₀ ≥ 1` and `g ≥ 0`,
    * the shared decay helper `abs_thetaMoment_pnat_le` (risk note C):
      `∑_{n ≥ 1} (n²)^k e^{−πn²e^{4u}} ≤ C_k exp(−(π/2) e^{4u})` for `u ≥ 0`,
    * `hasDerivAt_g : HasDerivAt g (g' u) u` and `hasDerivAt_g' : HasDerivAt g' (g'' u) u`
      (plus the complex-valued `ofReal` versions and continuity),
    * the kernel identity `g''_sub_g_eq : g'' u − g u = 8 Φ(u)` (step (5)) and the boundary value
      `g'_zero : g' 0 = −1/2` (step (6), from the differentiated theta functional equation),
    * N3: decay bounds `abs_g_le`, `abs_g'_le`, `abs_g''_le` on `u ≥ 0`,
    * `tendsto_exp_quad_mul_exp_neg_exp` / `tendsto_exp_lin_mul_exp_neg_exp`: the `atTop` limit
      behind the island majorant `integrableOn_exp_quad_mul_exp_neg_exp` (risk note D),
    * integrability on `Ioi 0`, and vanishing at `atTop`, of `g`, `g'`, `g''` (cast to `ℂ`)
      times ANY continuous complex weight of at most exponential growth, both pointwise and in
      the `Pi.mul` shape `(fun u ↦ (g u : ℂ)) * w` that `integral_Ioi_mul_deriv_eq_deriv_mul`
      consumes, with the named instances against complex `cos (z u)` and `sin (z u)`,
    * every hypothesis of the two integrations by parts of module D (both `HasDerivAt`
      families, the four `IntegrableOn` side conditions, the four boundary limits at `0⁺` and
      `+∞`), stated for arbitrary complex `z`,
    * `integral_g''_sub_g_mul_cos : ∫_0^∞ (g'' − g)(u) cos(zu) du = 8 H_0(z)`.

  What is NOT proved here: Riemann's integral for `Λ₀` (module A), the change of variables to
  `∫ g cos` (module B), the integration-by-parts identity itself (module D), or the
  representation theorem `H_0 = ξ/8` (registry node RH.dbn_H0_eq_xi, module E).  Every
  declaration below is a complete proof; the island CI word-scan and the axiom guard check this.

  SCOPE.  The C2 representation theorem is an identity between two entire functions; it is not
  RH-equivalent, and nothing in this file says anything about where the zeros of `H_t` lie.
  Nothing here proves RH.  conjecture1_proved = False.
-/
import DBNDefs

open Real MeasureTheory Set Filter Topology

namespace DBN

/-! ### The zeroth theta moment over `ℕ+` (memo item N5) -/

/-- `θ₀(u) − 1 = 2 ∑_{n ≥ 1} exp(−πn² e^{4u})`: the `k = 0` sibling of
`thetaMoment_eq_two_mul_pnat` (the `n = 0` term of the `ℤ`-sum is `1`, not `0`). -/
theorem thetaMoment_zero_sub_one_eq_two_mul_pnat (u : ℝ) :
    thetaMoment 0 u - 1 = 2 * ∑' n : ℕ+, Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u)) := by
  unfold thetaMoment
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat
    (f := fun n : ℤ ↦ ((n : ℝ) ^ 2) ^ 0 * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u)))
    (fun n ↦ by simp) (summable_thetaMoment 0 u)]
  simp

/-- The theta moments are nonnegative. -/
theorem thetaMoment_nonneg (k : ℕ) (u : ℝ) : 0 ≤ thetaMoment k u :=
  tsum_nonneg fun n ↦ by positivity

/-- `θ₀(u) ≥ 1`. -/
theorem one_le_thetaMoment_zero (u : ℝ) : 1 ≤ thetaMoment 0 u := by
  have h := thetaMoment_zero_sub_one_eq_two_mul_pnat u
  have : 0 ≤ ∑' n : ℕ+, Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u)) :=
    tsum_nonneg fun n ↦ (Real.exp_pos _).le
  linarith

/-! ### Decay of the `ℕ+` theta moments (the shared helper) -/

/-- The constant `C_k = ∑_{n ≥ 1} (n²)^k exp(−πn²/2)` of the theta-moment decay bound. -/
noncomputable def thetaPnatConst (k : ℕ) : ℝ :=
  ∑' n : ℕ+, ((n : ℝ) ^ 2) ^ k * Real.exp (-π * (n : ℝ) ^ 2 * (1 / 2))

theorem thetaPnatConst_nonneg (k : ℕ) : 0 ≤ thetaPnatConst k :=
  tsum_nonneg fun n ↦ by positivity

/-- **Decay of the `ℕ+` theta moments** (memo section 5, risk note C): for `u ≥ 0`,
`|∑_{n ≥ 1} (n²)^k exp(−πn² e^{4u})| ≤ C_k · exp(−(π/2) e^{4u})`. -/
theorem abs_thetaMoment_pnat_le (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |∑' n : ℕ+, ((n : ℝ) ^ 2) ^ k * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u))|
      ≤ thetaPnatConst k * Real.exp (-(π / 2) * Real.exp (4 * u)) := by
  have hs := summable_thetaTerm_pnat k (Real.exp_pos (4 * u))
  have hnn : 0 ≤ ∑' n : ℕ+, ((n : ℝ) ^ 2) ^ k * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u)) :=
    tsum_nonneg fun n ↦ by positivity
  rw [abs_of_nonneg hnn]
  have he : (1 : ℝ) ≤ Real.exp (4 * u) := Real.one_le_exp (by linarith)
  calc ∑' n : ℕ+, ((n : ℝ) ^ 2) ^ k * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u))
      ≤ ∑' n : ℕ+, Real.exp (-(π / 2) * Real.exp (4 * u)) *
          (((n : ℝ) ^ 2) ^ k * Real.exp (-π * (n : ℝ) ^ 2 * (1 / 2))) := by
        refine hs.tsum_le_tsum (fun n ↦ ?_)
          ((summable_thetaTerm_pnat k (by norm_num : (0 : ℝ) < 1 / 2)).mul_left _)
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr n.pos
        have hn : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
        have hexp : Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u))
            ≤ Real.exp (-(π / 2) * Real.exp (4 * u)) * Real.exp (-π * (n : ℝ) ^ 2 * (1 / 2)) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          nlinarith [Real.pi_pos, mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr he)]
        calc ((n : ℝ) ^ 2) ^ k * Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u))
            ≤ ((n : ℝ) ^ 2) ^ k * (Real.exp (-(π / 2) * Real.exp (4 * u))
                * Real.exp (-π * (n : ℝ) ^ 2 * (1 / 2))) := by gcongr
          _ = _ := by ring
    _ = Real.exp (-(π / 2) * Real.exp (4 * u)) * thetaPnatConst k := tsum_mul_left
    _ = thetaPnatConst k * Real.exp (-(π / 2) * Real.exp (4 * u)) := mul_comm _ _

/-- For `k ≥ 1` and `u ≥ 0`: `θ_k(u) ≤ 2 C_k exp(−(π/2) e^{4u})`. -/
theorem thetaMoment_le_decay (k : ℕ) (hk : 0 < k) {u : ℝ} (hu : 0 ≤ u) :
    thetaMoment k u ≤ 2 * thetaPnatConst k * Real.exp (-(π / 2) * Real.exp (4 * u)) := by
  have h := abs_thetaMoment_pnat_le k hu
  rw [abs_of_nonneg (tsum_nonneg fun n ↦ by positivity)] at h
  rw [thetaMoment_eq_two_mul_pnat k hk u]
  linarith

/-- For `u ≥ 0`: `θ₀(u) − 1 ≤ 2 C₀ exp(−(π/2) e^{4u})`. -/
theorem thetaMoment_zero_sub_one_le_decay {u : ℝ} (hu : 0 ≤ u) :
    thetaMoment 0 u - 1 ≤ 2 * thetaPnatConst 0 * Real.exp (-(π / 2) * Real.exp (4 * u)) := by
  have h := abs_thetaMoment_pnat_le 0 hu
  simp only [pow_zero, one_mul] at h
  rw [abs_of_nonneg (tsum_nonneg fun n ↦ (Real.exp_pos _).le)] at h
  rw [thetaMoment_zero_sub_one_eq_two_mul_pnat u]
  linarith

/-! ### The kernel `g` and its first two derivatives -/

/-- The kernel `g(u) = e^{u} ψ(e^{4u}) = e^{u} (θ₀(u) − 1)/2` of Riemann's symmetric integral
(memo section 2; `ψ(x) = ∑_{n ≥ 1} e^{−πn²x}`).  The three kernel definitions spell `Real.pi`
(not the scoped `π`) so that the registry's `Statements.RHDefs` can mirror them verbatim. -/
noncomputable def g (u : ℝ) : ℝ := Real.exp u * (thetaMoment 0 u - 1) / 2

/-- Closed form of `g'`: `e^{u} (θ₀(u) − 1)/2 − 2π e^{5u} θ₁(u)` (see `hasDerivAt_g`). -/
noncomputable def g' (u : ℝ) : ℝ :=
  Real.exp u * (thetaMoment 0 u - 1) / 2 - 2 * Real.pi * Real.exp (5 * u) * thetaMoment 1 u

/-- Closed form of `g''`: `e^{u} (θ₀(u) − 1)/2 − 12π e^{5u} θ₁(u) + 8π² e^{9u} θ₂(u)`
(see `hasDerivAt_g'`). -/
noncomputable def g'' (u : ℝ) : ℝ :=
  Real.exp u * (thetaMoment 0 u - 1) / 2 - 12 * Real.pi * Real.exp (5 * u) * thetaMoment 1 u
    + 8 * Real.pi ^ 2 * Real.exp (9 * u) * thetaMoment 2 u

/-- `g` in terms of the `ℕ+` theta sum: `g(u) = e^{u} ∑_{n ≥ 1} exp(−πn² e^{4u})`. -/
theorem g_eq_exp_mul_tsum_pnat (u : ℝ) :
    g u = Real.exp u * ∑' n : ℕ+, Real.exp (-π * (n : ℝ) ^ 2 * Real.exp (4 * u)) := by
  unfold g
  rw [thetaMoment_zero_sub_one_eq_two_mul_pnat u]
  ring

theorem g_nonneg (u : ℝ) : 0 ≤ g u := by
  have := one_le_thetaMoment_zero u
  unfold g
  have := Real.exp_pos u
  positivity

/-- **`g' = dg/du`**, from the termwise derivative `hasDerivAt_thetaMoment`. -/
theorem hasDerivAt_g (u : ℝ) : HasDerivAt g (g' u) u := by
  have h0 : HasDerivAt (thetaMoment 0) (-4 * π * Real.exp (4 * u) * thetaMoment 1 u) u :=
    hasDerivAt_thetaMoment 0 u
  have h := ((Real.hasDerivAt_exp u).mul (h0.sub_const 1)).div_const 2
  have e5 : Real.exp u * Real.exp (4 * u) = Real.exp (5 * u) := by
    rw [← Real.exp_add]; ring_nf
  refine h.congr_deriv ?_
  unfold g'
  rw [← e5]
  ring

/-- **`g'' = dg'/du`**, from the termwise derivative `hasDerivAt_thetaMoment`. -/
theorem hasDerivAt_g' (u : ℝ) : HasDerivAt g' (g'' u) u := by
  have h0 : HasDerivAt (thetaMoment 0) (-4 * π * Real.exp (4 * u) * thetaMoment 1 u) u :=
    hasDerivAt_thetaMoment 0 u
  have h1 : HasDerivAt (thetaMoment 1) (-4 * π * Real.exp (4 * u) * thetaMoment 2 u) u :=
    hasDerivAt_thetaMoment 1 u
  have hexp5 : HasDerivAt (fun x : ℝ ↦ Real.exp (5 * x)) (Real.exp (5 * u) * 5) u := by
    have := ((hasDerivAt_id u).const_mul (5 : ℝ)).exp
    simpa using this
  have hA := ((Real.hasDerivAt_exp u).mul (h0.sub_const 1)).div_const 2
  have hB := (hexp5.const_mul (2 * π)).mul h1
  have h := hA.sub hB
  have e5 : Real.exp u * Real.exp (4 * u) = Real.exp (5 * u) := by
    rw [← Real.exp_add]; ring_nf
  have e9 : Real.exp (5 * u) * Real.exp (4 * u) = Real.exp (9 * u) := by
    rw [← Real.exp_add]; ring_nf
  refine h.congr_deriv ?_
  unfold g''
  rw [← e5, ← e9, ← e5]
  ring

theorem deriv_g : deriv g = g' := funext fun u ↦ (hasDerivAt_g u).deriv

theorem deriv_g' : deriv g' = g'' := funext fun u ↦ (hasDerivAt_g' u).deriv

@[fun_prop]
theorem continuous_g : Continuous g :=
  continuous_iff_continuousAt.mpr fun u ↦ (hasDerivAt_g u).continuousAt

@[fun_prop]
theorem continuous_g' : Continuous g' :=
  continuous_iff_continuousAt.mpr fun u ↦ (hasDerivAt_g' u).continuousAt

@[fun_prop]
theorem continuous_g'' : Continuous g'' := by
  show Continuous (fun u ↦ Real.exp u * (thetaMoment 0 u - 1) / 2
    - 12 * π * Real.exp (5 * u) * thetaMoment 1 u + 8 * π ^ 2 * Real.exp (9 * u) * thetaMoment 2 u)
  fun_prop

/-! ### The kernel identity `g'' − g = 8Φ` and the boundary value `g'(0) = −1/2` -/

/-- **The kernel identity** (memo section 2, step (5)): `g''(u) − g(u) = 8 Φ(u)`. -/
theorem g''_sub_g_eq (u : ℝ) : g'' u - g u = 8 * Φ u := by
  rw [Φ_eq]
  unfold g'' g
  ring

/-- **`g'(0) = −1/2`** (memo section 2, step (6)), from the first derivative of the theta
functional equation at `u = 0`, which reads `θ₁(0) = θ₀(0)/(4π)`. -/
theorem g'_zero : g' 0 = -1 / 2 := by
  have d1 := thetaMoment_fe_deriv1 0
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at d1
  unfold g'
  simp only [mul_zero, Real.exp_zero, one_mul, mul_one]
  linear_combination (1 / 4 : ℝ) * d1

/-! ### Decay bounds on `u ≥ 0` (memo item N3) -/

/-- The constant `C₀ + 24π C₁ + 16π² C₂` in the decay bounds for `g'` and `g''`. -/
noncomputable def gKernelConst : ℝ :=
  thetaPnatConst 0 + 24 * π * thetaPnatConst 1 + 16 * π ^ 2 * thetaPnatConst 2

theorem gKernelConst_nonneg : 0 ≤ gKernelConst := by
  have h0 := thetaPnatConst_nonneg 0
  have h1 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 24) Real.pi_pos.le)
    (thetaPnatConst_nonneg 1)
  have h2 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) (sq_nonneg π))
    (thetaPnatConst_nonneg 2)
  unfold gKernelConst
  linarith

/-- **Decay of `g`**: for `u ≥ 0`, `|g(u)| ≤ C₀ e^{u} exp(−(π/2) e^{4u})`. -/
theorem abs_g_le {u : ℝ} (hu : 0 ≤ u) :
    |g u| ≤ thetaPnatConst 0 * (Real.exp u * Real.exp (-(π / 2) * Real.exp (4 * u))) := by
  have h1 := thetaMoment_zero_sub_one_le_decay hu
  rw [abs_of_nonneg (g_nonneg u)]
  unfold g
  calc Real.exp u * (thetaMoment 0 u - 1) / 2
      ≤ Real.exp u * (2 * thetaPnatConst 0 * Real.exp (-(π / 2) * Real.exp (4 * u))) / 2 := by
        gcongr
    _ = thetaPnatConst 0 * (Real.exp u * Real.exp (-(π / 2) * Real.exp (4 * u))) := by ring

/-- **Decay of `g'`**: for `u ≥ 0`, `|g'(u)| ≤ gKernelConst · e^{5u} exp(−(π/2) e^{4u})`. -/
theorem abs_g'_le {u : ℝ} (hu : 0 ≤ u) :
    |g' u| ≤ gKernelConst * (Real.exp (5 * u) * Real.exp (-(π / 2) * Real.exp (4 * u))) := by
  set E := Real.exp (-(π / 2) * Real.exp (4 * u)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have h0 := thetaMoment_zero_sub_one_le_decay hu
  have h0n : 0 ≤ thetaMoment 0 u - 1 := by linarith [one_le_thetaMoment_zero u]
  have h1 := thetaMoment_le_decay 1 one_pos hu
  have h1n := thetaMoment_nonneg 1 u
  have hC0 := thetaPnatConst_nonneg 0
  have hC1 := thetaPnatConst_nonneg 1
  have hC2 := thetaPnatConst_nonneg 2
  have h15 : Real.exp u ≤ Real.exp (5 * u) := Real.exp_le_exp.mpr (by linarith)
  have hX : 0 ≤ Real.exp (5 * u) * E := by positivity
  have hA : Real.exp u * (thetaMoment 0 u - 1) / 2 ≤ thetaPnatConst 0 * (Real.exp (5 * u) * E) := by
    calc Real.exp u * (thetaMoment 0 u - 1) / 2 ≤ Real.exp u * (2 * thetaPnatConst 0 * E) / 2 := by
          gcongr
      _ = thetaPnatConst 0 * (Real.exp u * E) := by ring
      _ ≤ thetaPnatConst 0 * (Real.exp (5 * u) * E) := by gcongr
  have hB : 2 * π * Real.exp (5 * u) * thetaMoment 1 u
      ≤ 4 * π * thetaPnatConst 1 * (Real.exp (5 * u) * E) := by
    calc 2 * π * Real.exp (5 * u) * thetaMoment 1 u
        ≤ 2 * π * Real.exp (5 * u) * (2 * thetaPnatConst 1 * E) := by gcongr
      _ = 4 * π * thetaPnatConst 1 * (Real.exp (5 * u) * E) := by ring
  have hA0 : 0 ≤ Real.exp u * (thetaMoment 0 u - 1) / 2 := by positivity
  have hB0 : 0 ≤ 2 * π * Real.exp (5 * u) * thetaMoment 1 u := by positivity
  have hK : thetaPnatConst 0 + 4 * π * thetaPnatConst 1 ≤ gKernelConst := by
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20) Real.pi_pos.le) hC1
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) (sq_nonneg π)) hC2
    unfold gKernelConst
    linarith
  unfold g'
  calc |Real.exp u * (thetaMoment 0 u - 1) / 2 - 2 * π * Real.exp (5 * u) * thetaMoment 1 u|
      ≤ |Real.exp u * (thetaMoment 0 u - 1) / 2| + |2 * π * Real.exp (5 * u) * thetaMoment 1 u| :=
        abs_sub _ _
    _ = Real.exp u * (thetaMoment 0 u - 1) / 2 + 2 * π * Real.exp (5 * u) * thetaMoment 1 u := by
        rw [abs_of_nonneg hA0, abs_of_nonneg hB0]
    _ ≤ thetaPnatConst 0 * (Real.exp (5 * u) * E)
          + 4 * π * thetaPnatConst 1 * (Real.exp (5 * u) * E) := add_le_add hA hB
    _ = (thetaPnatConst 0 + 4 * π * thetaPnatConst 1) * (Real.exp (5 * u) * E) := by ring
    _ ≤ gKernelConst * (Real.exp (5 * u) * E) := mul_le_mul_of_nonneg_right hK hX

/-- **Decay of `g''`**: for `u ≥ 0`, `|g''(u)| ≤ gKernelConst · e^{9u} exp(−(π/2) e^{4u})`. -/
theorem abs_g''_le {u : ℝ} (hu : 0 ≤ u) :
    |g'' u| ≤ gKernelConst * (Real.exp (9 * u) * Real.exp (-(π / 2) * Real.exp (4 * u))) := by
  set E := Real.exp (-(π / 2) * Real.exp (4 * u)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have h0 := thetaMoment_zero_sub_one_le_decay hu
  have h0n : 0 ≤ thetaMoment 0 u - 1 := by linarith [one_le_thetaMoment_zero u]
  have h1 := thetaMoment_le_decay 1 one_pos hu
  have h1n := thetaMoment_nonneg 1 u
  have h2 := thetaMoment_le_decay 2 two_pos hu
  have h2n := thetaMoment_nonneg 2 u
  have hC0 := thetaPnatConst_nonneg 0
  have hC1 := thetaPnatConst_nonneg 1
  have hC2 := thetaPnatConst_nonneg 2
  have h19 : Real.exp u ≤ Real.exp (9 * u) := Real.exp_le_exp.mpr (by linarith)
  have h59 : Real.exp (5 * u) ≤ Real.exp (9 * u) := Real.exp_le_exp.mpr (by linarith)
  have hX : 0 ≤ Real.exp (9 * u) * E := by positivity
  have hA : Real.exp u * (thetaMoment 0 u - 1) / 2 ≤ thetaPnatConst 0 * (Real.exp (9 * u) * E) := by
    calc Real.exp u * (thetaMoment 0 u - 1) / 2 ≤ Real.exp u * (2 * thetaPnatConst 0 * E) / 2 := by
          gcongr
      _ = thetaPnatConst 0 * (Real.exp u * E) := by ring
      _ ≤ thetaPnatConst 0 * (Real.exp (9 * u) * E) := by gcongr
  have hB : 12 * π * Real.exp (5 * u) * thetaMoment 1 u
      ≤ 24 * π * thetaPnatConst 1 * (Real.exp (9 * u) * E) := by
    calc 12 * π * Real.exp (5 * u) * thetaMoment 1 u
        ≤ 12 * π * Real.exp (9 * u) * (2 * thetaPnatConst 1 * E) := by gcongr
      _ = 24 * π * thetaPnatConst 1 * (Real.exp (9 * u) * E) := by ring
  have hC : 8 * π ^ 2 * Real.exp (9 * u) * thetaMoment 2 u
      ≤ 16 * π ^ 2 * thetaPnatConst 2 * (Real.exp (9 * u) * E) := by
    calc 8 * π ^ 2 * Real.exp (9 * u) * thetaMoment 2 u
        ≤ 8 * π ^ 2 * Real.exp (9 * u) * (2 * thetaPnatConst 2 * E) := by gcongr
      _ = 16 * π ^ 2 * thetaPnatConst 2 * (Real.exp (9 * u) * E) := by ring
  have hA0 : 0 ≤ Real.exp u * (thetaMoment 0 u - 1) / 2 := by positivity
  have hB0 : 0 ≤ 12 * π * Real.exp (5 * u) * thetaMoment 1 u := by positivity
  have hC0' : 0 ≤ 8 * π ^ 2 * Real.exp (9 * u) * thetaMoment 2 u := by positivity
  unfold g''
  calc |Real.exp u * (thetaMoment 0 u - 1) / 2 - 12 * π * Real.exp (5 * u) * thetaMoment 1 u
        + 8 * π ^ 2 * Real.exp (9 * u) * thetaMoment 2 u|
      ≤ |Real.exp u * (thetaMoment 0 u - 1) / 2 - 12 * π * Real.exp (5 * u) * thetaMoment 1 u|
        + |8 * π ^ 2 * Real.exp (9 * u) * thetaMoment 2 u| := abs_add_le _ _
    _ ≤ (|Real.exp u * (thetaMoment 0 u - 1) / 2| + |12 * π * Real.exp (5 * u) * thetaMoment 1 u|)
        + |8 * π ^ 2 * Real.exp (9 * u) * thetaMoment 2 u| := by gcongr; exact abs_sub _ _
    _ = Real.exp u * (thetaMoment 0 u - 1) / 2 + 12 * π * Real.exp (5 * u) * thetaMoment 1 u
        + 8 * π ^ 2 * Real.exp (9 * u) * thetaMoment 2 u := by
        rw [abs_of_nonneg hA0, abs_of_nonneg hB0, abs_of_nonneg hC0']
    _ ≤ thetaPnatConst 0 * (Real.exp (9 * u) * E)
          + 24 * π * thetaPnatConst 1 * (Real.exp (9 * u) * E)
          + 16 * π ^ 2 * thetaPnatConst 2 * (Real.exp (9 * u) * E) :=
        add_le_add (add_le_add hA hB) hC
    _ = gKernelConst * (Real.exp (9 * u) * E) := by unfold gKernelConst; ring

/-! ### The `atTop` limit shared by all boundary terms (extracted from the island's majorant) -/

/-- `exp(a u² + b u) · exp(−(π/2) e^{4u}) → 0` as `u → ∞`, for every `a, b` (the `Tendsto` form
of the argument inside `integrableOn_exp_quad_mul_exp_neg_exp`). -/
theorem tendsto_exp_quad_mul_exp_neg_exp (a b : ℝ) :
    Tendsto (fun u : ℝ ↦ Real.exp (a * u ^ 2 + b * u) * Real.exp (-(π / 2) * Real.exp (4 * u)))
      atTop (𝓝 0) := by
  have hfun : (fun u : ℝ ↦ Real.exp (a * u ^ 2 + b * u) * Real.exp (-(π / 2) * Real.exp (4 * u)))
      = Real.exp ∘ fun u ↦ a * u ^ 2 + b * u + -(π / 2) * Real.exp (4 * u) := by
    funext u; simp only [Function.comp, ← Real.exp_add]
  rw [hfun]
  refine Real.tendsto_exp_atBot.comp ?_
  have hfact : (fun u : ℝ ↦ a * u ^ 2 + b * u + -(π / 2) * Real.exp (4 * u))
      = fun u ↦ Real.exp (4 * u) *
          (a * (u ^ 2 * Real.exp (-(4 * u))) + b * (u * Real.exp (-(4 * u))) - π / 2) := by
    funext u
    rw [Real.exp_neg]
    field_simp
    ring
  rw [hfact]
  have h4 : Tendsto (fun u : ℝ ↦ 4 * u) atTop atTop := tendsto_id.const_mul_atTop (by norm_num)
  apply Filter.Tendsto.atTop_mul_neg (by linarith [Real.pi_pos] : -(π / 2) < 0)
  · exact Real.tendsto_exp_atTop.comp h4
  · have h2 : Tendsto (fun u : ℝ ↦ u ^ 2 * Real.exp (-(4 * u))) atTop (𝓝 0) := by
      have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp h4).const_mul (1 / 16)
      rw [mul_zero] at this
      refine this.congr fun u ↦ ?_
      simp only [Function.comp]
      ring
    have h1 : Tendsto (fun u : ℝ ↦ u * Real.exp (-(4 * u))) atTop (𝓝 0) := by
      have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp h4).const_mul (1 / 4)
      rw [mul_zero] at this
      refine this.congr fun u ↦ ?_
      simp only [Function.comp]
      ring
    have := ((h2.const_mul a).add (h1.const_mul b)).sub_const (π / 2)
    simpa using this

/-- `exp(b u) · exp(−(π/2) e^{4u}) → 0` as `u → ∞` (memo section 5, risk note D). -/
theorem tendsto_exp_lin_mul_exp_neg_exp (b : ℝ) :
    Tendsto (fun u : ℝ ↦ Real.exp (b * u) * Real.exp (-(π / 2) * Real.exp (4 * u)))
      atTop (𝓝 0) := by
  simpa using tendsto_exp_quad_mul_exp_neg_exp 0 b

/-! ### Generic integrability and vanishing at infinity against exponential weights -/

/-- A continuous complex function dominated on `[0, ∞)` by `C e^{bu} exp(−(π/2) e^{4u})`, times a
continuous weight of at most exponential growth `A e^{Bu}`, is integrable on `(0, ∞)`. -/
theorem integrableOn_superExp_mul {f w : ℝ → ℂ} (hf : Continuous f) (hw : Continuous w)
    {C b A B : ℝ}
    (hfb : ∀ u, 0 ≤ u → ‖f u‖ ≤ C * (Real.exp (b * u) * Real.exp (-(π / 2) * Real.exp (4 * u))))
    (hwb : ∀ u, 0 ≤ u → ‖w u‖ ≤ A * Real.exp (B * u)) :
    IntegrableOn (fun u ↦ f u * w u) (Ioi 0) := by
  have hg := (integrableOn_exp_quad_mul_exp_neg_exp 0 (b + B)).const_mul (C * A)
  refine hg.mono' (hf.mul hw).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu ↦ ?_
  have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
  show ‖f u * w u‖ ≤ C * A * (Real.exp (0 * u ^ 2 + (b + B) * u)
    * Real.exp (-(π / 2) * Real.exp (4 * u)))
  rw [norm_mul]
  calc ‖f u‖ * ‖w u‖
      ≤ (C * (Real.exp (b * u) * Real.exp (-(π / 2) * Real.exp (4 * u))))
          * (A * Real.exp (B * u)) :=
        mul_le_mul (hfb u hu0) (hwb u hu0) (norm_nonneg _) ((norm_nonneg _).trans (hfb u hu0))
    _ = C * A * (Real.exp (0 * u ^ 2 + (b + B) * u) * Real.exp (-(π / 2) * Real.exp (4 * u))) := by
        rw [show 0 * u ^ 2 + (b + B) * u = b * u + B * u by ring, Real.exp_add]
        ring

/-- A complex function dominated on `[0, ∞)` by `C e^{bu} exp(−(π/2) e^{4u})`, times a weight of
at most exponential growth `A e^{Bu}`, tends to `0` at `+∞`. -/
theorem tendsto_superExp_mul_atTop {f w : ℝ → ℂ} {C b A B : ℝ}
    (hfb : ∀ u, 0 ≤ u → ‖f u‖ ≤ C * (Real.exp (b * u) * Real.exp (-(π / 2) * Real.exp (4 * u))))
    (hwb : ∀ u, 0 ≤ u → ‖w u‖ ≤ A * Real.exp (B * u)) :
    Tendsto (fun u ↦ f u * w u) atTop (𝓝 0) := by
  have hlim := (tendsto_exp_lin_mul_exp_neg_exp (b + B)).const_mul (C * A)
  rw [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 0] with u hu
  rw [norm_mul]
  calc ‖f u‖ * ‖w u‖
      ≤ (C * (Real.exp (b * u) * Real.exp (-(π / 2) * Real.exp (4 * u))))
          * (A * Real.exp (B * u)) :=
        mul_le_mul (hfb u hu) (hwb u hu) (norm_nonneg _) ((norm_nonneg _).trans (hfb u hu))
    _ = C * A * (Real.exp ((b + B) * u) * Real.exp (-(π / 2) * Real.exp (4 * u))) := by
        rw [add_mul, Real.exp_add]
        ring

/-- `‖cos(z u)‖ ≤ 1 · e^{‖z‖ u}` for `u ≥ 0` (the exponential-weight form used below). -/
theorem norm_cos_mul_ofReal_le (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖Complex.cos (z * u)‖ ≤ 1 * Real.exp (‖z‖ * u) := by
  rw [one_mul]
  refine (norm_cos_le_exp_norm _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]

/-- `‖sin(z u)‖ ≤ 1 · e^{‖z‖ u}` for `u ≥ 0`. -/
theorem norm_sin_mul_ofReal_le (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖Complex.sin (z * u)‖ ≤ 1 * Real.exp (‖z‖ * u) := by
  rw [one_mul]
  refine (norm_sin_le_exp_norm _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]

/-! ### The complexified kernels -/

theorem hasDerivAt_ofReal_g (u : ℝ) :
    HasDerivAt (fun x : ℝ ↦ ((g x : ℝ) : ℂ)) ((g' u : ℝ) : ℂ) u :=
  (hasDerivAt_g u).ofReal_comp

theorem hasDerivAt_ofReal_g' (u : ℝ) :
    HasDerivAt (fun x : ℝ ↦ ((g' x : ℝ) : ℂ)) ((g'' u : ℝ) : ℂ) u :=
  (hasDerivAt_g' u).ofReal_comp

@[fun_prop]
theorem continuous_ofReal_g : Continuous (fun u : ℝ ↦ ((g u : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp continuous_g

@[fun_prop]
theorem continuous_ofReal_g' : Continuous (fun u : ℝ ↦ ((g' u : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp continuous_g'

@[fun_prop]
theorem continuous_ofReal_g'' : Continuous (fun u : ℝ ↦ ((g'' u : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp continuous_g''

theorem norm_ofReal_g_le {u : ℝ} (hu : 0 ≤ u) :
    ‖((g u : ℝ) : ℂ)‖
      ≤ thetaPnatConst 0 * (Real.exp (1 * u) * Real.exp (-(π / 2) * Real.exp (4 * u))) := by
  rw [Complex.norm_real, Real.norm_eq_abs, one_mul]
  exact abs_g_le hu

theorem norm_ofReal_g'_le {u : ℝ} (hu : 0 ≤ u) :
    ‖((g' u : ℝ) : ℂ)‖
      ≤ gKernelConst * (Real.exp (5 * u) * Real.exp (-(π / 2) * Real.exp (4 * u))) := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_g'_le hu

theorem norm_ofReal_g''_le {u : ℝ} (hu : 0 ≤ u) :
    ‖((g'' u : ℝ) : ℂ)‖
      ≤ gKernelConst * (Real.exp (9 * u) * Real.exp (-(π / 2) * Real.exp (4 * u))) := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_g''_le hu

/-! ### Integrability against exponentially bounded weights (pointwise and `Pi.mul` shapes) -/

theorem integrableOn_g_mul {w : ℝ → ℂ} (hw : Continuous w) {A B : ℝ}
    (hwb : ∀ u, 0 ≤ u → ‖w u‖ ≤ A * Real.exp (B * u)) :
    IntegrableOn (fun u ↦ ((g u : ℝ) : ℂ) * w u) (Ioi 0) :=
  integrableOn_superExp_mul continuous_ofReal_g hw (fun _ hu ↦ norm_ofReal_g_le hu) hwb

theorem integrableOn_g'_mul {w : ℝ → ℂ} (hw : Continuous w) {A B : ℝ}
    (hwb : ∀ u, 0 ≤ u → ‖w u‖ ≤ A * Real.exp (B * u)) :
    IntegrableOn (fun u ↦ ((g' u : ℝ) : ℂ) * w u) (Ioi 0) :=
  integrableOn_superExp_mul continuous_ofReal_g' hw (fun _ hu ↦ norm_ofReal_g'_le hu) hwb

theorem integrableOn_g''_mul {w : ℝ → ℂ} (hw : Continuous w) {A B : ℝ}
    (hwb : ∀ u, 0 ≤ u → ‖w u‖ ≤ A * Real.exp (B * u)) :
    IntegrableOn (fun u ↦ ((g'' u : ℝ) : ℂ) * w u) (Ioi 0) :=
  integrableOn_superExp_mul continuous_ofReal_g'' hw (fun _ hu ↦ norm_ofReal_g''_le hu) hwb

/-- `Pi.mul` shape of `integrableOn_g_mul`, as consumed by `integral_Ioi_mul_deriv_eq_deriv_mul`. -/
theorem integrableOn_ofReal_g_mul_pi {w : ℝ → ℂ} (hw : Continuous w) {A B : ℝ}
    (hwb : ∀ u, 0 ≤ u → ‖w u‖ ≤ A * Real.exp (B * u)) :
    IntegrableOn ((fun u ↦ ((g u : ℝ) : ℂ)) * w) (Ioi 0) :=
  integrableOn_g_mul hw hwb

/-- `Pi.mul` shape of `integrableOn_g'_mul`. -/
theorem integrableOn_ofReal_g'_mul_pi {w : ℝ → ℂ} (hw : Continuous w) {A B : ℝ}
    (hwb : ∀ u, 0 ≤ u → ‖w u‖ ≤ A * Real.exp (B * u)) :
    IntegrableOn ((fun u ↦ ((g' u : ℝ) : ℂ)) * w) (Ioi 0) :=
  integrableOn_g'_mul hw hwb

/-- `Pi.mul` shape of `integrableOn_g''_mul`. -/
theorem integrableOn_ofReal_g''_mul_pi {w : ℝ → ℂ} (hw : Continuous w) {A B : ℝ}
    (hwb : ∀ u, 0 ≤ u → ‖w u‖ ≤ A * Real.exp (B * u)) :
    IntegrableOn ((fun u ↦ ((g'' u : ℝ) : ℂ)) * w) (Ioi 0) :=
  integrableOn_g''_mul hw hwb

/-- `g(u) cos(zu)` is integrable on `(0, ∞)` for every complex `z`. -/
theorem integrableOn_g_mul_cos (z : ℂ) :
    IntegrableOn (fun u ↦ ((g u : ℝ) : ℂ) * Complex.cos (z * u)) (Ioi 0) :=
  integrableOn_g_mul (by fun_prop) fun _ hu ↦ norm_cos_mul_ofReal_le z hu

/-- `g(u) sin(zu)` is integrable on `(0, ∞)` for every complex `z`. -/
theorem integrableOn_g_mul_sin (z : ℂ) :
    IntegrableOn (fun u ↦ ((g u : ℝ) : ℂ) * Complex.sin (z * u)) (Ioi 0) :=
  integrableOn_g_mul (by fun_prop) fun _ hu ↦ norm_sin_mul_ofReal_le z hu

/-- `g'(u) cos(zu)` is integrable on `(0, ∞)` for every complex `z`. -/
theorem integrableOn_g'_mul_cos (z : ℂ) :
    IntegrableOn (fun u ↦ ((g' u : ℝ) : ℂ) * Complex.cos (z * u)) (Ioi 0) :=
  integrableOn_g'_mul (by fun_prop) fun _ hu ↦ norm_cos_mul_ofReal_le z hu

/-- `g'(u) sin(zu)` is integrable on `(0, ∞)` for every complex `z`. -/
theorem integrableOn_g'_mul_sin (z : ℂ) :
    IntegrableOn (fun u ↦ ((g' u : ℝ) : ℂ) * Complex.sin (z * u)) (Ioi 0) :=
  integrableOn_g'_mul (by fun_prop) fun _ hu ↦ norm_sin_mul_ofReal_le z hu

/-- `g''(u) cos(zu)` is integrable on `(0, ∞)` for every complex `z`. -/
theorem integrableOn_g''_mul_cos (z : ℂ) :
    IntegrableOn (fun u ↦ ((g'' u : ℝ) : ℂ) * Complex.cos (z * u)) (Ioi 0) :=
  integrableOn_g''_mul (by fun_prop) fun _ hu ↦ norm_cos_mul_ofReal_le z hu

/-! ### Vanishing at `+∞` against exponentially bounded weights (the `atTop` boundary terms) -/

theorem tendsto_ofReal_g_mul_atTop {w : ℝ → ℂ} {A B : ℝ}
    (hwb : ∀ u, 0 ≤ u → ‖w u‖ ≤ A * Real.exp (B * u)) :
    Tendsto ((fun u ↦ ((g u : ℝ) : ℂ)) * w) atTop (𝓝 0) :=
  tendsto_superExp_mul_atTop (fun _ hu ↦ norm_ofReal_g_le hu) hwb

theorem tendsto_ofReal_g'_mul_atTop {w : ℝ → ℂ} {A B : ℝ}
    (hwb : ∀ u, 0 ≤ u → ‖w u‖ ≤ A * Real.exp (B * u)) :
    Tendsto ((fun u ↦ ((g' u : ℝ) : ℂ)) * w) atTop (𝓝 0) :=
  tendsto_superExp_mul_atTop (fun _ hu ↦ norm_ofReal_g'_le hu) hwb

theorem tendsto_ofReal_g''_mul_atTop {w : ℝ → ℂ} {A B : ℝ}
    (hwb : ∀ u, 0 ≤ u → ‖w u‖ ≤ A * Real.exp (B * u)) :
    Tendsto ((fun u ↦ ((g'' u : ℝ) : ℂ)) * w) atTop (𝓝 0) :=
  tendsto_superExp_mul_atTop (fun _ hu ↦ norm_ofReal_g''_le hu) hwb

/-! ### Limits at `0⁺` (continuity) -/

theorem tendsto_ofReal_g_mul_nhdsGT {w : ℝ → ℂ} (hw : Continuous w) :
    Tendsto ((fun u ↦ ((g u : ℝ) : ℂ)) * w) (𝓝[>] 0) (𝓝 (((g 0 : ℝ) : ℂ) * w 0)) :=
  ((continuous_ofReal_g.mul hw).tendsto 0).mono_left nhdsWithin_le_nhds

theorem tendsto_ofReal_g'_mul_nhdsGT {w : ℝ → ℂ} (hw : Continuous w) :
    Tendsto ((fun u ↦ ((g' u : ℝ) : ℂ)) * w) (𝓝[>] 0) (𝓝 (((g' 0 : ℝ) : ℂ) * w 0)) :=
  ((continuous_ofReal_g'.mul hw).tendsto 0).mono_left nhdsWithin_le_nhds

/-! ### The side conditions of the two integrations by parts (consumed by module D)

Module D applies `integral_Ioi_mul_deriv_eq_deriv_mul` twice on `Ioi 0` with `z : ℂ` fixed:

* IBP-1: `u = (g · : ℂ)`, `u' = (g' · : ℂ)`, `v = −sin(z·)·z`, `v' = −(cos(z·)·z)·z`
  (so `v' = −z² cos(z·)`), boundary values `0` at `0⁺` and at `+∞`;
* IBP-2: `u = (g' · : ℂ)`, `u' = (g'' · : ℂ)`, `v = cos(z·)`, `v' = −sin(z·)·z`,
  boundary values `g'(0)` at `0⁺` and `0` at `+∞`.

Every hypothesis of both applications is stated below in exactly the `Pi.mul` shape of that
lemma, so the IBP module is pure assembly. -/

/-- `d/du cos(zu) = −sin(zu) · z` for real `u` and complex `z`. -/
theorem hasDerivAt_cos_mul_ofReal (z : ℂ) (u : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Complex.cos (z * x)) (-Complex.sin (z * u) * z) u := by
  have hin : HasDerivAt (fun x : ℝ ↦ z * (x : ℂ)) z u := by
    simpa using ((hasDerivAt_id u).ofReal_comp).const_mul z
  exact (Complex.hasDerivAt_cos (z * u)).comp u hin

/-- `d/du (−sin(zu) · z) = −(cos(zu) · z) · z` for real `u` and complex `z`. -/
theorem hasDerivAt_neg_sin_mul_ofReal_mul (z : ℂ) (u : ℝ) :
    HasDerivAt (fun x : ℝ ↦ -Complex.sin (z * x) * z) (-(Complex.cos (z * u) * z) * z) u := by
  have hin : HasDerivAt (fun x : ℝ ↦ z * (x : ℂ)) z u := by
    simpa using ((hasDerivAt_id u).ofReal_comp).const_mul z
  exact (((Complex.hasDerivAt_sin (z * u)).comp u hin).neg).mul_const z

/-- `‖−sin(zu) · z‖ ≤ ‖z‖ e^{‖z‖u}` for `u ≥ 0`. -/
theorem norm_neg_sin_mul_ofReal_mul_le (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖-Complex.sin (z * u) * z‖ ≤ ‖z‖ * Real.exp (‖z‖ * u) := by
  have h := norm_sin_mul_ofReal_le z hu
  rw [one_mul] at h
  rw [norm_mul, norm_neg]
  calc ‖Complex.sin (z * u)‖ * ‖z‖ ≤ Real.exp (‖z‖ * u) * ‖z‖ := by gcongr
    _ = ‖z‖ * Real.exp (‖z‖ * u) := mul_comm _ _

/-- `‖−(cos(zu) · z) · z‖ ≤ ‖z‖² e^{‖z‖u}` for `u ≥ 0`. -/
theorem norm_neg_cos_mul_ofReal_mul_mul_le (z : ℂ) {u : ℝ} (hu : 0 ≤ u) :
    ‖-(Complex.cos (z * u) * z) * z‖ ≤ ‖z‖ ^ 2 * Real.exp (‖z‖ * u) := by
  have h := norm_cos_mul_ofReal_le z hu
  rw [one_mul] at h
  rw [norm_mul, norm_neg, norm_mul]
  calc ‖Complex.cos (z * u)‖ * ‖z‖ * ‖z‖ ≤ Real.exp (‖z‖ * u) * ‖z‖ * ‖z‖ := by gcongr
    _ = ‖z‖ ^ 2 * Real.exp (‖z‖ * u) := by ring

/-- IBP-1, `IntegrableOn (u * v')`: `g · (−(cos(z·)·z)·z)`. -/
theorem integrableOn_ofReal_g_mul_cos_deriv2 (z : ℂ) :
    IntegrableOn ((fun u ↦ ((g u : ℝ) : ℂ)) * fun x : ℝ ↦ -(Complex.cos (z * x) * z) * z)
      (Ioi 0) :=
  integrableOn_ofReal_g_mul_pi (by fun_prop) fun _ hu ↦ norm_neg_cos_mul_ofReal_mul_mul_le z hu

/-- IBP-1 `IntegrableOn (u' * v)` and IBP-2 `IntegrableOn (u * v')`: `g' · (−sin(z·)·z)`. -/
theorem integrableOn_ofReal_g'_mul_cos_deriv (z : ℂ) :
    IntegrableOn ((fun u ↦ ((g' u : ℝ) : ℂ)) * fun x : ℝ ↦ -Complex.sin (z * x) * z) (Ioi 0) :=
  integrableOn_ofReal_g'_mul_pi (by fun_prop) fun _ hu ↦ norm_neg_sin_mul_ofReal_mul_le z hu

/-- IBP-2, `IntegrableOn (u' * v)`: `g'' · cos(z·)`. -/
theorem integrableOn_ofReal_g''_mul_cos_pi (z : ℂ) :
    IntegrableOn ((fun u ↦ ((g'' u : ℝ) : ℂ)) * fun x : ℝ ↦ Complex.cos (z * x)) (Ioi 0) :=
  integrableOn_ofReal_g''_mul_pi (by fun_prop) fun _ hu ↦ norm_cos_mul_ofReal_le z hu

/-- IBP-1 boundary term at `0⁺`: `g(u) · (−sin(zu)·z) → 0`. -/
theorem tendsto_ofReal_g_mul_cos_deriv_nhdsGT (z : ℂ) :
    Tendsto ((fun u ↦ ((g u : ℝ) : ℂ)) * fun x : ℝ ↦ -Complex.sin (z * x) * z) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_ofReal_g_mul_nhdsGT (w := fun x : ℝ ↦ -Complex.sin (z * x) * z) (by fun_prop)
  simpa using h

/-- IBP-1 boundary term at `+∞`: `g(u) · (−sin(zu)·z) → 0`. -/
theorem tendsto_ofReal_g_mul_cos_deriv_atTop (z : ℂ) :
    Tendsto ((fun u ↦ ((g u : ℝ) : ℂ)) * fun x : ℝ ↦ -Complex.sin (z * x) * z) atTop (𝓝 0) :=
  tendsto_ofReal_g_mul_atTop fun _ hu ↦ norm_neg_sin_mul_ofReal_mul_le z hu

/-- IBP-2 boundary term at `0⁺`: `g'(u) · cos(zu) → g'(0)`. -/
theorem tendsto_ofReal_g'_mul_cos_nhdsGT (z : ℂ) :
    Tendsto ((fun u ↦ ((g' u : ℝ) : ℂ)) * fun x : ℝ ↦ Complex.cos (z * x)) (𝓝[>] 0)
      (𝓝 ((g' 0 : ℝ) : ℂ)) := by
  have h := tendsto_ofReal_g'_mul_nhdsGT (w := fun x : ℝ ↦ Complex.cos (z * x)) (by fun_prop)
  simpa using h

/-- IBP-2 boundary term at `+∞`: `g'(u) · cos(zu) → 0`. -/
theorem tendsto_ofReal_g'_mul_cos_atTop (z : ℂ) :
    Tendsto ((fun u ↦ ((g' u : ℝ) : ℂ)) * fun x : ℝ ↦ Complex.cos (z * x)) atTop (𝓝 0) :=
  tendsto_ofReal_g'_mul_atTop fun _ hu ↦ norm_cos_mul_ofReal_le z hu

/-! ### The kernel identity against `cos(zu)`: the bridge to `H_0` -/

/-- `∫_0^∞ (g'' − g)(u) cos(zu) du = 8 H_0(z)` for every complex `z` (pointwise kernel identity
`g''_sub_g_eq`, and `e^{0 · u²} = 1` in `HIntegrand 0`). -/
theorem integral_g''_sub_g_mul_cos (z : ℂ) :
    ∫ u in Ioi (0 : ℝ), ((g'' u - g u : ℝ) : ℂ) * Complex.cos (z * u) = 8 * H 0 z := by
  unfold H HIntegrand
  rw [← integral_const_mul]
  congr 1
  funext u
  rw [g''_sub_g_eq]
  simp only [zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]
  push_cast
  ring

end DBN

/-- Registry-shaped summary of C2 module C (proposed lemma node `RH_dbn_g_kernel_identities`,
design memo section 5): `g'` and `g''` ARE the first two derivatives of the kernel
`g(u) = e^{u} ψ(e^{4u})`, the kernel identity `g'' − g = 8Φ` holds pointwise, and
`g'(0) = −1/2`.  An ingredient of the representation theorem `H_0 = ξ/8`, not that theorem;
not RH-adjacent.  Nothing here proves RH.  conjecture1_proved = False. -/
theorem dbn_g_kernel_identities :
    (∀ u : ℝ, HasDerivAt DBN.g (DBN.g' u) u) ∧ (∀ u : ℝ, HasDerivAt DBN.g' (DBN.g'' u) u) ∧
      (∀ u : ℝ, DBN.g'' u - DBN.g u = 8 * DBN.Φ u) ∧ DBN.g' 0 = -1 / 2 :=
  ⟨DBN.hasDerivAt_g, DBN.hasDerivAt_g', DBN.g''_sub_g_eq, DBN.g'_zero⟩
