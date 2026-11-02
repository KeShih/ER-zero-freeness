/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs
import ERZeroFreeness.ErdosRenyi
import ERZeroFreeness.DenseSubgraph
import ERZeroFreeness.TaylorGood
import ERZeroFreeness.CycleMoments
import ERZeroFreeness.Bonferroni
import ERZeroFreeness.Poisson
import ERZeroFreeness.CycleModel
import ERZeroFreeness.Vanishing
import ERZeroFreeness.SupBound

/-!
# Zero-freeness from a first-moment bound (Proposition 6.1, `prop:zero-free-moment`, `t`-plane)

`zero_free_of_first_moment` is the `t`-plane conclusion `eq:t-zero-free` of Proposition 6.1:
if `0 < s < 1`, `(q-1)s ≤ 1`, `ds² < 1` and `E|Ẑ_G(t)| ≤ B` for `G ∼ G(n, d/n)`, all `n ≥ d`
and all `t ∈ L_r(I_s)`, then for some `ρ > 0`, with probability tending to `1`, `Ẑ_G` has no
zero on `L_ρ(I_s)`.  The convergence in distribution `Ẑ_{G_n} → 𝒲` stated in the proposition
is not formalized; it is not needed for zero-freeness.  The `z`-plane part is
`prop_zero_free_moment`.

The proof replaces the analytic transfer (Theorem 3.1, `lem:analytic-transfer`) by a direct
argument: the compactness argument becomes the quantitative identity theorem
`exists_norm_le_of_isBigO_pow`, and convergence in law of the Taylor coefficients becomes
convergence of the mass functions of the short-cycle counts on `ℕ^k` (`eventually_sum_mem_le`).

Proof.  Choose `ρ > 0` with `4ρ ≤ r` and `tube s (4ρ) ⊆ cycleDomain q d` (the
inequalities defining `𝒟` hold strictly on `I_s`: `|t| ≤ s < 1`, `(q-1)|t|³ ≤ s² < 1`,
`d|t|² ≤ ds² < 1`, `Re(1-dt) ≥ 1`).  Put `K = tube s ρ`, `L = tube s (3ρ)`.
* `erProb_exists_norm_gt_le`: `P_n[sup_L |Ẑ| > M] ≤ C_U/M`.
* `cycleModel_bounds` on `L`: constants `C₀`, `σ`, `E∞ = ∑' i, poisExp (λ_i) (σ i)`.
Given `η > 0`: choose `Y > 0` with `E∞ ≤ η Y`, then `M ≥ 1` with `C_U/M ≤ η` and
`C₀ + Y ≤ log M`, `ε = exp(-C₀ - Y)/(2M)`, and `k` from `exists_norm_le_of_isBigO_pow`.
For `n ≥ d`, `{∃ t ∈ K, Ẑ_G t = 0}` is contained in
`HasDenseSubgraph G (2(k+2)) ∪ {∃ t ∈ L, M < |Ẑ_G t|} ∪ {cycleCounts k G ∈ 𝔅}`, where
`𝔅 = {x | ∃ g, DifferentiableOn ℂ g (openTube s (4ρ)) ∧ (∀ t ∈ L, ‖g t‖ ≤ M) ∧
(∃ t ∈ K, g t = 0) ∧ (g - Q(·;x)) =O[𝓝 0] t^{k+3}}` (on the non-dense event the
coefficients agree, `zhat_coeff_eq_cyclePoly_coeff`, so `Ẑ_G - Q = X^{k+3}·R`).
The first probability → 0 (`tendsto_erProb_hasDenseSubgraph`), the second is `≤ η`, and the
third is eventually `≤ poisProb λ 𝔅 + η` (`tendsto_erExp_cycle_descFactorial`,
`tendsto_prob_eq_of_factorial_moments`, `eventually_sum_mem_le`, `sum_erWeight`).
Finally `𝔅 ⊆ {Y ≤ ∑σ}`: otherwise `∑σ < Y ≤ log M - C₀`, so `|W| ≤ M` on `L`, and
`h = (g - W)/(2M)` satisfies the hypotheses of `exists_norm_le_of_isBigO_pow`
(`cycleModel_differentiableOn`, `cycleModel_sub_cyclePoly_isBigO`), so at the zero `t*` of `g`,
`|W(t*)| ≤ 2Mε = exp(-C₀ - Y) < exp(-C₀ - ∑σ) ≤ |W(t*)|`.  By `poisProb_le_of_sum` the set
`{Y ≤ ∑σ}` has probability `≤ E∞/Y ≤ η`, so the bad event eventually has probability `≤ 4η`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

namespace TransferAux

/-! ### Elementary facts about the tubes `L_r(I_s)` and `U_r(I_s)` -/

private theorem tube_mono {s r r' : ℝ} (h : r ≤ r') : tube s r ⊆ tube s r' := by
  rintro t ⟨x, hx, hxt⟩
  exact ⟨x, hx, hxt.trans h⟩

private theorem tube_subset_openTube {s r r' : ℝ} (h : r < r') : tube s r ⊆ openTube s r' := by
  rintro t ⟨x, hx, hxt⟩
  exact ⟨x, hx, hxt.trans_lt h⟩

private theorem openTube_subset_tube {s r : ℝ} : openTube s r ⊆ tube s r := by
  rintro t ⟨x, hx, hxt⟩
  exact ⟨x, hx, hxt.le⟩

private theorem norm_le_of_mem_tube {s r : ℝ} {t : ℂ} (ht : t ∈ tube s r) : ‖t‖ ≤ s + r := by
  obtain ⟨x, ⟨hx1, hx2⟩, hxt⟩ := ht
  have hx : ‖(x : ℂ)‖ ≤ s := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  calc ‖t‖ = ‖(t - x) + x‖ := by rw [sub_add_cancel]
    _ ≤ ‖t - x‖ + ‖(x : ℂ)‖ := norm_add_le _ _
    _ ≤ r + s := add_le_add hxt hx
    _ = s + r := add_comm r s

private theorem re_le_of_mem_tube {s r : ℝ} {t : ℂ} (ht : t ∈ tube s r) : t.re ≤ r := by
  obtain ⟨x, ⟨hx1, hx2⟩, hxt⟩ := ht
  have h1 : (t - x).re ≤ ‖t - x‖ := Complex.re_le_norm _
  rw [Complex.sub_re, Complex.ofReal_re] at h1
  linarith

private theorem isCompact_tube (s r : ℝ) : IsCompact (tube s r) := by
  have h : tube s r = (fun p : ℝ × ℂ => (p.1 : ℂ) + p.2) ''
      (Set.Icc (-s) 0 ×ˢ Metric.closedBall (0 : ℂ) r) := by
    ext t
    constructor
    · rintro ⟨x, hx, hxt⟩
      exact ⟨(x, t - x), Set.mk_mem_prod hx (mem_closedBall_zero_iff.2 hxt),
        add_sub_cancel _ _⟩
    · rintro ⟨⟨x, w⟩, ⟨hx, hw⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      show ‖(x : ℂ) + w - x‖ ≤ r
      rw [add_sub_cancel_left]
      exact mem_closedBall_zero_iff.1 hw
  rw [h]
  exact (isCompact_Icc.prod (isCompact_closedBall _ _)).image (by fun_prop)

/-- A thin closed tube around `I_s` lies in the domain `𝒟` of the compensated cycle model. -/
private theorem exists_rho {q : ℕ} (hq : 2 ≤ q) {d : ℝ} (hd : 0 < d) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hsq : ((q : ℝ) - 1) * s ≤ 1) (hds : d * s ^ 2 < 1)
    {r : ℝ} (hr : 0 < r) :
    ∃ ρ > 0, 4 * ρ ≤ r ∧ tube s (4 * ρ) ⊆ cycleDomain q d := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hs3 : ((q : ℝ) - 1) * s ^ 3 < 1 := by
    have hs2 : s ^ 2 < 1 := by nlinarith
    calc ((q : ℝ) - 1) * s ^ 3 = (((q : ℝ) - 1) * s) * s ^ 2 := by ring
      _ ≤ 1 * s ^ 2 := mul_le_mul_of_nonneg_right hsq (by positivity)
      _ < 1 := by linarith
  have e1 : ∀ᶠ ρ in 𝓝 (0 : ℝ), s + 4 * ρ < 1 :=
    ContinuousAt.eventually_lt (f := fun ρ : ℝ => s + 4 * ρ) (g := fun _ => (1 : ℝ))
      (by fun_prop) (by fun_prop) (by simp only [mul_zero, add_zero]; exact hs1)
  have e2 : ∀ᶠ ρ in 𝓝 (0 : ℝ), d * (s + 4 * ρ) ^ 2 < 1 :=
    ContinuousAt.eventually_lt (f := fun ρ : ℝ => d * (s + 4 * ρ) ^ 2) (g := fun _ => (1 : ℝ))
      (by fun_prop) (by fun_prop) (by simp only [mul_zero, add_zero]; exact hds)
  have e3 : ∀ᶠ ρ in 𝓝 (0 : ℝ), ((q : ℝ) - 1) * (s + 4 * ρ) ^ 3 < 1 :=
    ContinuousAt.eventually_lt (f := fun ρ : ℝ => ((q : ℝ) - 1) * (s + 4 * ρ) ^ 3)
      (g := fun _ => (1 : ℝ)) (by fun_prop) (by fun_prop)
      (by simp only [mul_zero, add_zero]; exact hs3)
  have e4 : ∀ᶠ ρ in 𝓝 (0 : ℝ), d * (4 * ρ) < 1 :=
    ContinuousAt.eventually_lt (f := fun ρ : ℝ => d * (4 * ρ)) (g := fun _ => (1 : ℝ))
      (by fun_prop) (by fun_prop) (by simp only [mul_zero]; exact one_pos)
  have e5 : ∀ᶠ ρ in 𝓝 (0 : ℝ), 4 * ρ < r :=
    ContinuousAt.eventually_lt (f := fun ρ : ℝ => 4 * ρ) (g := fun _ => r)
      (by fun_prop) (by fun_prop) (by simp only [mul_zero]; exact hr)
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 (e1.and (e2.and (e3.and (e4.and e5))))
  have hmem : dist (δ / 2) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith
  obtain ⟨h1, h2, h3, h4, h5⟩ := hδP hmem
  refine ⟨δ / 2, by linarith, h5.le, ?_⟩
  intro t ht
  have hn := norm_le_of_mem_tube ht
  have hre := re_le_of_mem_tube ht
  have hn0 : 0 ≤ ‖t‖ := norm_nonneg t
  refine ⟨hn.trans_lt h1, ?_, ?_, ?_⟩
  · calc d * ‖t‖ ^ 2 ≤ d * (s + 4 * (δ / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn0 hn 2) hd.le
      _ < 1 := h2
  · calc ((q : ℝ) - 1) * ‖t‖ ^ 3 ≤ ((q : ℝ) - 1) * (s + 4 * (δ / 2)) ^ 3 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn0 hn 3) (by linarith)
      _ < 1 := h3
  · have hre' : (1 - (d : ℂ) * t).re = 1 - d * t.re := by
      rw [Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul]
    rw [hre']
    have : d * t.re ≤ d * (4 * (δ / 2)) := mul_le_mul_of_nonneg_left hre hd.le
    linarith

/-! ### Glue: Taylor coefficients, Poisson limits, and an `ε`-criterion -/

/-- On the non-dense event, `Ẑ_G - Q(·; C(G)) = X^{k+3} · R`, hence `O(t^{k+3})` at `0`. -/
private theorem zhat_sub_cyclePoly_isBigO {q : ℕ} (hq : 2 ≤ q) (k : ℕ) {V : Type*}
    [Fintype V] (G : SimpleGraph V) (hG : ¬ HasDenseSubgraph G (2 * (k + 2))) :
    (fun t => (zhat G q).eval t - (cyclePoly q k (cycleCounts k G)).eval t) =O[𝓝 0]
      fun t => t ^ (k + 3) := by
  have hdvd : X ^ (k + 3) ∣ zhat G q - cyclePoly q k (cycleCounts k G) := by
    rw [X_pow_dvd_iff]
    intro j hj
    rw [coeff_sub, zhat_coeff_eq_cyclePoly_coeff hq k G hG j (by omega), sub_self]
  obtain ⟨R, hR⟩ := hdvd
  have heq : (fun t => (zhat G q).eval t - (cyclePoly q k (cycleCounts k G)).eval t) =
      fun t => t ^ (k + 3) * R.eval t := by
    funext t
    rw [← eval_sub, hR, eval_mul, eval_pow, eval_X]
  rw [heq]
  have h1 : (fun t : ℂ => R.eval t) =O[𝓝 0] (fun _ => (1 : ℂ)) :=
    (R.continuous.tendsto 0).isBigO_one ℂ
  have h2 := (Asymptotics.isBigO_refl (fun t : ℂ => t ^ (k + 3)) (𝓝 0)).mul h1
  simp only [mul_one] at h2
  exact h2

/-- Poisson limit of the short cycle counts, as an eventual upper bound for any set. -/
private theorem eventually_erProb_cycleCounts_mem_le {d : ℝ} (hd : 0 < d) (k : ℕ)
    (B : Set (Fin k → ℕ)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, erProb n (d / n) {G | cycleCounts k G ∈ B} ≤
      poisProb (fun i : Fin k => cycleMean d i) B + η := by
  have hw : ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), 0 ≤ erWeight n (d / n) G := by
    filter_upwards [eventually_ge_atTop ⌈d⌉₊] with n hn G
    have hdn : d ≤ n := (Nat.le_ceil d).trans (by exact_mod_cast hn)
    obtain ⟨h0, h1⟩ := div_natCast_mem_Icc hd.le hdn
    exact erWeight_nonneg h0 h1 G
  have hlam : ∀ i : Fin k, 0 ≤ cycleMean d i := fun i => by
    unfold cycleMean
    positivity
  have htot : Tendsto (fun n : ℕ => ∑ G : SimpleGraph (Fin n), erWeight n (d / n) G) atTop
      (𝓝 1) := by
    simp only [sum_erWeight]
    exact tendsto_const_nhds
  have hconv := fun x => tendsto_prob_eq_of_factorial_moments
    (Ω := fun n => SimpleGraph (Fin n)) (fun n G => erWeight n (d / n) G) hw
    (fun n G => cycleCounts k G) hlam (fun κ => tendsto_erExp_cycle_descFactorial hd k κ) x
  exact eventually_sum_mem_le (Ω := fun n => SimpleGraph (Fin n))
    (fun n G => erWeight n (d / n) G) hw htot (fun n G => cycleCounts k G) hlam hconv B hη

private theorem tendsto_zero_of_eventually_le {f : ℕ → ℝ} (h0 : ∀ᶠ n in atTop, 0 ≤ f n)
    (h : ∀ η > 0, ∀ᶠ n in atTop, f n ≤ 4 * η) : Tendsto f atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => h0.mono fun n hn => ha.trans_le hn, fun a ha => ?_⟩
  filter_upwards [h (a / 8) (by positivity)] with n hn
  linarith

/-! ### The exceptional set of cycle-count vectors -/

/-- The set `𝔅` of cycle-count vectors `x` for which some holomorphic `g` on `U_{4ρ}(I_s)`,
bounded by `M` on `L_{3ρ}(I_s)` and vanishing somewhere on `L_ρ(I_s)`, agrees with
`Q_{k+2}(·;x)` to order `k + 2` at `0`. -/
private def badSet (q : ℕ) (s ρ M : ℝ) (k : ℕ) : Set (Fin k → ℕ) :=
  {x | ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (openTube s (4 * ρ)) ∧
    (∀ t ∈ tube s (3 * ρ), ‖g t‖ ≤ M) ∧ (∃ t ∈ tube s ρ, g t = 0) ∧
    (fun t => g t - (cyclePoly q k x).eval t) =O[𝓝 0] fun t => t ^ (k + 3)}

/-- If `∑ σ < Y`, the compensated model `W` is bounded by `M` on `L_{3ρ}` and bounded below by
`exp(-C₀ - ∑ σ) > 2Mε` on `L_ρ`, so no `g` as in `badSet` can exist (quantitative identity
theorem applied to `(g - W)/(2M)`). -/
private theorem badSet_subset {q : ℕ} (hq : 2 ≤ q) {d : ℝ} (hd : 0 < d) {s ρ M C₀ Y : ℝ}
    (hρ : 0 < ρ) (hM : 0 < M) (hOD : openTube s (4 * ρ) ⊆ cycleDomain q d)
    (hYM : C₀ + Y ≤ Real.log M) {σ : ℕ → ℕ → ℝ}
    (hW : ∀ (r : ℕ) (x : Fin r → ℕ), ∀ t ∈ tube s (3 * ρ),
        Real.exp (-C₀ - ∑ i : Fin r, σ i (x i)) ≤ ‖cycleModel q d r x t‖ ∧
          ‖cycleModel q d r x t‖ ≤ Real.exp (C₀ + ∑ i : Fin r, σ i (x i)))
    {k : ℕ} (hk : ∀ k' ≥ k, ∀ h : ℂ → ℂ, DifferentiableOn ℂ h (openTube s (4 * ρ)) →
      (∀ t ∈ tube s (3 * ρ), ‖h t‖ ≤ 1) → (h =O[𝓝 0] fun t => t ^ k') →
        ∀ t ∈ tube s ρ, ‖h t‖ ≤ Real.exp (-C₀ - Y) / (2 * M)) :
    badSet q s ρ M k ⊆ {x | Y ≤ ∑ i : Fin k, σ i (x i)} := by
  rintro x ⟨g, hgd, hgM, ⟨t₀, ht₀, hgt₀⟩, hgO⟩
  by_contra hlt'
  have hlt : ∑ i : Fin k, σ i (x i) < Y := lt_of_not_ge hlt'
  have h2M : (0 : ℝ) < 2 * M := by positivity
  have hWL : ∀ t ∈ tube s (3 * ρ), ‖cycleModel q d k x t‖ ≤ M := by
    intro t ht
    calc ‖cycleModel q d k x t‖ ≤ Real.exp (C₀ + ∑ i : Fin k, σ i (x i)) := (hW k x t ht).2
      _ ≤ Real.exp (Real.log M) := Real.exp_le_exp.2 (by linarith)
      _ = M := Real.exp_log hM
  obtain ⟨h, hh⟩ : ∃ h : ℂ → ℂ,
      h = fun t => ((2 * M : ℝ) : ℂ)⁻¹ * (g t - cycleModel q d k x t) := ⟨_, rfl⟩
  have hhd : DifferentiableOn ℂ h (openTube s (4 * ρ)) := by
    rw [hh]
    exact (hgd.sub ((cycleModel_differentiableOn hq hd k x).mono hOD)).const_mul _
  have hnorm : ∀ t, ‖h t‖ = (2 * M)⁻¹ * ‖g t - cycleModel q d k x t‖ := by
    intro t
    rw [hh, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2M]
  have hhb : ∀ t ∈ tube s (3 * ρ), ‖h t‖ ≤ 1 := by
    intro t ht
    rw [hnorm, inv_mul_le_iff₀ h2M]
    calc ‖g t - cycleModel q d k x t‖ ≤ ‖g t‖ + ‖cycleModel q d k x t‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hgM t ht) (hWL t ht)
      _ = 2 * M * 1 := by ring
  have hhO : h =O[𝓝 0] fun t => t ^ (k + 3) := by
    have h1 : (fun t => g t - cycleModel q d k x t) =O[𝓝 0] fun t => t ^ (k + 3) :=
      (hgO.sub (cycleModel_sub_cyclePoly_isBigO hq hd k x)).congr_left fun t => by ring
    rw [hh]
    exact h1.const_mul_left _
  have hsmall := hk (k + 3) (by omega) h hhd hhb hhO t₀ ht₀
  rw [hnorm, hgt₀, zero_sub, norm_neg, inv_mul_le_iff₀ h2M, mul_div_cancel₀ _ h2M.ne']
    at hsmall
  have hlow := (hW k x t₀ (tube_mono (by linarith) ht₀)).1
  have hlt' : Real.exp (-C₀ - Y) < Real.exp (-C₀ - ∑ i : Fin k, σ i (x i)) :=
    Real.exp_lt_exp.2 (by linarith)
  linarith

end TransferAux

/-- **Proposition 6.1 (`prop:zero-free-moment`), `t`-plane part** (`eq:t-zero-free`).  A
uniform first-moment bound on `L_r(I_s)` gives `ρ > 0` such that, with probability tending to
`1`, `Ẑ_G` has no zero on `L_ρ(I_s)`. -/
theorem zero_free_of_first_moment {q : ℕ} (hq : 2 ≤ q) {d : ℝ} (hd : 0 < d) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hsq : ((q : ℝ) - 1) * s ≤ 1) (hds : d * s ^ 2 < 1)
    {r B : ℝ} (hr : 0 < r)
    (hmom : ∀ n : ℕ, d ≤ n → ∀ t ∈ tube s r,
      erExp n (d / n) (fun G => ‖(zhat G q).eval t‖) ≤ B) :
    ∃ ρ > 0, Tendsto (fun n : ℕ => erProb n (d / n)
        {G | ∀ t ∈ tube s ρ, (zhat G q).eval t ≠ 0}) atTop (𝓝 1) := by
  obtain ⟨ρ, hρ, h4ρ, hdom⟩ := TransferAux.exists_rho hq hd hs0 hs1 hsq hds hr
  refine ⟨ρ, hρ, ?_⟩
  have hOD : openTube s (4 * ρ) ⊆ cycleDomain q d := TransferAux.openTube_subset_tube.trans hdom
  have hLD : tube s (3 * ρ) ⊆ cycleDomain q d :=
    (TransferAux.tube_subset_openTube (by linarith : 3 * ρ < 4 * ρ)).trans hOD
  -- `P_n[sup_L |Ẑ| > M] ≤ C_U / M`
  obtain ⟨CU, hCU⟩ := erProb_exists_norm_gt_le (q := q) hd hs0.le hρ
    (fun n hn t ht => hmom n hn t (TransferAux.tube_mono h4ρ ht))
  -- the compensated cycle model on `L`
  obtain ⟨C₀, σ, hσ0, hσsum, hEsum, hW⟩ :=
    cycleModel_bounds hq hd (TransferAux.isCompact_tube s (3 * ρ)) hLD
  have hlam : ∀ (k : ℕ) (i : Fin k), 0 ≤ cycleMean d i := fun k i => by
    unfold cycleMean
    positivity
  have hpe : ∀ i, 0 ≤ poisExp (cycleMean d i) (σ i) := fun i =>
    tsum_nonneg fun j => mul_nonneg (poisPMF_nonneg (by unfold cycleMean; positivity) j) (hσ0 i j)
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = ∑' i, poisExp (cycleMean d i) (σ i) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := hE ▸ tsum_nonneg hpe
  have hn0 : ∀ᶠ n : ℕ in atTop, d ≤ n := by
    filter_upwards [eventually_ge_atTop ⌈d⌉₊] with n hn
    exact (Nat.le_ceil d).trans (by exact_mod_cast hn)
  -- the bad event has probability tending to `0`
  have hbad : Tendsto (fun n : ℕ => erProb n (d / n)
      {G | ∃ t ∈ tube s ρ, (zhat G q).eval t = 0}) atTop (𝓝 0) := by
    refine TransferAux.tendsto_zero_of_eventually_le ?_ ?_
    · filter_upwards [hn0] with n hn
      obtain ⟨hp0, hp1⟩ := div_natCast_mem_Icc hd.le hn
      exact erProb_nonneg hp0 hp1 _
    intro η hη
    -- the parameters `Y`, `M`, `ε`, `k`
    obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = E / η + 1 := ⟨_, rfl⟩
    have hY0 : 0 < Y := by
      have := div_nonneg hE0 hη.le
      rw [hY]
      linarith
    have hEY : E / Y ≤ η := by
      rw [div_le_iff₀ hY0, hY, mul_add, mul_div_cancel₀ _ hη.ne', mul_one]
      linarith
    obtain ⟨M, hM⟩ : ∃ M : ℝ, M = max 1 (max (CU / η) (Real.exp (C₀ + Y))) := ⟨_, rfl⟩
    have hM0 : 0 < M := by
      rw [hM]
      exact lt_of_lt_of_le one_pos (le_max_left _ _)
    have hCUM : CU / M ≤ η := by
      rw [div_le_iff₀ hM0]
      have h1 : CU / η ≤ M := by
        rw [hM]
        exact (le_max_left _ _).trans (le_max_right _ _)
      calc CU = η * (CU / η) := (mul_div_cancel₀ _ hη.ne').symm
        _ ≤ η * M := mul_le_mul_of_nonneg_left h1 hη.le
    have hlogM : C₀ + Y ≤ Real.log M := by
      have h1 : Real.exp (C₀ + Y) ≤ M := by
        rw [hM]
        exact (le_max_right _ _).trans (le_max_right _ _)
      calc C₀ + Y = Real.log (Real.exp (C₀ + Y)) := (Real.log_exp _).symm
        _ ≤ Real.log M := Real.log_le_log (Real.exp_pos _) h1
    have hε : 0 < Real.exp (-C₀ - Y) / (2 * M) := by positivity
    obtain ⟨k, hk⟩ := exists_norm_le_of_isBigO_pow hs0.le hρ hε
    have h𝔅 := TransferAux.badSet_subset hq hd hρ hM0 hOD hlogM hW hk
    -- the Poisson probability of `𝔅` is at most `η`
    have hpois : poisProb (fun i : Fin k => cycleMean d i) (TransferAux.badSet q s ρ M k) ≤ η := by
      have hfin : ∑ i : Fin k, poisExp (cycleMean d i) (σ i) ≤ E := by
        rw [hE]
        exact (Fin.sum_univ_eq_sum_range (fun i => poisExp (cycleMean d i) (σ i)) k).le.trans
          (hEsum.sum_le_tsum _ fun i _ => hpe i)
      calc poisProb (fun i : Fin k => cycleMean d i) (TransferAux.badSet q s ρ M k)
          ≤ poisProb (fun i : Fin k => cycleMean d i) {x | Y ≤ ∑ i : Fin k, σ i (x i)} :=
            poisProb_mono (hlam k) h𝔅
        _ ≤ (∑ i : Fin k, poisExp (cycleMean d i) (σ i)) / Y :=
            poisProb_le_of_sum (hlam k) (fun i : Fin k => σ i) (fun i j => hσ0 i j)
              (fun i => hσsum i) hY0
        _ ≤ E / Y := div_le_div_of_nonneg_right hfin hY0.le
        _ ≤ η := hEY
    have hA1 := (tendsto_order.1 (tendsto_erProb_hasDenseSubgraph hd (2 * (k + 2)))).2 η hη
    have hA3 := TransferAux.eventually_erProb_cycleCounts_mem_le hd k
      (TransferAux.badSet q s ρ M k) hη
    filter_upwards [hA1, hA3, hn0] with n h1 h3 hn
    obtain ⟨hp0, hp1⟩ := div_natCast_mem_Icc hd.le hn
    have h2 := hCU M hM0 n hn
    have hsub : {G : SimpleGraph (Fin n) | ∃ t ∈ tube s ρ, (zhat G q).eval t = 0} ⊆
        ({G | HasDenseSubgraph G (2 * (k + 2))} ∪
          {G | ∃ t ∈ tube s (3 * ρ), M < ‖(zhat G q).eval t‖}) ∪
          {G | cycleCounts k G ∈ TransferAux.badSet q s ρ M k} := by
      rintro G ⟨t₀, ht₀, hz⟩
      by_cases hD : HasDenseSubgraph G (2 * (k + 2))
      · exact Or.inl (Or.inl hD)
      by_cases hS : ∃ t ∈ tube s (3 * ρ), M < ‖(zhat G q).eval t‖
      · exact Or.inl (Or.inr hS)
      refine Or.inr ⟨fun t => (zhat G q).eval t, (zhat G q).differentiableOn, ?_,
        ⟨t₀, ht₀, hz⟩, TransferAux.zhat_sub_cyclePoly_isBigO hq k G hD⟩
      intro t ht
      by_contra hlt
      exact hS ⟨t, ht, lt_of_not_ge hlt⟩
    calc erProb n (d / n) {G | ∃ t ∈ tube s ρ, (zhat G q).eval t = 0}
        ≤ erProb n (d / n) (({G | HasDenseSubgraph G (2 * (k + 2))} ∪
          {G | ∃ t ∈ tube s (3 * ρ), M < ‖(zhat G q).eval t‖}) ∪
          {G | cycleCounts k G ∈ TransferAux.badSet q s ρ M k}) := erProb_mono hp0 hp1 hsub
      _ ≤ erProb n (d / n) ({G | HasDenseSubgraph G (2 * (k + 2))} ∪
          {G | ∃ t ∈ tube s (3 * ρ), M < ‖(zhat G q).eval t‖}) +
          erProb n (d / n) {G | cycleCounts k G ∈ TransferAux.badSet q s ρ M k} :=
            erProb_union_le hp0 hp1 _ _
      _ ≤ (erProb n (d / n) {G | HasDenseSubgraph G (2 * (k + 2))} +
          erProb n (d / n) {G | ∃ t ∈ tube s (3 * ρ), M < ‖(zhat G q).eval t‖}) +
          erProb n (d / n) {G | cycleCounts k G ∈ TransferAux.badSet q s ρ M k} := by
            have := erProb_union_le hp0 hp1 {G : SimpleGraph (Fin n) |
              HasDenseSubgraph G (2 * (k + 2))}
              {G | ∃ t ∈ tube s (3 * ρ), M < ‖(zhat G q).eval t‖}
            linarith
      _ ≤ (η + η) + (η + η) :=
            add_le_add (add_le_add h1.le (h2.trans hCUM)) (by linarith [h3, hpois])
      _ = 4 * η := by ring
  -- pass to the complement
  have hcompl : ∀ n : ℕ, erProb n (d / n) {G | ∀ t ∈ tube s ρ, (zhat G q).eval t ≠ 0} =
      1 - erProb n (d / n) {G | ∃ t ∈ tube s ρ, (zhat G q).eval t = 0} := by
    intro n
    rw [← erProb_compl]
    congr 1
    ext G
    constructor
    · rintro hG ⟨t, ht, hz⟩
      exact hG t ht hz
    · intro hG t ht hz
      exact hG ⟨t, ht, hz⟩
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub hbad
  rw [sub_zero] at hlim
  exact hlim.congr fun n => (hcompl n).symm

end

end ERZeroFreeness
