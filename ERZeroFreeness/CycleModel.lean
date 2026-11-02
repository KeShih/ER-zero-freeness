/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs
import ERZeroFreeness.Poisson

/-!
# The compensated cycle model (Lemma 3.3, `lem:cycle-general`, finite form)

For `x : Fin r → ℕ` (in place of the Poisson cycle counts `P_3, …, P_{r+2}`), the compensated
finite cycle product is (`cycleModel`, with `Q_{r+2} = cyclePoly`)
`W_{r+2}(t;x) = Q_{r+2}(t;x) · exp(-(q-1)/2 [log(1-dt) + ∑_{ℓ ≤ r+2} (dt)^ℓ/ℓ])`.

The paper passes to the almost-sure limit `𝒲 = lim_m 𝒲_m`; here the finite products are used
directly, through three properties:

* `cycleModel_differentiableOn`: `W_{r+2}(·;x)` is holomorphic on the domain `𝒟`
  (`cycleDomain`);
* `cycleModel_sub_cyclePoly_isBigO`: `W_{r+2} - Q_{r+2} = O(t^{r+3})` at `0`, so `W_{r+2}` and
  `Q_{r+2}` have the same Taylor coefficients at `0` through degree `r+2`;
* `cycleModel_bounds`: on a compact `L ⊆ 𝒟`, uniformly in `r` and `x`,
  `exp(-C₀ - ∑_i σ_i(x_i)) ≤ |W_{r+2}(t;x)| ≤ exp(C₀ + ∑_i σ_i(x_i))`, where
  `∑_i E σ_i(P_i) < ∞` for `P_i ∼ Pois(λ_{i+3})`.

Proof.  On `𝒟`, `1 + (q-1)t^ℓ ≠ 0` for `ℓ ≥ 3`, so
`|W(t)| = exp(Re F(t) + ∑_{i<r} Re τ_i(t; x_i))` with
`F(t) = -(q-1)/2 [log(1-dt) + dt + (dt)²/2]` and
`τ_i(t;k) = k log(1 + (q-1)t^{ℓ}) - (q-1)(dt)^ℓ/(2ℓ)`, `ℓ = i+3`,
using `λ_ℓ (q-1) t^ℓ = (q-1)(dt)^ℓ/(2ℓ)`.  For `T = max_L |t|`, `c = (q-1)T³ < 1`,
`Complex.norm_log_one_add_sub_self_le` gives
`|τ_i(t;k)| ≤ σ_i(k) := k (q-1)² T^{2ℓ} / (2(1-c)) + |k - λ_ℓ| (q-1) T^ℓ`, and `C₀` is a bound
for `|F|` on `L`.  `E σ_i(P) ≤ (q-1)² (dT²)^ℓ/(4ℓ(1-c)) + (q-1) T^ℓ √λ_ℓ`
(`poisExp_abs_sub_le`), summable since `dT² < 1`.  Near `0`,
`log(1-dt) + ∑_{ℓ ≤ r+2} (dt)^ℓ/ℓ = O(t^{r+3})` (`Complex.log_sub_logTaylor_isBigO` at `-dt`),
`|e^w - 1| ≤ 2|w|` for `|w| ≤ 1` (`Complex.norm_exp_sub_one_le`), and `Q_{r+2}` is bounded.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-! ### Helpers for the compensated cycle model -/

/-- The exponent `-(q-1)/2 · [log(1-dt) + ∑_{ℓ=1}^{r+2} (dt)^ℓ/ℓ]` of the compensating factor. -/
private def cmExpo (q : ℕ) (d : ℝ) (r : ℕ) (t : ℂ) : ℂ :=
  -(((q : ℂ) - 1) / 2) *
    (Complex.log (1 - (d : ℂ) * t) +
      ∑ l ∈ Finset.range (r + 2), ((d : ℂ) * t) ^ (l + 1) / ((l : ℂ) + 1))

/-- The deterministic part `F(t) = -(q-1)/2 · [log(1-dt) + dt + (dt)²/2]`. -/
private def cmF (q : ℕ) (d : ℝ) (t : ℂ) : ℂ :=
  -(((q : ℂ) - 1) / 2) * (Complex.log (1 - (d : ℂ) * t) + (d : ℂ) * t + ((d : ℂ) * t) ^ 2 / 2)

/-- The cycle variable `a_i(t) = (q-1) t^{i+3}`. -/
private def cmA (q : ℕ) (t : ℂ) (i : ℕ) : ℂ := ((q : ℂ) - 1) * t ^ (i + 3)

/-- `τ_i(t;k) = k log(1 + a_i(t)) - λ_{i+3} a_i(t)`. -/
private def cmTau (q : ℕ) (d : ℝ) (t : ℂ) (i k : ℕ) : ℂ :=
  (k : ℂ) * Complex.log (1 + cmA q t i) - ((cycleMean d i : ℝ) : ℂ) * cmA q t i

private lemma cm_cycleModel_eq_mul_exp (q : ℕ) (d : ℝ) (r : ℕ) (x : Fin r → ℕ) (t : ℂ) :
    cycleModel q d r x t = (cyclePoly q r x).eval t * Complex.exp (cmExpo q d r t) := rfl

private lemma cm_cmExpo_eq (q : ℕ) (d : ℝ) (r : ℕ) (t : ℂ) :
    cmExpo q d r t = cmF q d t - ∑ i : Fin r, ((cycleMean d i : ℝ) : ℂ) * cmA q t i := by
  have key : ∀ i : ℕ, ((cycleMean d i : ℝ) : ℂ) * cmA q t i =
      ((q : ℂ) - 1) / 2 * (((d : ℂ) * t) ^ (i + 2 + 1) / (((i + 2 : ℕ) : ℂ) + 1)) := by
    intro i
    have e1 : ((cycleMean d i : ℝ) : ℂ) = (d : ℂ) ^ (i + 3) * (2 : ℂ)⁻¹ * ((i : ℂ) + 3)⁻¹ := by
      simp only [cycleMean]
      push_cast
      rw [div_eq_mul_inv, mul_inv]
      ring
    have e2 : (((i + 2 : ℕ) : ℂ) + 1) = (i : ℂ) + 3 := by push_cast; ring
    rw [e1, e2, cmA, div_eq_mul_inv _ ((i : ℂ) + 3)]
    ring
  rw [Fin.sum_univ_eq_sum_range (fun i => ((cycleMean d i : ℝ) : ℂ) * cmA q t i)]
  simp only [key, ← Finset.mul_sum]
  simp only [cmExpo, cmF, Finset.sum_range_succ' _ (r + 1), Finset.sum_range_succ' _ r]
  push_cast
  ring_nf

private lemma cm_norm_q_sub_one {q : ℕ} (hq : 1 ≤ q) : ‖((q : ℂ) - 1)‖ = (q : ℝ) - 1 := by
  have h : ((q : ℂ) - 1) = (((q : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  rw [h, Complex.norm_of_nonneg (by linarith)]

private lemma cm_norm_cmA {q : ℕ} (hq : 1 ≤ q) (t : ℂ) (i : ℕ) :
    ‖cmA q t i‖ = ((q : ℝ) - 1) * ‖t‖ ^ (i + 3) := by
  rw [cmA, norm_mul, norm_pow, cm_norm_q_sub_one hq]

private lemma cm_norm_cmA_le {q : ℕ} (hq : 1 ≤ q) {T : ℝ} (hT1 : T ≤ 1) {t : ℂ} (ht : ‖t‖ ≤ T)
    (i : ℕ) : ‖cmA q t i‖ ≤ ((q : ℝ) - 1) * T ^ (i + 3) ∧
      ((q : ℝ) - 1) * T ^ (i + 3) ≤ ((q : ℝ) - 1) * T ^ 3 := by
  have hq' : (0 : ℝ) ≤ (q : ℝ) - 1 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hT0 : 0 ≤ T := (norm_nonneg t).trans ht
  rw [cm_norm_cmA hq]
  constructor
  · gcongr
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hT0 hT1 (by omega)) hq'

private lemma cm_one_add_cmA_ne_zero {q : ℕ} (hq : 1 ≤ q) {t : ℂ} (ht1 : ‖t‖ < 1)
    (htq : ((q : ℝ) - 1) * ‖t‖ ^ 3 < 1) (i : ℕ) : 1 + cmA q t i ≠ 0 := by
  have h := cm_norm_cmA_le hq ht1.le le_rfl i
  have hlt : ‖cmA q t i‖ < 1 := lt_of_le_of_lt (h.1.trans h.2) htq
  intro h0
  have : cmA q t i = -1 := by linear_combination h0
  rw [this, norm_neg, norm_one] at hlt
  exact lt_irrefl _ hlt

private lemma cm_cycleModel_eq_exp {q : ℕ} (hq : 1 ≤ q) (d : ℝ) (r : ℕ) (x : Fin r → ℕ) {t : ℂ}
    (ht1 : ‖t‖ < 1) (htq : ((q : ℝ) - 1) * ‖t‖ ^ 3 < 1) :
    cycleModel q d r x t = Complex.exp (cmF q d t + ∑ i : Fin r, cmTau q d t i (x i)) := by
  have hP : (cyclePoly q r x).eval t =
      Complex.exp (∑ i : Fin r, (x i : ℂ) * Complex.log (1 + cmA q t i)) := by
    rw [Complex.exp_sum]
    simp only [cyclePoly, eval_prod, eval_pow, eval_add, eval_one, eval_mul, eval_C, eval_X]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.exp_nat_mul, Complex.exp_log (cm_one_add_cmA_ne_zero hq ht1 htq i)]
    rfl
  rw [cm_cycleModel_eq_mul_exp, cm_cmExpo_eq, hP, ← Complex.exp_add]
  congr 1
  simp only [cmTau, Finset.sum_sub_distrib]
  ring

/-- The majorant `σ_i(k)` of `|τ_i(t;k)|` for `|t| ≤ T` (`cm_norm_cmTau_le`). -/
private def cmSigma (q : ℕ) (d T : ℝ) (i k : ℕ) : ℝ :=
  (k : ℝ) * (((q : ℝ) - 1) ^ 2 * T ^ (2 * (i + 3)) / (2 * (1 - ((q : ℝ) - 1) * T ^ 3))) +
    |(k : ℝ) - cycleMean d i| * (((q : ℝ) - 1) * T ^ (i + 3))

private lemma cm_norm_cmTau_le {q : ℕ} (hq : 1 ≤ q) {d T : ℝ} (hT1 : T ≤ 1)
    (hc : ((q : ℝ) - 1) * T ^ 3 < 1) {t : ℂ} (ht : ‖t‖ ≤ T) (i k : ℕ) :
    ‖cmTau q d t i k‖ ≤ cmSigma q d T i k := by
  have hT0 : 0 ≤ T := (norm_nonneg t).trans ht
  set a := cmA q t i with ha_def
  obtain ⟨ha, ha'⟩ := cm_norm_cmA_le hq hT1 ht i
  have ha1 : ‖a‖ < 1 := lt_of_le_of_lt (ha.trans ha') hc
  have key : cmTau q d t i k =
      (k : ℂ) * (Complex.log (1 + a) - a) + (((k : ℝ) - cycleMean d i : ℝ) : ℂ) * a := by
    simp only [cmTau, ← ha_def]
    push_cast
    ring
  rw [key, cmSigma]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_natCast]
    gcongr
    refine (Complex.norm_log_one_add_sub_self_le ha1).trans ?_
    have h1 : 0 < 1 - ((q : ℝ) - 1) * T ^ 3 := by linarith
    have h2 : 1 - ((q : ℝ) - 1) * T ^ 3 ≤ 1 - ‖a‖ := by linarith
    have h3 : ‖a‖ ^ 2 ≤ ((q : ℝ) - 1) ^ 2 * T ^ (2 * (i + 3)) := by
      calc ‖a‖ ^ 2 ≤ (((q : ℝ) - 1) * T ^ (i + 3)) ^ 2 := by gcongr
        _ = ((q : ℝ) - 1) ^ 2 * T ^ (2 * (i + 3)) := by ring
    calc ‖a‖ ^ 2 * (1 - ‖a‖)⁻¹ / 2
        ≤ ((q : ℝ) - 1) ^ 2 * T ^ (2 * (i + 3)) * (1 - ((q : ℝ) - 1) * T ^ 3)⁻¹ / 2 := by
          gcongr
      _ = ((q : ℝ) - 1) ^ 2 * T ^ (2 * (i + 3)) / (2 * (1 - ((q : ℝ) - 1) * T ^ 3)) := by
          field_simp
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr

private lemma cm_exists_radius {q : ℕ} {d : ℝ} {L : Set ℂ} (hL : IsCompact L)
    (hLD : L ⊆ cycleDomain q d) :
    ∃ T : ℝ, 0 ≤ T ∧ T < 1 ∧ d * T ^ 2 < 1 ∧ ((q : ℝ) - 1) * T ^ 3 < 1 ∧
      ∀ t ∈ L, ‖t‖ ≤ T := by
  rcases L.eq_empty_or_nonempty with h | h
  · exact ⟨0, le_rfl, one_pos, by simp, by simp, by simp [h]⟩
  · obtain ⟨t₀, ht₀, hmax⟩ := hL.exists_isMaxOn h continuous_norm.continuousOn
    obtain ⟨h1, h2, h3, -⟩ := hLD ht₀
    exact ⟨‖t₀‖, norm_nonneg _, h1, h2, h3, fun t ht => isMaxOn_iff.mp hmax t ht⟩

private lemma cm_one_sub_mem_slitPlane {q : ℕ} {d : ℝ} {t : ℂ} (ht : t ∈ cycleDomain q d) :
    1 - (d : ℂ) * t ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl ht.2.2.2)

private lemma cm_cmF_continuousOn (q : ℕ) (d : ℝ) : ContinuousOn (cmF q d) (cycleDomain q d) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  unfold cmF
  apply ContinuousAt.mul continuousAt_const
  apply ContinuousAt.add
  · apply ContinuousAt.add
    · exact ContinuousAt.clog (by fun_prop) (cm_one_sub_mem_slitPlane ht)
    · fun_prop
  · fun_prop

private lemma cm_cycleMean_nonneg {d : ℝ} (hd : 0 ≤ d) (i : ℕ) : 0 ≤ cycleMean d i := by
  unfold cycleMean
  positivity

/-- `E σ_i(P) = A_i λ_i + B_i E|P - λ_i|` for `P ∼ Pois(λ_i)`. -/
private lemma cm_hasSum_cmSigma (q : ℕ) {d : ℝ} (hd : 0 ≤ d) (T : ℝ) (i : ℕ) :
    HasSum (fun k => poisPMF (cycleMean d i) k * cmSigma q d T i k)
      (cycleMean d i * (((q : ℝ) - 1) ^ 2 * T ^ (2 * (i + 3)) / (2 * (1 - ((q : ℝ) - 1) * T ^ 3)))
        + poisExp (cycleMean d i) (fun k => |(k : ℝ) - cycleMean d i|) *
          (((q : ℝ) - 1) * T ^ (i + 3))) := by
  have hlam := cm_cycleMean_nonneg hd i
  have h1 : HasSum (fun k => poisPMF (cycleMean d i) k * (k : ℝ)) (cycleMean d i) := by
    have hs := summable_poisPMF_mul_pow hlam 1
    simp only [pow_one] at hs
    have := hs.hasSum
    rwa [← poisExp, poisExp_natCast hlam] at this
  have h2 : HasSum (fun k => poisPMF (cycleMean d i) k * |(k : ℝ) - cycleMean d i|)
      (poisExp (cycleMean d i) (fun k => |(k : ℝ) - cycleMean d i|)) :=
    (summable_poisPMF_mul_abs_sub hlam).hasSum
  have hfun : (fun k => poisPMF (cycleMean d i) k * cmSigma q d T i k) = fun k =>
      poisPMF (cycleMean d i) k * (k : ℝ) *
          (((q : ℝ) - 1) ^ 2 * T ^ (2 * (i + 3)) / (2 * (1 - ((q : ℝ) - 1) * T ^ 3))) +
        poisPMF (cycleMean d i) k * |(k : ℝ) - cycleMean d i| * (((q : ℝ) - 1) * T ^ (i + 3)) := by
    funext k
    simp only [cmSigma]
    ring
  rw [hfun]
  exact (h1.mul_right _).add (h2.mul_right _)

private lemma cm_cmSigma_nonneg {q : ℕ} (hq : 1 ≤ q) (d : ℝ) {T : ℝ} (hT0 : 0 ≤ T)
    (hc : ((q : ℝ) - 1) * T ^ 3 < 1) (i k : ℕ) : 0 ≤ cmSigma q d T i k := by
  have hq' : (0 : ℝ) ≤ (q : ℝ) - 1 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have h1 : 0 < 1 - ((q : ℝ) - 1) * T ^ 3 := by linarith
  unfold cmSigma
  positivity

private lemma cm_sqrt_cycleMean_le {d : ℝ} (hd : 0 ≤ d) (i : ℕ) :
    Real.sqrt (cycleMean d i) ≤ Real.sqrt d ^ (i + 3) := by
  rw [Real.sqrt_le_left (by positivity), ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hd]
  unfold cycleMean
  rw [div_le_iff₀ (by positivity)]
  have : (1 : ℝ) ≤ 2 * ((i : ℝ) + 3) := by
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith
  calc d ^ (i + 3) = d ^ (i + 3) * 1 := (mul_one _).symm
    _ ≤ d ^ (i + 3) * (2 * ((i : ℝ) + 3)) := by gcongr

private lemma cm_cycleMean_le {d : ℝ} (hd : 0 ≤ d) (i : ℕ) : cycleMean d i ≤ d ^ (i + 3) := by
  unfold cycleMean
  rw [div_le_iff₀ (by positivity)]
  have : (1 : ℝ) ≤ 2 * ((i : ℝ) + 3) := by
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith
  calc d ^ (i + 3) = d ^ (i + 3) * 1 := (mul_one _).symm
    _ ≤ d ^ (i + 3) * (2 * ((i : ℝ) + 3)) := by gcongr

private lemma cm_summable_poisExp_cmSigma {q : ℕ} (hq : 1 ≤ q) {d : ℝ} (hd : 0 ≤ d) {T : ℝ}
    (hT0 : 0 ≤ T) (hdT : d * T ^ 2 < 1) (hc : ((q : ℝ) - 1) * T ^ 3 < 1) :
    Summable fun i => poisExp (cycleMean d i) (cmSigma q d T i) := by
  have hq' : (0 : ℝ) ≤ (q : ℝ) - 1 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have h1c : 0 < 1 - ((q : ℝ) - 1) * T ^ 3 := by linarith
  set c := ((q : ℝ) - 1) * T ^ 3 with hc_def
  set ρ₁ := d * T ^ 2 with hρ₁
  set ρ₂ := T * Real.sqrt d with hρ₂
  have hρ₁0 : 0 ≤ ρ₁ := by positivity
  have hρ₂0 : 0 ≤ ρ₂ := by positivity
  have hρ₂1 : ρ₂ < 1 := by
    have hsq : ρ₂ ^ 2 = ρ₁ := by
      rw [hρ₂, hρ₁, mul_pow, Real.sq_sqrt hd]
      ring
    nlinarith
  set K₁ := ((q : ℝ) - 1) ^ 2 / (2 * (1 - c)) with hK₁
  set K₂ := (q : ℝ) - 1 with hK₂
  have hK₁0 : 0 ≤ K₁ := by positivity
  refine Summable.of_nonneg_of_le (f := fun i => K₁ * ρ₁ ^ 3 * ρ₁ ^ i + K₂ * ρ₂ ^ 3 * ρ₂ ^ i)
    (fun i => ?_) (fun i => ?_) ?_
  · exact tsum_nonneg fun k => mul_nonneg (poisPMF_nonneg (cm_cycleMean_nonneg hd i) k)
      (cm_cmSigma_nonneg hq d hT0 hc i k)
  · have hlam := cm_cycleMean_nonneg hd i
    rw [poisExp, (cm_hasSum_cmSigma q hd T i).tsum_eq]
    have hE := poisExp_abs_sub_le hlam
    have hB : 0 ≤ ((q : ℝ) - 1) * T ^ (i + 3) := by positivity
    have hA : 0 ≤ ((q : ℝ) - 1) ^ 2 * T ^ (2 * (i + 3)) / (2 * (1 - c)) := by positivity
    calc cycleMean d i * (((q : ℝ) - 1) ^ 2 * T ^ (2 * (i + 3)) / (2 * (1 - c)))
          + poisExp (cycleMean d i) (fun k => |(k : ℝ) - cycleMean d i|) *
            (((q : ℝ) - 1) * T ^ (i + 3))
        ≤ d ^ (i + 3) * (((q : ℝ) - 1) ^ 2 * T ^ (2 * (i + 3)) / (2 * (1 - c)))
          + Real.sqrt d ^ (i + 3) * (((q : ℝ) - 1) * T ^ (i + 3)) := by
          gcongr
          · exact cm_cycleMean_le hd i
          · exact hE.trans (cm_sqrt_cycleMean_le hd i)
      _ = K₁ * ρ₁ ^ 3 * ρ₁ ^ i + K₂ * ρ₂ ^ 3 * ρ₂ ^ i := by
          rw [hK₁, hK₂, hρ₁, hρ₂]
          ring
  · exact ((summable_geometric_of_lt_one hρ₁0 (by linarith)).mul_left (K₁ * ρ₁ ^ 3)).add
      ((summable_geometric_of_lt_one hρ₂0 hρ₂1).mul_left (K₂ * ρ₂ ^ 3))

/-- Mathlib's Taylor polynomial of `log(1+w)` at `w = -z`:
`logTaylor (n+1) (-z) = -∑_{ℓ=1}^{n} z^ℓ/ℓ`. -/
private lemma cm_logTaylor_neg_eq (n : ℕ) (z : ℂ) :
    Complex.logTaylor (n + 1) (-z) = -∑ l ∈ Finset.range n, z ^ (l + 1) / ((l : ℂ) + 1) := by
  rw [Complex.logTaylor, Finset.sum_range_succ', ← Finset.sum_neg_distrib]
  simp only [pow_zero, CharP.cast_eq_zero, div_zero, add_zero, Nat.cast_add, Nat.cast_one]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [neg_pow z, ← mul_assoc, ← pow_add,
    (show Odd (l + 1 + 1 + (l + 1)) from ⟨l + 1, by ring⟩).neg_one_pow]
  ring

private lemma cm_log_partial_isBigO (d : ℝ) (r : ℕ) :
    (fun t : ℂ => Complex.log (1 - (d : ℂ) * t) +
        ∑ l ∈ Finset.range (r + 2), ((d : ℂ) * t) ^ (l + 1) / ((l : ℂ) + 1)) =O[𝓝 0]
      fun t => t ^ (r + 3) := by
  have hk : Tendsto (fun t : ℂ => -((d : ℂ) * t)) (𝓝 0) (𝓝 0) := by
    have : Continuous (fun t : ℂ => -((d : ℂ) * t)) := by fun_prop
    simpa using this.tendsto 0
  have h1 := (Complex.log_sub_logTaylor_isBigO (r + 2)).comp_tendsto hk
  have h2 : (fun t : ℂ => (-((d : ℂ) * t)) ^ (r + 2 + 1)) =O[𝓝 0] fun t => t ^ (r + 3) := by
    have : (fun t : ℂ => (-((d : ℂ) * t)) ^ (r + 2 + 1)) =
        fun t => (-(d : ℂ)) ^ (r + 3) * t ^ (r + 3) := by
      funext t
      ring
    rw [this]
    exact Asymptotics.isBigO_const_mul_self _ _ _
  refine (h1.trans h2).congr_left fun t => ?_
  simp only [Function.comp, cm_logTaylor_neg_eq, sub_neg_eq_add, ← sub_eq_add_neg]

/-- The domain `𝒟` of the compensated cycle model is open. -/
theorem isOpen_cycleDomain (q : ℕ) (d : ℝ) : IsOpen (cycleDomain q d) := by
  unfold cycleDomain
  refine (isOpen_lt (by fun_prop) (by fun_prop)).and
    ((isOpen_lt (by fun_prop) (by fun_prop)).and
      ((isOpen_lt (by fun_prop) (by fun_prop)).and (isOpen_lt (by fun_prop) (by fun_prop))))

/-- `W_{r+2}(·;x)` is holomorphic on `𝒟`. -/
theorem cycleModel_differentiableOn {q : ℕ} (hq : 2 ≤ q) {d : ℝ} (hd : 0 < d) (r : ℕ)
    (x : Fin r → ℕ) : DifferentiableOn ℂ (cycleModel q d r x) (cycleDomain q d) := by
  intro t ht
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold cycleModel
  refine ((cyclePoly q r x).differentiable t).mul ?_
  refine DifferentiableAt.cexp ?_
  refine DifferentiableAt.const_mul ?_ _
  refine DifferentiableAt.add ?_ ?_
  · exact DifferentiableAt.clog (by fun_prop) (cm_one_sub_mem_slitPlane ht)
  · fun_prop

/-- `W_{r+2}` and `Q_{r+2}` have the same Taylor coefficients at `0` through degree `r+2`. -/
theorem cycleModel_sub_cyclePoly_isBigO {q : ℕ} (hq : 2 ≤ q) {d : ℝ} (hd : 0 < d) (r : ℕ)
    (x : Fin r → ℕ) :
    (fun t => cycleModel q d r x t - (cyclePoly q r x).eval t) =O[𝓝 0] fun t => t ^ (r + 3) := by
  have hEO : (fun t => cmExpo q d r t) =O[𝓝 0] fun t => t ^ (r + 3) :=
    (cm_log_partial_isBigO d r).const_mul_left _
  have hpow : Tendsto (fun t : ℂ => t ^ (r + 3)) (𝓝 0) (𝓝 0) := by
    have := ((continuous_pow (r + 3) : Continuous fun t : ℂ => t ^ (r + 3)).tendsto 0)
    simpa using this
  have hE0 : Tendsto (fun t => cmExpo q d r t) (𝓝 0) (𝓝 0) := hEO.trans_tendsto hpow
  have hexp : (fun t => Complex.exp (cmExpo q d r t) - 1) =O[𝓝 0] fun t => cmExpo q d r t := by
    refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [hE0.eventually (Metric.closedBall_mem_nhds (0 : ℂ) one_pos)] with t ht
    exact Complex.norm_exp_sub_one_le (mem_closedBall_zero_iff.mp ht)
  have hP : (fun t => (cyclePoly q r x).eval t) =O[𝓝 0] fun _ => (1 : ℂ) :=
    ((cyclePoly q r x).continuous.tendsto 0).isBigO_one ℂ
  refine (hP.mul (hexp.trans hEO)).congr (fun t => ?_) (fun t => one_mul _)
  rw [cm_cycleModel_eq_mul_exp]
  ring

/-- Two-sided bounds on `|W_{r+2}|` on a compact subset of `𝒟`, uniform in `r`, by a
random variable `∑_i σ_i(x_i)` whose Poisson expectations are summable. -/
theorem cycleModel_bounds {q : ℕ} (hq : 2 ≤ q) {d : ℝ} (hd : 0 < d) {L : Set ℂ}
    (hL : IsCompact L) (hLD : L ⊆ cycleDomain q d) :
    ∃ (C₀ : ℝ) (σ : ℕ → ℕ → ℝ), (∀ i k, 0 ≤ σ i k) ∧
      (∀ i, Summable fun k => poisPMF (cycleMean d i) k * σ i k) ∧
      (Summable fun i => poisExp (cycleMean d i) (σ i)) ∧
      ∀ (r : ℕ) (x : Fin r → ℕ), ∀ t ∈ L,
        Real.exp (-C₀ - ∑ i : Fin r, σ i (x i)) ≤ ‖cycleModel q d r x t‖ ∧
          ‖cycleModel q d r x t‖ ≤ Real.exp (C₀ + ∑ i : Fin r, σ i (x i)) := by
  have hq1 : 1 ≤ q := by omega
  obtain ⟨T, hT0, hT1, hdT, hcT, hLT⟩ := cm_exists_radius hL hLD
  obtain ⟨C₀, hC₀⟩ := hL.exists_bound_of_continuousOn ((cm_cmF_continuousOn q d).mono hLD)
  refine ⟨C₀, cmSigma q d T, cm_cmSigma_nonneg hq1 d hT0 hcT, fun i => ?_,
    cm_summable_poisExp_cmSigma hq1 hd.le hT0 hdT hcT, ?_⟩
  · exact (cm_hasSum_cmSigma q hd.le T i).summable
  · intro r x t ht
    obtain ⟨ht1, -, htq, -⟩ := hLD ht
    have hnorm : ‖cycleModel q d r x t‖ =
        Real.exp ((cmF q d t).re + ∑ i : Fin r, (cmTau q d t i (x i)).re) := by
      rw [cm_cycleModel_eq_exp hq1 d r x ht1 htq, Complex.norm_exp, Complex.add_re, Complex.re_sum]
    have hF : |(cmF q d t).re| ≤ C₀ := (Complex.abs_re_le_norm _).trans (hC₀ t ht)
    have hsum : |∑ i : Fin r, (cmTau q d t i (x i)).re| ≤ ∑ i : Fin r, cmSigma q d T i (x i) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
        (Complex.abs_re_le_norm _).trans (cm_norm_cmTau_le hq1 hT1.le hcT (hLT t ht) i (x i)))
    rw [hnorm]
    obtain ⟨hF1, hF2⟩ := abs_le.mp hF
    obtain ⟨hs1, hs2⟩ := abs_le.mp hsum
    constructor
    · exact Real.exp_le_exp.mpr (by linarith)
    · exact Real.exp_le_exp.mpr (by linarith)

end

end ERZeroFreeness
