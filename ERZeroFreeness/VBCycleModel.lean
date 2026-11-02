/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.IsingVBDefs
import ERZeroFreeness.Poisson

/-!
# The signed finite cycle model

Two-sided bounds for the signed finite cycle product
`Q^{sg}_{r+2}(t; x) = ∏_{ℓ=3}^{r+2} (1 + t^ℓ)^{x^+_ℓ} (1 - t^ℓ)^{x^-_ℓ}` on a closed disk
`|t| ≤ R` with `R < 1` and `dR² < 1`, uniform in the truncation `r` (Step 3 of Section 7).

* `sgCyclePoly_eval_eq_exp`: for `|t| < 1`, `Q^{sg}_{r+2}(t; x)` is the exponential of
  `∑_ℓ (x^+_ℓ log(1 + t^ℓ) + x^-_ℓ log(1 - t^ℓ))` (principal logarithm).
* `norm_signedLog_le`: the linear terms cancel up to the centred counts,
  `|k₁ log(1+a) + k₂ log(1-a)| ≤ (|k₁ - μ| + |k₂ - μ|) |a| + (k₁ + k₂) |a|² / (2(1 - |a|))`.
* `sgCyclePoly_bounds`: `e^{-Σ(x)} ≤ |Q^{sg}_{r+2}(t; x)| ≤ e^{Σ(x)}` on `|t| ≤ R`, where
  `Σ(x) = ∑_i (σ_i(x^+_{i+3}) + σ_i(x^-_{i+3}))` and `∑_i E σ_i(P_i) < ∞` for
  `P_i ∼ Pois(λ_{i+3}/2)`.  Since `P^+_ℓ` and `P^-_ℓ` have the same mean, the centring needs no
  exponential compensation.

These finite products, with bounds uniform in `r`, take the place of the paper's random
holomorphic limit function on the disk `|t| < r_d`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-! ### The principal logarithm of the factors -/

/-- `‖t^m‖ < 1` for `‖t‖ < 1` and `m ≥ 1`. -/
private lemma VBCycleModel_norm_pow_lt_one {t : ℂ} (ht : ‖t‖ < 1) {m : ℕ} (hm : m ≠ 0) :
    ‖t ^ m‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg t) ht hm

/-- `1 + a ≠ 0` for `‖a‖ < 1`. -/
private lemma VBCycleModel_one_add_ne_zero {a : ℂ} (ha : ‖a‖ < 1) : 1 + a ≠ 0 := by
  intro h0
  have : a = -1 := by linear_combination h0
  rw [this, norm_neg, norm_one] at ha
  exact lt_irrefl _ ha

/-- `1 - a ≠ 0` for `‖a‖ < 1`. -/
private lemma VBCycleModel_one_sub_ne_zero {a : ℂ} (ha : ‖a‖ < 1) : 1 - a ≠ 0 := by
  intro h0
  have : a = 1 := by linear_combination -h0
  rw [this, norm_one] at ha
  exact lt_irrefl _ ha

/-- Principal-logarithm representation of `Q^{sg}_{r+2}` on the open unit disk. -/
theorem sgCyclePoly_eval_eq_exp (r : ℕ) (x : Fin (r + r) → ℕ) {t : ℂ} (ht : ‖t‖ < 1) :
    (sgCyclePoly r x).eval t = Complex.exp (∑ i : Fin r,
      ((x (Fin.castAdd r i) : ℂ) * Complex.log (1 + t ^ (i.1 + 3)) +
        (x (Fin.natAdd r i) : ℂ) * Complex.log (1 - t ^ (i.1 + 3)))) := by
  rw [Complex.exp_sum]
  simp only [sgCyclePoly, eval_prod, eval_mul, eval_pow, eval_add, eval_sub, eval_one, eval_X]
  refine Finset.prod_congr rfl fun i _ => ?_
  have ha : ‖t ^ (i.1 + 3)‖ < 1 := VBCycleModel_norm_pow_lt_one ht (by omega)
  rw [Complex.exp_add, Complex.exp_nat_mul, Complex.exp_nat_mul,
    Complex.exp_log (VBCycleModel_one_add_ne_zero ha),
    Complex.exp_log (VBCycleModel_one_sub_ne_zero ha)]

/-- The linear terms cancel up to the centred counts: for `|a| < 1` and every `μ`,
`|k₁ log(1+a) + k₂ log(1-a)| ≤ (|k₁ - μ| + |k₂ - μ|) |a| + (k₁ + k₂) |a|² / (2(1 - |a|))`. -/
theorem norm_signedLog_le {a : ℂ} (ha : ‖a‖ < 1) (k₁ k₂ : ℕ) (μ : ℝ) :
    ‖(k₁ : ℂ) * Complex.log (1 + a) + (k₂ : ℂ) * Complex.log (1 - a)‖ ≤
      (|(k₁ : ℝ) - μ| + |(k₂ : ℝ) - μ|) * ‖a‖ +
        ((k₁ : ℝ) + k₂) * (‖a‖ ^ 2 * (1 - ‖a‖)⁻¹ / 2) := by
  set B : ℝ := ‖a‖ ^ 2 * (1 - ‖a‖)⁻¹ / 2 with hB
  have ha' : ‖-a‖ < 1 := by rwa [norm_neg]
  have h1 : ‖Complex.log (1 + a) - a‖ ≤ B := Complex.norm_log_one_add_sub_self_le ha
  have h2 : ‖Complex.log (1 - a) + a‖ ≤ B := by
    have := Complex.norm_log_one_add_sub_self_le ha'
    rw [norm_neg, ← sub_eq_add_neg, sub_neg_eq_add] at this
    exact this
  have key : (k₁ : ℂ) * Complex.log (1 + a) + (k₂ : ℂ) * Complex.log (1 - a) =
      ((((k₁ : ℝ) - μ : ℝ) : ℂ) - (((k₂ : ℝ) - μ : ℝ) : ℂ)) * a +
        ((k₁ : ℂ) * (Complex.log (1 + a) - a) + (k₂ : ℂ) * (Complex.log (1 - a) + a)) := by
    push_cast
    ring
  rw [key]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    gcongr
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  · refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast, add_mul]
    gcongr

/-! ### Helpers for `sgCyclePoly_bounds` -/

/-- `σ_i(k) = |k - μ_i| R^{i+3} + k R^{2(i+3)} (1-R)⁻¹/2`, with `μ_i = λ_{i+3}/2`. -/
private def VBCycleModel_sigma (d R : ℝ) (i k : ℕ) : ℝ :=
  |(k : ℝ) - cycleMean d i / 2| * R ^ (i + 3) + (k : ℝ) * (R ^ (2 * (i + 3)) * (1 - R)⁻¹ / 2)

private lemma VBCycleModel_sigma_nonneg (d : ℝ) {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) (i k : ℕ) :
    0 ≤ VBCycleModel_sigma d R i k := by
  have : 0 < 1 - R := by linarith
  unfold VBCycleModel_sigma
  positivity

private lemma VBCycleModel_mu_nonneg {d : ℝ} (hd : 0 ≤ d) (i : ℕ) : 0 ≤ cycleMean d i / 2 := by
  unfold cycleMean
  positivity

/-- `μ_i = λ_{i+3}/2 ≤ d^{i+3}`. -/
private lemma VBCycleModel_mu_le {d : ℝ} (hd : 0 ≤ d) (i : ℕ) :
    cycleMean d i / 2 ≤ d ^ (i + 3) := by
  have hdi : 0 ≤ d ^ (i + 3) := by positivity
  have h1 : (1 : ℝ) ≤ 2 * ((i : ℝ) + 3) := by
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith
  have h2 : cycleMean d i ≤ d ^ (i + 3) := by
    unfold cycleMean
    rw [div_le_iff₀ (by positivity)]
    calc d ^ (i + 3) = d ^ (i + 3) * 1 := (mul_one _).symm
      _ ≤ d ^ (i + 3) * (2 * ((i : ℝ) + 3)) := by gcongr
  have h3 : 0 ≤ cycleMean d i := by unfold cycleMean; positivity
  linarith

/-- `√μ_i ≤ (√d)^{i+3}`. -/
private lemma VBCycleModel_sqrt_mu_le {d : ℝ} (hd : 0 ≤ d) (i : ℕ) :
    Real.sqrt (cycleMean d i / 2) ≤ Real.sqrt d ^ (i + 3) := by
  rw [Real.sqrt_le_left (by positivity)]
  have : (Real.sqrt d ^ (i + 3)) ^ 2 = d ^ (i + 3) := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hd]
  rw [this]
  exact VBCycleModel_mu_le hd i

/-- `E σ_i(P) = E|P - μ_i| R^{i+3} + μ_i R^{2(i+3)}(1-R)⁻¹/2` for `P ∼ Pois(μ_i)`. -/
private lemma VBCycleModel_hasSum_sigma {d : ℝ} (hd : 0 ≤ d) (R : ℝ) (i : ℕ) :
    HasSum (fun k => poisPMF (cycleMean d i / 2) k * VBCycleModel_sigma d R i k)
      (poisExp (cycleMean d i / 2) (fun k => |(k : ℝ) - cycleMean d i / 2|) * R ^ (i + 3) +
        cycleMean d i / 2 * (R ^ (2 * (i + 3)) * (1 - R)⁻¹ / 2)) := by
  have hlam := VBCycleModel_mu_nonneg hd i
  have h1 : HasSum (fun k => poisPMF (cycleMean d i / 2) k * (k : ℝ)) (cycleMean d i / 2) := by
    have hs : Summable fun k => poisPMF (cycleMean d i / 2) k * (k : ℝ) := by
      simpa only [pow_one] using summable_poisPMF_mul_pow hlam 1
    have e : ∑' k, poisPMF (cycleMean d i / 2) k * (k : ℝ) = cycleMean d i / 2 :=
      poisExp_natCast hlam
    have := hs.hasSum
    rwa [e] at this
  have h2 : HasSum (fun k => poisPMF (cycleMean d i / 2) k * |(k : ℝ) - cycleMean d i / 2|)
      (poisExp (cycleMean d i / 2) (fun k => |(k : ℝ) - cycleMean d i / 2|)) :=
    (summable_poisPMF_mul_abs_sub hlam).hasSum
  have hfun : (fun k => poisPMF (cycleMean d i / 2) k * VBCycleModel_sigma d R i k) = fun k =>
      poisPMF (cycleMean d i / 2) k * |(k : ℝ) - cycleMean d i / 2| * R ^ (i + 3) +
        poisPMF (cycleMean d i / 2) k * (k : ℝ) * (R ^ (2 * (i + 3)) * (1 - R)⁻¹ / 2) := by
    funext k
    simp only [VBCycleModel_sigma]
    ring
  rw [hfun]
  exact (h2.mul_right _).add (h1.mul_right _)

/-- `∑_i E σ_i(P_i) < ∞`: geometric with ratios `√d R` and `d R²`. -/
private lemma VBCycleModel_summable_poisExp_sigma {d : ℝ} (hd : 0 ≤ d) {R : ℝ} (hR0 : 0 ≤ R)
    (hR1 : R < 1) (hdR : d * R ^ 2 < 1) :
    Summable fun i => poisExp (cycleMean d i / 2) (VBCycleModel_sigma d R i) := by
  set ρ₁ := d * R ^ 2 with hρ₁
  set ρ₂ := R * Real.sqrt d with hρ₂
  have hρ₁0 : 0 ≤ ρ₁ := by positivity
  have hρ₂0 : 0 ≤ ρ₂ := by positivity
  have hρ₂1 : ρ₂ < 1 := by
    have hsq : ρ₂ ^ 2 = ρ₁ := by
      rw [hρ₂, hρ₁, mul_pow, Real.sq_sqrt hd]
      ring
    nlinarith
  have h1R : 0 < 1 - R := by linarith
  set K := (1 - R)⁻¹ / 2 with hK
  have hK0 : 0 ≤ K := by positivity
  refine Summable.of_nonneg_of_le (f := fun i => ρ₂ ^ 3 * ρ₂ ^ i + K * ρ₁ ^ 3 * ρ₁ ^ i)
    (fun i => ?_) (fun i => ?_) ?_
  · exact tsum_nonneg fun k => mul_nonneg (poisPMF_nonneg (VBCycleModel_mu_nonneg hd i) k)
      (VBCycleModel_sigma_nonneg d hR0 hR1 i k)
  · have hlam := VBCycleModel_mu_nonneg hd i
    rw [poisExp, (VBCycleModel_hasSum_sigma hd R i).tsum_eq]
    have hE := poisExp_abs_sub_le hlam
    calc poisExp (cycleMean d i / 2) (fun k => |(k : ℝ) - cycleMean d i / 2|) * R ^ (i + 3) +
          cycleMean d i / 2 * (R ^ (2 * (i + 3)) * (1 - R)⁻¹ / 2)
        ≤ Real.sqrt d ^ (i + 3) * R ^ (i + 3) +
            d ^ (i + 3) * (R ^ (2 * (i + 3)) * (1 - R)⁻¹ / 2) := by
          gcongr
          · exact hE.trans (VBCycleModel_sqrt_mu_le hd i)
          · exact VBCycleModel_mu_le hd i
      _ = ρ₂ ^ 3 * ρ₂ ^ i + K * ρ₁ ^ 3 * ρ₁ ^ i := by
          rw [hK, hρ₁, hρ₂]
          ring
  · exact ((summable_geometric_of_lt_one hρ₂0 hρ₂1).mul_left (ρ₂ ^ 3)).add
      ((summable_geometric_of_lt_one hρ₁0 hdR).mul_left (K * ρ₁ ^ 3))

/-- `|L_i(t)| ≤ σ_i(k₁) + σ_i(k₂)` on `|t| ≤ R` (`norm_signedLog_le` with `a = t^{i+3}`,
`μ = μ_i`). -/
private lemma VBCycleModel_norm_term_le (d : ℝ) {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1) {t : ℂ}
    (ht : ‖t‖ ≤ R) (i k₁ k₂ : ℕ) :
    ‖(k₁ : ℂ) * Complex.log (1 + t ^ (i + 3)) + (k₂ : ℂ) * Complex.log (1 - t ^ (i + 3))‖ ≤
      VBCycleModel_sigma d R i k₁ + VBCycleModel_sigma d R i k₂ := by
  have hna : ‖t ^ (i + 3)‖ ≤ R ^ (i + 3) := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg t) ht _
  have hRi : R ^ (i + 3) ≤ R := pow_le_of_le_one hR0 hR1.le (by omega)
  have ha1 : ‖t ^ (i + 3)‖ < 1 := by linarith
  refine (norm_signedLog_le ha1 k₁ k₂ (cycleMean d i / 2)).trans ?_
  have h1R : 0 < 1 - R := by linarith
  have hB : ‖t ^ (i + 3)‖ ^ 2 * (1 - ‖t ^ (i + 3)‖)⁻¹ / 2 ≤
      R ^ (2 * (i + 3)) * (1 - R)⁻¹ / 2 := by
    have h2 : 1 - R ≤ 1 - ‖t ^ (i + 3)‖ := by linarith
    have h3 : ‖t ^ (i + 3)‖ ^ 2 ≤ R ^ (2 * (i + 3)) := by
      calc ‖t ^ (i + 3)‖ ^ 2 ≤ (R ^ (i + 3)) ^ 2 := by gcongr
        _ = R ^ (2 * (i + 3)) := by ring
    gcongr
  calc (|(k₁ : ℝ) - cycleMean d i / 2| + |(k₂ : ℝ) - cycleMean d i / 2|) * ‖t ^ (i + 3)‖ +
        ((k₁ : ℝ) + k₂) * (‖t ^ (i + 3)‖ ^ 2 * (1 - ‖t ^ (i + 3)‖)⁻¹ / 2)
      ≤ (|(k₁ : ℝ) - cycleMean d i / 2| + |(k₂ : ℝ) - cycleMean d i / 2|) * R ^ (i + 3) +
        ((k₁ : ℝ) + k₂) * (R ^ (2 * (i + 3)) * (1 - R)⁻¹ / 2) := by
        gcongr
    _ = VBCycleModel_sigma d R i k₁ + VBCycleModel_sigma d R i k₂ := by
        unfold VBCycleModel_sigma
        ring

/-- **The signed finite cycle model**: there are `σ_i(k) ≥ 0` with `∑_i E σ_i(P_i) < ∞`
(`P_i ∼ Pois(λ_{i+3}/2)`) such that, for every `r` and `x`,
`e^{-Σ(x)} ≤ |Q^{sg}_{r+2}(t; x)| ≤ e^{Σ(x)}` on `|t| ≤ R`, with
`Σ(x) = ∑_{i<r} (σ_i(x^+_{i+3}) + σ_i(x^-_{i+3}))`. -/
theorem sgCyclePoly_bounds {d : ℝ} (hd : 0 < d) {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1)
    (hdR : d * R ^ 2 < 1) :
    ∃ σ : ℕ → ℕ → ℝ, (∀ i k, 0 ≤ σ i k) ∧
      (∀ i, Summable fun k => poisPMF (cycleMean d i / 2) k * σ i k) ∧
      (Summable fun i => poisExp (cycleMean d i / 2) (σ i)) ∧
      ∀ (r : ℕ) (x : Fin (r + r) → ℕ) (t : ℂ), ‖t‖ ≤ R →
        Real.exp (-∑ i : Fin r, (σ i (x (Fin.castAdd r i)) + σ i (x (Fin.natAdd r i)))) ≤
            ‖(sgCyclePoly r x).eval t‖ ∧
          ‖(sgCyclePoly r x).eval t‖ ≤
            Real.exp (∑ i : Fin r, (σ i (x (Fin.castAdd r i)) + σ i (x (Fin.natAdd r i)))) := by
  refine ⟨VBCycleModel_sigma d R, VBCycleModel_sigma_nonneg d hR0 hR1,
    fun i => (VBCycleModel_hasSum_sigma hd.le R i).summable,
    VBCycleModel_summable_poisExp_sigma hd.le hR0 hR1 hdR, ?_⟩
  intro r x t ht
  have ht1 : ‖t‖ < 1 := lt_of_le_of_lt ht hR1
  rw [sgCyclePoly_eval_eq_exp r x ht1, Complex.norm_exp]
  have hre : |(∑ i : Fin r, ((x (Fin.castAdd r i) : ℂ) * Complex.log (1 + t ^ (i.1 + 3)) +
      (x (Fin.natAdd r i) : ℂ) * Complex.log (1 - t ^ (i.1 + 3)))).re| ≤
      ∑ i : Fin r, (VBCycleModel_sigma d R i (x (Fin.castAdd r i)) +
        VBCycleModel_sigma d R i (x (Fin.natAdd r i))) :=
    (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
      VBCycleModel_norm_term_le d hR0 hR1 ht i.1 _ _))
  obtain ⟨h1, h2⟩ := abs_le.mp hre
  exact ⟨Real.exp_le_exp.mpr h1, Real.exp_le_exp.mpr h2⟩

end

end ERZeroFreeness
