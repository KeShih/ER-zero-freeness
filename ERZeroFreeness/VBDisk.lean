/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Vanishing
import ERZeroFreeness.SupBound

/-!
# Analytic tools on disks

Disk versions of the analytic tools of Theorem 3.1 and Lemma 3.2, used for the Viana–Bray
polynomial on a disk `|t| < r_d` (Step 3 of Section 7):

* `norm_eval_le_circleAvg_zero`: by Cauchy's integral formula,
  `|f(t)| ≤ (1 - θ)⁻¹ (2π)⁻¹ ∫_0^{2π} |f(R e^{iφ})| dφ` for a polynomial `f` and `|t| ≤ θR`,
  `0 ≤ θ < 1`;
* `sum_exists_norm_gt_le`: for a finite family of polynomials `f_ω` with weights `w_ω ≥ 0`, a
  first-moment bound `B` on the circle `|t| = R₁` bounds the weight of
  `{ω : sup_{|t| ≤ R} |f_ω(t)| > M}` by `R₁ B / ((R₁ - R) M)` (Markov's inequality), the form of
  `lem:holomorphic-tightness` used here;
* `disk_norm_le_of_isBigO_pow`: the quantitative identity theorem on disks, deduced from
  `exists_norm_le_of_isBigO_pow` by rotating each point onto the negative real axis.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- Cauchy's integral formula on the circle `|w| = R`, for `|t| ≤ θR` with `0 ≤ θ < 1`:
`|f(t)| ≤ (1 - θ)⁻¹ (2π)⁻¹ ∫_0^{2π} |f(R e^{iφ})| dφ`. -/
theorem norm_eval_le_circleAvg_zero (f : ℂ[X]) {R θ : ℝ} (hR : 0 < R) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) {t : ℂ} (ht : ‖t‖ ≤ θ * R) :
    ‖f.eval t‖ ≤ (1 - θ)⁻¹ * ((2 * Real.pi)⁻¹ *
      ∫ φ in (0 : ℝ)..2 * Real.pi, ‖f.eval (circleMap 0 R φ)‖) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hθR0 : 0 ≤ θ * R := mul_nonneg hθ0 hR.le
  have hθR : θ * R < R := by nlinarith
  have hw : t ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  -- Cauchy's integral formula on the circle `|z| = R`
  have hC : ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∮ z in C(0, R), (z - t)⁻¹ • f.eval z) =
      f.eval t :=
    ((Polynomial.differentiable f).diffContOnCl
      (s := Metric.ball 0 R)).two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw
  rw [← hC, norm_smul]
  have h2pi : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    simp [Real.pi_pos.le]
  rw [h2pi]
  have hpi : 0 < 2 * Real.pi := Real.two_pi_pos
  have hcont : Continuous fun φ : ℝ =>
      ‖deriv (circleMap 0 R) φ • ((circleMap 0 R φ - t)⁻¹ • f.eval (circleMap 0 R φ))‖ := by
    have : deriv (circleMap (0 : ℂ) R) = fun φ => circleMap 0 R φ * Complex.I :=
      funext (deriv_circleMap 0 R)
    rw [this]
    exact (((continuous_circleMap 0 R).mul continuous_const).smul
      ((continuous_circleMap_inv hw).smul
        ((Polynomial.continuous f).comp (continuous_circleMap 0 R)))).norm
  -- on the circle, `|z - t| ≥ (1 - θ) R` and `|dz/dφ| = R`
  have key : ‖∮ z in C(0, R), (z - t)⁻¹ • f.eval z‖ ≤
      ∫ φ in (0 : ℝ)..2 * Real.pi, (1 - θ)⁻¹ * ‖f.eval (circleMap 0 R φ)‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm hpi.le).trans ?_
    apply intervalIntegral.integral_mono_on hpi.le
    · exact hcont.intervalIntegrable _ _
    · exact (continuous_const.mul
        ((Polynomial.continuous f).comp (continuous_circleMap 0 R)).norm).intervalIntegrable _ _
    · intro φ _
      simp only [deriv_circleMap, norm_smul, norm_mul, norm_circleMap_zero, Complex.norm_I,
        mul_one, norm_inv]
      have hd : (1 - θ) * R ≤ ‖circleMap 0 R φ - t‖ := by
        have h1 : ‖circleMap 0 R φ‖ = R := by rw [norm_circleMap_zero, abs_of_pos hR]
        have h2 : ‖circleMap 0 R φ‖ - ‖t‖ ≤ ‖circleMap 0 R φ - t‖ := norm_sub_norm_le _ _
        nlinarith
      have hpos : 0 < ‖circleMap 0 R φ - t‖ := lt_of_lt_of_le (by positivity) hd
      rw [abs_of_pos hR]
      have h8 : R * ‖circleMap 0 R φ - t‖⁻¹ ≤ (1 - θ)⁻¹ := by
        rw [← div_eq_mul_inv, div_le_iff₀ hpos, inv_mul_eq_div, le_div_iff₀ h1θ]
        linarith
      calc R * (‖circleMap 0 R φ - t‖⁻¹ * ‖f.eval (circleMap 0 R φ)‖)
          = (R * ‖circleMap 0 R φ - t‖⁻¹) * ‖f.eval (circleMap 0 R φ)‖ := by ring
        _ ≤ (1 - θ)⁻¹ * ‖f.eval (circleMap 0 R φ)‖ :=
          mul_le_mul_of_nonneg_right h8 (norm_nonneg _)
  rw [intervalIntegral.integral_const_mul] at key
  calc (2 * Real.pi)⁻¹ * ‖∮ z in C(0, R), (z - t)⁻¹ • f.eval z‖
      ≤ (2 * Real.pi)⁻¹ *
          ((1 - θ)⁻¹ * ∫ φ in (0 : ℝ)..2 * Real.pi, ‖f.eval (circleMap 0 R φ)‖) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = (1 - θ)⁻¹ * ((2 * Real.pi)⁻¹ *
          ∫ φ in (0 : ℝ)..2 * Real.pi, ‖f.eval (circleMap 0 R φ)‖) := by ring

/-- Suprema on disks from first moments on a larger circle (Markov's inequality), for any finite
weighted family of polynomials: if `∑_ω w_ω |f_ω(t)| ≤ B` on `|t| = R₁`, then the weight of
`{ω : ∃ t, |t| ≤ R ∧ M < |f_ω(t)|}` is at most `R₁/(R₁ - R) · B/M`. -/
theorem sum_exists_norm_gt_le {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (f : Ω → ℂ[X]) {R R₁ B : ℝ} (hR : 0 ≤ R) (hRR : R < R₁)
    (hmom : ∀ t : ℂ, ‖t‖ = R₁ → ∑ ω, w ω * ‖(f ω).eval t‖ ≤ B) {M : ℝ} (hM : 0 < M) :
    (∑ ω, if ∃ t : ℂ, ‖t‖ ≤ R ∧ M < ‖(f ω).eval t‖ then w ω else 0) ≤
      R₁ / (R₁ - R) * B / M := by
  have hR₁ : 0 < R₁ := lt_of_le_of_lt hR hRR
  -- the ratio `θ = R / R₁ ∈ [0, 1)`
  set θ : ℝ := R / R₁ with hθdef
  have hθ0 : 0 ≤ θ := div_nonneg hR hR₁.le
  have hθ1 : θ < 1 := (div_lt_one hR₁).2 hRR
  have h1θ : 0 < 1 - θ := by linarith
  have hθR : R = θ * R₁ := by rw [hθdef, div_mul_cancel₀ _ hR₁.ne']
  have hK : (1 - θ)⁻¹ = R₁ / (R₁ - R) := by
    rw [hθdef, one_sub_div hR₁.ne', inv_div]
  have hpi : 0 < 2 * Real.pi := Real.two_pi_pos
  -- the circle integrals `I(ω) = ∫_0^{2π} |f_ω(R₁ e^{iφ})| dφ`
  set I : Ω → ℝ := fun ω => ∫ φ in (0 : ℝ)..2 * Real.pi, ‖(f ω).eval (circleMap 0 R₁ φ)‖
    with hIdef
  have hI0 : ∀ ω, 0 ≤ I ω := fun ω =>
    intervalIntegral.integral_nonneg hpi.le fun φ _ => norm_nonneg _
  -- the majorant `S(ω) = (1 - θ)⁻¹ (2π)⁻¹ I(ω)` of `sup_{|t| ≤ R} |f_ω(t)|`
  set S : Ω → ℝ := fun ω => (1 - θ)⁻¹ * ((2 * Real.pi)⁻¹ * I ω) with hS
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω =>
    mul_nonneg (inv_nonneg.2 h1θ.le) (mul_nonneg (by positivity) (hI0 ω))
  have hev : ∀ ω, (∃ t : ℂ, ‖t‖ ≤ R ∧ M < ‖(f ω).eval t‖) → M ≤ S ω := by
    rintro ω ⟨t, ht, hMt⟩
    have h1 := norm_eval_le_circleAvg_zero (f ω) hR₁ hθ0 hθ1 (t := t) (by rw [← hθR]; exact ht)
    exact hMt.le.trans h1
  -- Markov's inequality, pointwise
  have hpt : ∀ ω, (if ∃ t : ℂ, ‖t‖ ≤ R ∧ M < ‖(f ω).eval t‖ then w ω else 0) ≤
      w ω * S ω / M := by
    intro ω
    split_ifs with h
    · rw [le_div_iff₀ hM]
      exact mul_le_mul_of_nonneg_left (hev ω h) (hw ω)
    · exact div_nonneg (mul_nonneg (hw ω) (hS0 ω)) hM.le
  -- `∑_ω w(ω) I(ω) ≤ 2π B`: exchange the finite sum with the integral
  have hcont : ∀ ω, Continuous fun φ : ℝ => ‖(f ω).eval (circleMap 0 R₁ φ)‖ := fun ω =>
    ((Polynomial.continuous _).comp (continuous_circleMap _ _)).norm
  have hswap : ∑ ω, w ω * I ω =
      ∫ φ in (0 : ℝ)..2 * Real.pi, ∑ ω, w ω * ‖(f ω).eval (circleMap 0 R₁ φ)‖ := by
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun ω _ => ?_
      rw [intervalIntegral.integral_const_mul]
    · intro ω _
      exact (continuous_const.mul (hcont ω)).intervalIntegrable _ _
  have hsumI : ∑ ω, w ω * I ω ≤ 2 * Real.pi * B := by
    rw [hswap]
    calc ∫ φ in (0 : ℝ)..2 * Real.pi, ∑ ω, w ω * ‖(f ω).eval (circleMap 0 R₁ φ)‖
        ≤ ∫ φ in (0 : ℝ)..2 * Real.pi, B := by
          apply intervalIntegral.integral_mono_on hpi.le
          · exact (continuous_finsetSum _ fun ω _ =>
              continuous_const.mul (hcont ω)).intervalIntegrable _ _
          · exact intervalIntegrable_const
          · intro φ _
            apply hmom
            rw [norm_circleMap_zero, abs_of_pos hR₁]
      _ = 2 * Real.pi * B := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have hsumS : ∑ ω, w ω * S ω ≤ (1 - θ)⁻¹ * B := by
    have hrw : ∑ ω, w ω * S ω = (1 - θ)⁻¹ * ((2 * Real.pi)⁻¹ * ∑ ω, w ω * I ω) := by
      simp only [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω _ => ?_
      ring
    rw [hrw]
    have h2 : (2 * Real.pi)⁻¹ * ∑ ω, w ω * I ω ≤ B := by
      rw [inv_mul_le_iff₀ hpi]
      exact hsumI
    exact mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 h1θ.le)
  calc (∑ ω, if ∃ t : ℂ, ‖t‖ ≤ R ∧ M < ‖(f ω).eval t‖ then w ω else 0)
      ≤ ∑ ω, w ω * S ω / M := Finset.sum_le_sum fun ω _ => hpt ω
    _ = (∑ ω, w ω * S ω) / M := by rw [Finset.sum_div]
    _ ≤ (1 - θ)⁻¹ * B / M := div_le_div_of_nonneg_right hsumS hM.le
    _ = R₁ / (R₁ - R) * B / M := by rw [hK]

/-- **Quantitative identity theorem on disks.**  For `0 ≤ R₀ < R` and `ε > 0` there is `k` such
that every `h` holomorphic on `|t| < R`, bounded by `1` there and with `h = O(t^{k'})` at `0` for
some `k' ≥ k`, satisfies `|h| ≤ ε` on `|t| ≤ R₀`.  Deduced from `exists_norm_le_of_isBigO_pow`
by rotation. -/
theorem disk_norm_le_of_isBigO_pow {R₀ R : ℝ} (hR₀ : 0 ≤ R₀) (hR : R₀ < R) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ k : ℕ, ∀ k' ≥ k, ∀ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball 0 R) →
      (∀ t ∈ Metric.ball (0 : ℂ) R, ‖h t‖ ≤ 1) → (h =O[𝓝 0] fun t => t ^ k') →
        ∀ t : ℂ, ‖t‖ ≤ R₀ → ‖h t‖ ≤ ε := by
  set ρ : ℝ := (R - R₀) / 4 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  obtain ⟨k, hk⟩ := exists_norm_le_of_isBigO_pow hR₀ hρ hε
  refine ⟨k, fun k' hk' h hd hb hO t ht => ?_⟩
  -- every point of the tubes around `[-R₀, 0]` of radius `< 4ρ` lies in the ball
  have hx : ∀ x : ℝ, x ∈ Set.Icc (-R₀) 0 → ‖(x : ℂ)‖ ≤ R₀ := by
    intro x hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hopen : ∀ u ∈ openTube R₀ (4 * ρ), ‖u‖ < R := by
    rintro u ⟨x, hxI, hux⟩
    calc ‖u‖ = ‖(u - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖u - x‖ + ‖(x : ℂ)‖ := norm_add_le _ _
      _ < 4 * ρ + R₀ := by linarith [hx x hxI]
      _ = R := by rw [hρdef]; ring
  have hclosed : ∀ u ∈ tube R₀ (3 * ρ), ‖u‖ < R := by
    rintro u ⟨x, hxI, hux⟩
    calc ‖u‖ = ‖(u - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖u - x‖ + ‖(x : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 * ρ + R₀ := by linarith [hx x hxI]
      _ < R := by rw [hρdef]; linarith
  -- the rotation `t = c · (-‖t‖)`
  obtain ⟨c, hc, htc⟩ : ∃ c : ℂ, ‖c‖ = 1 ∧ t = c * (-((‖t‖ : ℝ) : ℂ)) := by
    by_cases h0 : t = 0
    · exact ⟨1, by simp, by simp [h0]⟩
    · have hn : (‖t‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
      refine ⟨-t / ‖t‖, ?_, ?_⟩
      · rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_norm,
          div_self (norm_ne_zero_iff.mpr h0)]
      · rw [div_mul_eq_mul_div, neg_mul_neg, mul_div_assoc, div_self hn, mul_one]
  have hmul : ∀ u : ℂ, ‖c * u‖ = ‖u‖ := fun u => by rw [norm_mul, hc, one_mul]
  have hmaps : ∀ u : ℂ, ‖u‖ < R → c * u ∈ Metric.ball (0 : ℂ) R := fun u hu => by
    rw [Metric.mem_ball, dist_zero_right, hmul]; exact hu
  set hc' : ℂ → ℂ := fun u => h (c * u) with hhc'
  have hd' : DifferentiableOn ℂ hc' (openTube R₀ (4 * ρ)) := by
    refine hd.comp (differentiableOn_id.const_mul c) ?_
    intro u hu
    exact hmaps u (hopen u hu)
  have hb' : ∀ u ∈ tube R₀ (3 * ρ), ‖hc' u‖ ≤ 1 := fun u hu => hb _ (hmaps u (hclosed u hu))
  have hO' : hc' =O[𝓝 0] fun u => u ^ k' := by
    have htend : Tendsto (fun u : ℂ => c * u) (𝓝 0) (𝓝 0) := by
      have := (continuous_const_mul c).tendsto 0
      rwa [mul_zero] at this
    have h1 := hO.comp_tendsto htend
    refine h1.trans (Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun u => ?_))
    simp [Function.comp, mul_pow, norm_pow, hc]
  have hmem : (-((‖t‖ : ℝ) : ℂ)) ∈ tube R₀ ρ :=
    ⟨-‖t‖, ⟨by linarith, by linarith [norm_nonneg t]⟩, by push_cast; simp [hρ.le]⟩
  have := hk k' hk' hc' hd' hb' hO' _ hmem
  rw [htc]
  exact this

end

end ERZeroFreeness
