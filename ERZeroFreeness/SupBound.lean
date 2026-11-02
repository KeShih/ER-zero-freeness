/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs
import ERZeroFreeness.ErdosRenyi

/-!
# Suprema on tubes from first moments (Lemma 3.2, `lem:holomorphic-tightness`)

The part of Lemma 3.2 that is used (`erProb_exists_norm_gt_le`): a uniform first-moment bound
`E|Ẑ_G(t)| ≤ B` on `L_{4ρ}(I_s)` gives `Pr[sup_{L_{3ρ}(I_s)} |Ẑ_G| > M] ≤ C/M` for
`G ∼ G(n, d/n)`, uniformly in `n ≥ d`.  The tightness statement of the lemma is not needed: the
compactness argument of Theorem 3.1 is replaced by `exists_norm_le_of_isBigO_pow`.  The paper
bounds `|f(t)|` by an average over a disk; here a circle average is used.

Proof.  For a polynomial `f`, the Cauchy integral formula on the circle `|w - y| = 4ρ`
(`DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul`) gives, for
`|t - y| ≤ 7ρ/2`, `|f(t)| ≤ 8 · (2π)^{-1} ∫_0^{2π} |f(y + 4ρ e^{iθ})| dθ`
(`SupBoundAux.norm_eval_le_circleAvg`).  The centres `y_j = -j ρ/2`, `0 ≤ j ≤ N = ⌊2s/ρ⌋`,
lie in `I_s` and form a `ρ/2`-net of it, so every point of `L_{3ρ}(I_s)` is within `7ρ/2` of
some `y_j` (`SupBoundAux.exists_centre`).  This bounds `sup_{L_{3ρ}} |Ẑ_G|` by
`S(G) = 8 (2π)^{-1} ∑_j ∫_0^{2π} |Ẑ_G(y_j + 4ρ e^{iθ})| dθ`; the circles lie in `L_{4ρ}(I_s)`
(`SupBoundAux.circleMap_mem_tube`), so exchanging the finite sum over graphs with the integral
gives `E_{G(n,d/n)} S ≤ 8 (N + 1) B`, and Markov's inequality (`erProb_le_erExp_div`) finishes
with `C = 8 (N + 1) B`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

namespace SupBoundAux

/-- Cauchy estimate on a circle: for a polynomial `f`, a centre `y`, a radius `R > 0` and a point
`t` with `‖t - y‖ ≤ 7R/8`, `‖f(t)‖ ≤ 8/(2π) ∫_0^{2π} ‖f(y + R e^{iθ})‖ dθ`. -/
theorem norm_eval_le_circleAvg (f : ℂ[X]) {y t : ℂ} {R : ℝ} (hR : 0 < R)
    (ht : ‖t - y‖ ≤ 7 * R / 8) :
    ‖f.eval t‖ ≤
      8 / (2 * Real.pi) * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f.eval (circleMap y R θ)‖ := by
  have hw : t ∈ Metric.ball y R := by
    rw [Metric.mem_ball, dist_eq_norm]; linarith
  have hC : ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∮ z in C(y, R), (z - t)⁻¹ • f.eval z) =
      f.eval t :=
    ((Polynomial.differentiable f).diffContOnCl
      (s := Metric.ball y R)).two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw
  rw [← hC, norm_smul]
  have h2pi : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    simp [Real.pi_pos.le]
  rw [h2pi]
  have hpi : 0 < 2 * Real.pi := Real.two_pi_pos
  have hcont : Continuous fun θ : ℝ =>
      ‖deriv (circleMap y R) θ • ((circleMap y R θ - t)⁻¹ • f.eval (circleMap y R θ))‖ := by
    have : deriv (circleMap y R) = fun θ => circleMap 0 R θ * Complex.I :=
      funext (deriv_circleMap y R)
    rw [this]
    exact (((continuous_circleMap 0 R).mul continuous_const).smul
      ((continuous_circleMap_inv hw).smul
        ((Polynomial.continuous f).comp (continuous_circleMap y R)))).norm
  have key : ‖∮ z in C(y, R), (z - t)⁻¹ • f.eval z‖ ≤
      ∫ θ in (0 : ℝ)..2 * Real.pi, 8 * ‖f.eval (circleMap y R θ)‖ := by
    refine (intervalIntegral.norm_integral_le_integral_norm hpi.le).trans ?_
    apply intervalIntegral.integral_mono_on hpi.le
    · exact hcont.intervalIntegrable _ _
    · exact (continuous_const.mul
        ((Polynomial.continuous f).comp (continuous_circleMap y R)).norm).intervalIntegrable _ _
    · intro θ _
      simp only [deriv_circleMap, norm_smul, norm_mul, norm_circleMap_zero, Complex.norm_I,
        mul_one, norm_inv]
      have hd : R / 8 ≤ ‖circleMap y R θ - t‖ := by
        have h1 : ‖circleMap y R θ - y‖ = R := by simp [abs_of_pos hR]
        have h2 : ‖circleMap y R θ - y‖ ≤ ‖circleMap y R θ - t‖ + ‖t - y‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        linarith
      have hpos : 0 < ‖circleMap y R θ - t‖ := by linarith [show 0 < R / 8 by positivity]
      rw [abs_of_pos hR]
      have h8 : R * ‖circleMap y R θ - t‖⁻¹ ≤ 8 := by
        rw [← div_eq_mul_inv, div_le_iff₀ hpos]; linarith
      calc R * (‖circleMap y R θ - t‖⁻¹ * ‖f.eval (circleMap y R θ)‖)
          = (R * ‖circleMap y R θ - t‖⁻¹) * ‖f.eval (circleMap y R θ)‖ := by ring
        _ ≤ 8 * ‖f.eval (circleMap y R θ)‖ := mul_le_mul_of_nonneg_right h8 (norm_nonneg _)
  rw [intervalIntegral.integral_const_mul] at key
  calc (2 * Real.pi)⁻¹ * ‖∮ z in C(y, R), (z - t)⁻¹ • f.eval z‖
      ≤ (2 * Real.pi)⁻¹ * (8 * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f.eval (circleMap y R θ)‖) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = 8 / (2 * Real.pi) * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖f.eval (circleMap y R θ)‖ := by ring

/-- The centres `y_j = -j ρ/2`, `j ≤ ⌊2s/ρ⌋`, form a `ρ/2`-net of `I_s`; hence every point of
`L_{3ρ}(I_s)` is within `7ρ/2 = 7(4ρ)/8` of some centre. -/
theorem exists_centre {s ρ : ℝ} (hρ : 0 < ρ) {t : ℂ} (ht : t ∈ tube s (3 * ρ)) :
    ∃ j ∈ Finset.range (⌊s / (ρ / 2)⌋₊ + 1),
      ‖t - (((-((j : ℝ) * (ρ / 2))) : ℝ) : ℂ)‖ ≤ 7 * (4 * ρ) / 8 := by
  obtain ⟨x, ⟨hx1, hx2⟩, hxt⟩ := ht
  have hρ2 : 0 < ρ / 2 := by positivity
  have hx0 : 0 ≤ -x / (ρ / 2) := div_nonneg (by linarith) hρ2.le
  have h1 : ((⌊-x / (ρ / 2)⌋₊ : ℕ) : ℝ) ≤ -x / (ρ / 2) := Nat.floor_le hx0
  have h2 : -x / (ρ / 2) < ((⌊-x / (ρ / 2)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨⌊-x / (ρ / 2)⌋₊, ?_, ?_⟩
  · rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hρ2.le)
  · set j : ℕ := ⌊-x / (ρ / 2)⌋₊
    have h1' : (j : ℝ) * (ρ / 2) ≤ -x := (le_div_iff₀ hρ2).1 h1
    have h2' : -x < ((j : ℝ) + 1) * (ρ / 2) := (div_lt_iff₀ hρ2).1 h2
    have hxy : ‖(x : ℂ) - (((-((j : ℝ) * (ρ / 2))) : ℝ) : ℂ)‖ ≤ ρ / 2 := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith
    calc ‖t - (((-((j : ℝ) * (ρ / 2))) : ℝ) : ℂ)‖
        = ‖(t - x) + ((x : ℂ) - (((-((j : ℝ) * (ρ / 2))) : ℝ) : ℂ))‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ ‖t - x‖ + ‖(x : ℂ) - (((-((j : ℝ) * (ρ / 2))) : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 * ρ + ρ / 2 := add_le_add hxt hxy
      _ = 7 * (4 * ρ) / 8 := by ring

/-- The circles of radius `4ρ` around the centres `y_j = -j ρ/2`, `j ≤ ⌊2s/ρ⌋`, lie in
`L_{4ρ}(I_s)`. -/
theorem circleMap_mem_tube {s ρ : ℝ} (hs : 0 ≤ s) (hρ : 0 < ρ) {j : ℕ}
    (hj : j ∈ Finset.range (⌊s / (ρ / 2)⌋₊ + 1)) (θ : ℝ) :
    circleMap (((-((j : ℝ) * (ρ / 2))) : ℝ) : ℂ) (4 * ρ) θ ∈ tube s (4 * ρ) := by
  have hρ2 : 0 < ρ / 2 := by positivity
  refine ⟨-((j : ℝ) * (ρ / 2)), ⟨?_, ?_⟩, ?_⟩
  · have hjN : j ≤ ⌊s / (ρ / 2)⌋₊ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have h1 : (j : ℝ) ≤ s / (ρ / 2) :=
      (Nat.cast_le.2 hjN).trans (Nat.floor_le (div_nonneg hs hρ2.le))
    have h2 : (j : ℝ) * (ρ / 2) ≤ s := (le_div_iff₀ hρ2).1 h1
    linarith
  · have : 0 ≤ (j : ℝ) * (ρ / 2) := by positivity
    linarith
  · rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos (by positivity)]

end SupBoundAux

open SupBoundAux in
/-- **Lemma 3.2 (`lem:holomorphic-tightness`), as used.**  If `E|Ẑ_G(t)| ≤ B` for
`G ∼ G(n, d/n)`, all `n ≥ d` and all `t ∈ L_{4ρ}(I_s)`, then there is `C` with
`Pr[|Ẑ_G(t)| > M for some t ∈ L_{3ρ}(I_s)] ≤ C/M` for all `M > 0` and `n ≥ d`. -/
theorem erProb_exists_norm_gt_le {q : ℕ} {d : ℝ} (hd : 0 < d) {s ρ B : ℝ} (hs : 0 ≤ s)
    (hρ : 0 < ρ)
    (hmom : ∀ n : ℕ, d ≤ n → ∀ t ∈ tube s (4 * ρ),
      erExp n (d / n) (fun G => ‖(zhat G q).eval t‖) ≤ B) :
    ∃ C : ℝ, ∀ M : ℝ, 0 < M → ∀ n : ℕ, d ≤ n →
      erProb n (d / n) {G | ∃ t ∈ tube s (3 * ρ), M < ‖(zhat G q).eval t‖} ≤ C / M := by
  -- `N + 1` centres `y_j = -j ρ/2`, `0 ≤ j ≤ N`
  set N : ℕ := ⌊s / (ρ / 2)⌋₊
  set y : ℕ → ℂ := fun j => (((-((j : ℝ) * (ρ / 2))) : ℝ) : ℂ)
  have hpi : 0 < 2 * Real.pi := Real.two_pi_pos
  refine ⟨8 * ((N : ℝ) + 1) * B, fun M hM n hn => ?_⟩
  obtain ⟨hp0, hp1⟩ := div_natCast_mem_Icc hd.le hn
  -- the circle integrals `I_j(G) = ∫_0^{2π} |Ẑ_G(y_j + 4ρ e^{iθ})| dθ`
  set I : ℕ → SimpleGraph (Fin n) → ℝ := fun j G =>
    ∫ θ in (0 : ℝ)..2 * Real.pi, ‖(zhat G q).eval (circleMap (y j) (4 * ρ) θ)‖
  have hI0 : ∀ j G, 0 ≤ I j G := fun j G =>
    intervalIntegral.integral_nonneg hpi.le fun θ _ => norm_nonneg _
  -- the majorant `S(G) = 8 (2π)⁻¹ ∑_j I_j(G)` of `sup_{L_{3ρ}} |Ẑ_G|`
  set S : SimpleGraph (Fin n) → ℝ := fun G =>
    8 / (2 * Real.pi) * ∑ j ∈ Finset.range (N + 1), I j G with hS
  have hS0 : ∀ G, 0 ≤ S G := fun G =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => hI0 j G)
  have hsub : {G | ∃ t ∈ tube s (3 * ρ), M < ‖(zhat G q).eval t‖} ⊆ {G | M ≤ S G} := by
    rintro G ⟨t, ht, hMt⟩
    obtain ⟨j, hj, htj⟩ := exists_centre hρ ht
    have h1 := norm_eval_le_circleAvg (zhat G q) (y := y j)
      (by positivity : (0 : ℝ) < 4 * ρ) htj
    have h2 : I j G ≤ ∑ i ∈ Finset.range (N + 1), I i G :=
      Finset.single_le_sum (fun i _ => hI0 i G) hj
    show M ≤ S G
    have h3 : 8 / (2 * Real.pi) * I j G ≤ S G := mul_le_mul_of_nonneg_left h2 (by positivity)
    exact hMt.le.trans (h1.trans h3)
  -- each `E[I_j] ≤ 2π B`: exchange the finite sum over graphs with the integral
  have hIj : ∀ j ∈ Finset.range (N + 1),
      ∑ G : SimpleGraph (Fin n), erWeight n (d / n) G * I j G ≤ 2 * Real.pi * B := by
    intro j hj
    have hcont : ∀ G : SimpleGraph (Fin n), Continuous fun θ : ℝ =>
        ‖(zhat G q).eval (circleMap (y j) (4 * ρ) θ)‖ := fun G =>
      ((Polynomial.continuous _).comp (continuous_circleMap _ _)).norm
    have hswap : ∑ G : SimpleGraph (Fin n), erWeight n (d / n) G * I j G =
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          erExp n (d / n) (fun G => ‖(zhat G q).eval (circleMap (y j) (4 * ρ) θ)‖) := by
      unfold erExp
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun G _ => ?_
        rw [intervalIntegral.integral_const_mul]
      · intro G _
        exact (continuous_const.mul (hcont G)).intervalIntegrable _ _
    rw [hswap]
    calc ∫ θ in (0 : ℝ)..2 * Real.pi,
          erExp n (d / n) (fun G => ‖(zhat G q).eval (circleMap (y j) (4 * ρ) θ)‖)
        ≤ ∫ θ in (0 : ℝ)..2 * Real.pi, B := by
          apply intervalIntegral.integral_mono_on hpi.le
          · unfold erExp
            exact (continuous_finsetSum _ fun G _ =>
              continuous_const.mul (hcont G)).intervalIntegrable _ _
          · exact intervalIntegrable_const
          · intro θ _
            exact hmom n hn _ (circleMap_mem_tube hs hρ hj θ)
      _ = 2 * Real.pi * B := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have hexp : erExp n (d / n) S ≤ 8 * ((N : ℝ) + 1) * B := by
    have hrw : erExp n (d / n) S = 8 / (2 * Real.pi) *
        ∑ j ∈ Finset.range (N + 1), ∑ G : SimpleGraph (Fin n), erWeight n (d / n) G * I j G := by
      unfold erExp
      simp only [hS, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun G _ => ?_
      ring
    rw [hrw]
    calc 8 / (2 * Real.pi) *
          ∑ j ∈ Finset.range (N + 1), ∑ G : SimpleGraph (Fin n), erWeight n (d / n) G * I j G
        ≤ 8 / (2 * Real.pi) * ∑ j ∈ Finset.range (N + 1), 2 * Real.pi * B :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hIj) (by positivity)
      _ = 8 * ((N : ℝ) + 1) * B := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          field_simp
  -- Markov's inequality
  calc erProb n (d / n) {G | ∃ t ∈ tube s (3 * ρ), M < ‖(zhat G q).eval t‖}
      ≤ erProb n (d / n) {G | M ≤ S G} := erProb_mono hp0 hp1 hsub
    _ ≤ erExp n (d / n) S / M := erProb_le_erExp_div hp0 hp1 hS0 hM
    _ ≤ 8 * ((N : ℝ) + 1) * B / M := div_le_div_of_nonneg_right hexp hM.le

end

end ERZeroFreeness
