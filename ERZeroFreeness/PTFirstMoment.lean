/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Remainder
import ERZeroFreeness.PTSecondMoment

/-! # Remainder and first moment on `L_r(I_s)` (Appendix B)

For `q ≥ 3`, `s > 0`, `(q-1)s ≤ 1` and `d s² < 2 c_q`, `E|Ẑ_{G_n}(t)|` is bounded uniformly in
`n ≥ d` and `t` in a closed tube `L_r(I_s)`, `r > 0` (`pt_first_moment_bound`).

Proof.  `(q-1)s ≤ 1` gives `s ≤ 1/(q-1)`, so `L_{4ρ}(I_s) ⊆ L_{4ρ}(I)` and `remainder_bound`
applies unchanged (`pt_remainder_bound`).  `pt_first_moment_bound` then follows
`first_moment_bound`, with `pt_second_moment_bound` and `pt_remainder_bound` in place of
`second_moment_bound` and `remainder_bound`: `ρ := min ρ₀ (κ/(4d(q-1)))`, `r := 4ρ`, and the
bound is `|C| + (1/2 + B₂/2)`, where `B₂` bounds the second moment.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- Tubes are monotone in the interval: `I_s ⊆ I_{s'}` for `s ≤ s'`, hence
`L_r(I_s) ⊆ L_r(I_{s'})`. -/
theorem pt_tube_subset_of_le {s s' r : ℝ} (h : s ≤ s') : tube s r ⊆ tube s' r := by
  rintro t ⟨x, ⟨hx1, hx2⟩, hxt⟩
  exact ⟨x, ⟨by linarith, hx2⟩, hxt⟩

/-- **`lem:remainder` on the tube `L_{4ρ}(I_s)`**, `(q-1)s ≤ 1`: a corollary of
`remainder_bound` through `L_{4ρ}(I_s) ⊆ L_{4ρ}(I)` (Appendix B: "`L_{4ρ}(I_s) ⊆ L_{4ρ}`"). -/
theorem pt_remainder_bound {q : ℕ} (hq : 3 ≤ q) {d : ℝ} (hd : 0 < d) {δ : ℝ} (hδ : 0 < δ)
    {s : ℝ} (hsq : ((q : ℝ) - 1) * s ≤ 1) :
    ∃ κ > 0, ∃ C : ℝ, ∀ ρ : ℝ, 0 ≤ ρ → ∀ n : ℕ, d ≤ n →
      ∀ t ∈ tube s (4 * ρ),
        erExp n (d / n) (fun G => ‖(zhat G q).eval t - zhatB G q δ t‖) ≤
          C * Real.exp (-(κ - 2 * d * ((q : ℝ) - 1) * ρ) * n) := by
  obtain ⟨κ, hκ, C, hrem⟩ := remainder_bound hq hd hδ
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hs : s ≤ 1 / ((q : ℝ) - 1) := by
    rw [le_div_iff₀ hq1]; linarith
  exact ⟨κ, hκ, C, fun ρ hρ n hn t ht => hrem ρ hρ n hn t (pt_tube_subset_of_le hs ht)⟩

/-- `‖a‖ ≤ ‖a - b‖ + (1/2 + ‖b‖²/2)` (triangle inequality and `‖b‖ ≤ (1 + ‖b‖²)/2`). -/
private lemma ptFirst_norm_le_aux (a b : ℂ) :
    ‖a‖ ≤ ‖a - b‖ + (1 / 2 + 1 / 2 * ‖b‖ ^ 2) := by
  have h1 : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    calc ‖a‖ = ‖(a - b) + b‖ := by rw [sub_add_cancel]
      _ ≤ ‖a - b‖ + ‖b‖ := norm_add_le _ _
  have h2 : ‖b‖ ≤ 1 / 2 + 1 / 2 * ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖b‖ - 1)]
  linarith

/-- If `ρ ≤ κ / (4 d (q-1))`, the exponential factor of `pt_remainder_bound` is at most `1`. -/
private lemma ptFirst_exp_le_one {q : ℕ} (hq : 3 ≤ q) {d : ℝ} (hd : 0 < d) {κ ρ : ℝ}
    (hκ : 0 < κ) (hρκ : ρ ≤ κ / (4 * d * ((q : ℝ) - 1))) (n : ℕ) :
    Real.exp (-(κ - 2 * d * ((q : ℝ) - 1) * ρ) * n) ≤ 1 := by
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hc : (0 : ℝ) < 2 * d * ((q : ℝ) - 1) := by positivity
  have h1 : 2 * d * ((q : ℝ) - 1) * ρ ≤ κ / 2 := by
    calc 2 * d * ((q : ℝ) - 1) * ρ
        ≤ 2 * d * ((q : ℝ) - 1) * (κ / (4 * d * ((q : ℝ) - 1))) :=
          mul_le_mul_of_nonneg_left hρκ hc.le
      _ = κ / 2 := by field_simp; ring
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Real.exp_le_one_iff]
  have h2 : 0 ≤ κ - 2 * d * ((q : ℝ) - 1) * ρ := by linarith
  have h3 : 0 ≤ (κ - 2 * d * ((q : ℝ) - 1) * ρ) * n := mul_nonneg h2 hn0
  linarith [neg_mul (κ - 2 * d * ((q : ℝ) - 1) * ρ) (n : ℝ)]

/-- **`eq:potts-first-moment` on a tube around `I_s`** (Appendix B:
"`sup_n sup_{t ∈ L_{4ρ}(I_s)} E|Ẑ_{G_n}(t)| < ∞`"). Generalizes `first_moment_bound`
(the case `s = 1/(q-1)`); its conclusion is the hypothesis `hmom` of `prop_zero_free_moment`. -/
theorem pt_first_moment_bound {q : ℕ} (hq : 3 ≤ q) {d : ℝ} (hd : 0 < d) {s : ℝ} (hs0 : 0 < s)
    (hsq : ((q : ℝ) - 1) * s ≤ 1) (hds : d * s ^ 2 < 2 * cq q) :
    ∃ r > 0, ∃ B : ℝ, ∀ n : ℕ, d ≤ n → ∀ t ∈ tube s r,
      erExp n (d / n) (fun G => ‖(zhat G q).eval t‖) ≤ B := by
  obtain ⟨δ, hδ, ρ₀, hρ₀, hsec⟩ := pt_second_moment_bound hq hd hs0 hds
  obtain ⟨κ, hκ, C, hrem⟩ := pt_remainder_bound hq hd hδ hsq
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  set ρ : ℝ := min ρ₀ (κ / (4 * d * ((q : ℝ) - 1)))
  have hρpos : 0 < ρ := lt_min hρ₀ (by positivity)
  have hρle : ρ ≤ ρ₀ := min_le_left _ _
  have hρκ : ρ ≤ κ / (4 * d * ((q : ℝ) - 1)) := min_le_right _ _
  obtain ⟨B, hB⟩ := hsec ρ hρpos hρle
  refine ⟨4 * ρ, by positivity, |C| + (1 / 2 + 1 / 2 * B), ?_⟩
  intro n hn t ht
  obtain ⟨hp0, hp1⟩ := div_natCast_mem_Icc hd.le hn
  have hexp := ptFirst_exp_le_one hq hd hκ hρκ n
  have hexp0 : 0 < Real.exp (-(κ - 2 * d * ((q : ℝ) - 1) * ρ) * n) := Real.exp_pos _
  have hrem' := hrem ρ hρpos.le n hn t ht
  have hsec' := hB n hn t ht
  have hCexp : C * Real.exp (-(κ - 2 * d * ((q : ℝ) - 1) * ρ) * n) ≤ |C| := by
    calc C * Real.exp (-(κ - 2 * d * ((q : ℝ) - 1) * ρ) * n)
        ≤ |C| * Real.exp (-(κ - 2 * d * ((q : ℝ) - 1) * ρ) * n) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hexp0.le
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hexp (abs_nonneg C)
      _ = |C| := mul_one _
  calc erExp n (d / n) (fun G => ‖(zhat G q).eval t‖)
      ≤ erExp n (d / n) (fun G => ‖(zhat G q).eval t - zhatB G q δ t‖ +
          (1 / 2 + 1 / 2 * ‖zhatB G q δ t‖ ^ 2)) :=
        erExp_mono hp0 hp1 fun G => ptFirst_norm_le_aux _ _
    _ = erExp n (d / n) (fun G => ‖(zhat G q).eval t - zhatB G q δ t‖) +
          erExp n (d / n) (fun G => 1 / 2 + 1 / 2 * ‖zhatB G q δ t‖ ^ 2) :=
        erExp_add (fun G => ‖(zhat G q).eval t - zhatB G q δ t‖)
          (fun G => 1 / 2 + 1 / 2 * ‖zhatB G q δ t‖ ^ 2)
    _ = erExp n (d / n) (fun G => ‖(zhat G q).eval t - zhatB G q δ t‖) +
          (1 / 2 + 1 / 2 * erExp n (d / n) (fun G => ‖zhatB G q δ t‖ ^ 2)) := by
        rw [erExp_add (fun _ => (1 / 2 : ℝ)) (fun G => 1 / 2 * ‖zhatB G q δ t‖ ^ 2),
          erExp_const, erExp_const_mul]
    _ ≤ |C| + (1 / 2 + 1 / 2 * B) := by
        have h := mul_le_mul_of_nonneg_left hsec' (by norm_num : (0 : ℝ) ≤ 1 / 2)
        linarith

end

end ERZeroFreeness
