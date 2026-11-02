/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs
import ERZeroFreeness.ErdosRenyi
import ERZeroFreeness.Remainder
import ERZeroFreeness.SecondMoment

/-!
# The uniform first moment (`eq:potts-first-moment`)

For `q ≥ 3` and `0 < d < d₂(q)` there is `r > 0` such that `E|Ẑ_{G_n}(t)|` is bounded
uniformly in `n ≥ d` and `t ∈ L_r(I)`, `I = [-1/(q-1), 0]` (`first_moment_bound`).  This is the
hypothesis `eq:first-moment-hypothesis` of `prop:zero-free-moment` for the interval `I`.

Proof.  Take `δ, ρ₀` from `second_moment_bound`, `κ, C` from `remainder_bound` for this `δ`, and
`ρ = min ρ₀ (κ / (4 d (q-1)))`, `r = 4ρ`; then the factor `exp(-(κ - 2d(q-1)ρ)n)` of
`remainder_bound` is at most `1`.  With `B` the second-moment bound,
`E|Ẑ| ≤ E|Ẑ - Ẑ^B| + E|Ẑ^B| ≤ |C| + (1 + B)/2`, using `|x| ≤ (1 + |x|²)/2`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- Pointwise bound used in the first moment: `‖a‖ ≤ ‖a - b‖ + (1/2 + ‖b‖²/2)`
(triangle inequality and `‖b‖ ≤ (1 + ‖b‖²)/2`). -/
private lemma firstMoment_norm_le_aux (a b : ℂ) :
    ‖a‖ ≤ ‖a - b‖ + (1 / 2 + 1 / 2 * ‖b‖ ^ 2) := by
  have h1 : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    calc ‖a‖ = ‖(a - b) + b‖ := by rw [sub_add_cancel]
      _ ≤ ‖a - b‖ + ‖b‖ := norm_add_le _ _
  have h2 : ‖b‖ ≤ 1 / 2 + 1 / 2 * ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖b‖ - 1)]
  linarith

/-- If `ρ ≤ κ / (4 d (q-1))` then the exponential factor of `remainder_bound` is at most `1`. -/
private lemma firstMoment_exp_le_one {q : ℕ} (hq : 3 ≤ q) {d : ℝ} (hd : 0 < d) {κ ρ : ℝ}
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

/-- **`eq:potts-first-moment`.** For `q ≥ 3` and `0 < d < d₂(q)`, `E|Ẑ_{G_n}(t)|` is bounded
uniformly in `n ≥ d` and `t` in a closed tube `L_r([-1/(q-1), 0])`, `r > 0`. -/
theorem first_moment_bound {q : ℕ} (hq : 3 ≤ q) {d : ℝ} (hd : 0 < d) (hd2 : d < d2 q) :
    ∃ r > 0, ∃ B : ℝ, ∀ n : ℕ, d ≤ n → ∀ t ∈ tube (1 / ((q : ℝ) - 1)) r,
      erExp n (d / n) (fun G => ‖(zhat G q).eval t‖) ≤ B := by
  obtain ⟨δ, hδ, ρ₀, hρ₀, hsec⟩ := second_moment_bound hq hd hd2
  obtain ⟨κ, hκ, C, hrem⟩ := remainder_bound hq hd hδ
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
  have hexp := firstMoment_exp_le_one hq hd hκ hρκ n
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
        erExp_mono hp0 hp1 fun G => firstMoment_norm_le_aux _ _
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
