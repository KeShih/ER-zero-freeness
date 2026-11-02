/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Entropy

/-! # The parameter `s = |t(x₀)|` of Appendix B

For `x₀ ∈ [0,1)` the map `t` sends the positive-temperature interval `[x₀,1]` onto
`I_s = [-s, 0]` with `s = s(x₀) = (1-x₀)/(q-1+x₀)` (`ptS`).  This file proves the elementary
facts about `s` used in Appendix B: `s > 0`, `(q-1)s ≤ 1`, `x_s = x₀`, and the equivalence of
`eq:positive-temperature-range` with `d s² < 2 c_q`.

The proofs are direct computations: `(q-1)(1-x₀) = (q-1+x₀) - q x₀`,
`1 - (q-1)s = q x₀/(q-1+x₀)`, `1 + s = q/(q-1+x₀)`, and
`d₂(q) ((q-1+x₀)/((q-1)(1-x₀)))² = 2 c_q / s²` (`d2_eq`).
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- `s(x₀) = |t(x₀)| = (1 - x₀)/(q - 1 + x₀)`, the length of `I_s = t([x₀,1]) = [-s, 0]`
(Appendix B).  It equals `-tRe q x₀`, with `tRe` from `RSDefs`. -/
def ptS (q : ℕ) (x0 : ℝ) : ℝ := (1 - x0) / ((q : ℝ) - 1 + x0)

/-- The defining equation of `ptS`. -/
theorem ptS_def (q : ℕ) (x0 : ℝ) : ptS q x0 = (1 - x0) / ((q : ℝ) - 1 + x0) := rfl

/-- `s(x₀) > 0` for `q ≥ 2` and `0 ≤ x₀ < 1`. -/
theorem pt_s_pos {q : ℕ} (hq : 2 ≤ q) {x0 : ℝ} (hx0 : 0 ≤ x0) (hx1 : x0 < 1) :
    0 < ptS q x0 := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  unfold ptS
  apply div_pos <;> linarith

/-- `(q-1) s(x₀) ≤ 1` for `q ≥ 2` and `x₀ ≥ 0`, i.e. `I_s ⊆ I = [-1/(q-1), 0]`. -/
theorem pt_s_mul_le_one {q : ℕ} (hq : 2 ≤ q) {x0 : ℝ} (hx0 : 0 ≤ x0) :
    ((q : ℝ) - 1) * ptS q x0 ≤ 1 := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hden : 0 < (q : ℝ) - 1 + x0 := by linarith
  unfold ptS
  rw [mul_div_assoc', div_le_one hden]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ q) hx0]

/-- The left endpoint `x_s = (1-(q-1)s)/(1+s)` of `prop:zero-free-moment` is `x₀` for
`s = s(x₀)` (Appendix B: "`t([x₀,1]) = I_s` and `x_s = x₀`"). -/
theorem pt_xs_eq {q : ℕ} (hq : 2 ≤ q) {x0 : ℝ} (hx0 : 0 ≤ x0) :
    (1 - ((q : ℝ) - 1) * ptS q x0) / (1 + ptS q x0) = x0 := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hden : 0 < (q : ℝ) - 1 + x0 := by linarith
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  unfold ptS
  have h1 : 1 - ((q : ℝ) - 1) * ((1 - x0) / ((q : ℝ) - 1 + x0)) =
      q * x0 / ((q : ℝ) - 1 + x0) := by
    field_simp; ring
  have h2 : 1 + (1 - x0) / ((q : ℝ) - 1 + x0) = q / ((q : ℝ) - 1 + x0) := by
    field_simp; ring
  rw [h1, h2, div_div_div_cancel_right₀ hden.ne', mul_div_cancel_left₀ _ hq0]

/-- **`eq:positive-temperature-range`** is the condition `d s² < 2 c_q` (Appendix B: "the
condition `d < d₂(q) = 2(q-1)² c_q` is relaxed to `d s² < 2 c_q`").  The hypothesis `q ≥ 3`
is needed because `d2 q` and `cq q` divide by `q(q-2)`, which vanishes at `q = 2`. -/
theorem pt_range_iff {q : ℕ} (hq : 3 ≤ q) {x0 : ℝ} (hx0 : 0 ≤ x0) (hx1 : x0 < 1) (d : ℝ) :
    d < d2 q * (((q : ℝ) - 1 + x0) / (((q : ℝ) - 1) * (1 - x0))) ^ 2 ↔
      d * ptS q x0 ^ 2 < 2 * cq q := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : 0 < (q : ℝ) - 1 := by linarith
  have hden : 0 < (q : ℝ) - 1 + x0 := by linarith
  have h1x : 0 < 1 - x0 := by linarith
  have hs : 0 < ptS q x0 := pt_s_pos (by omega) hx0 hx1
  have key : d2 q * (((q : ℝ) - 1 + x0) / (((q : ℝ) - 1) * (1 - x0))) ^ 2 =
      2 * cq q / ptS q x0 ^ 2 := by
    rw [d2_eq]; unfold ptS; field_simp
  rw [key, lt_div_iff₀ (by positivity)]

/-- For `x₀ ∈ (0,1)` the range `eq:positive-temperature-range` strictly contains `(0, d₂(q))`;
in particular it contains `d = d₂(q)`, so the positive-temperature theorem
(`potts_zero_free_positive_temperature`) reaches densities beyond those of Theorem 1.1. -/
theorem pt_d2_lt_range {q : ℕ} (hq : 3 ≤ q) {x0 : ℝ} (hx0 : 0 < x0) (hx1 : x0 < 1) :
    d2 q < d2 q * (((q : ℝ) - 1 + x0) / (((q : ℝ) - 1) * (1 - x0))) ^ 2 := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : 0 < (q : ℝ) - 1 := by linarith
  have hd2 : 0 < d2 q := by
    rw [d2_eq]; have := cq_pos hq; have := pow_pos hq1 2; positivity
  have hprod : 0 < ((q : ℝ) - 1) * (1 - x0) := mul_pos hq1 (by linarith)
  have hratio : 1 < ((q : ℝ) - 1 + x0) / (((q : ℝ) - 1) * (1 - x0)) := by
    rw [one_lt_div hprod]; nlinarith
  have h2 : 1 < (((q : ℝ) - 1 + x0) / (((q : ℝ) - 1) * (1 - x0))) ^ 2 :=
    one_lt_pow₀ hratio (by norm_num)
  exact lt_mul_of_one_lt_right hd2 h2

end

end ERZeroFreeness
