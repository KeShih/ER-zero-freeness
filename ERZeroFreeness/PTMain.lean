/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Main
import ERZeroFreeness.PTParams
import ERZeroFreeness.PTFirstMoment

/-! # Positive-temperature zero-freeness (Appendix B)

For `q ≥ 3`, `x₀ ∈ (0,1)` and `d` in the range `eq:positive-temperature-range`, with probability
tending to one `Z_{G_n}(q,·)` has no zeros within a fixed distance of `[x₀,1]`
(`potts_zero_free_positive_temperature`), and `Ẑ_{G_n}` has no zeros on a closed tube around
`I_s = t([x₀,1])` (`pt_zero_free_tplane`).

Proof.  `pt_zero_free_interval`: `s < 1` since `2s ≤ (q-1)s ≤ 1`, and `d s² < 2c_q < 1`
(`cq_lt_half`); `pt_first_moment_bound` gives the first-moment hypothesis of
`prop_zero_free_moment`.  `pt_zero_free_tplane` applies `zero_free_of_first_moment` to the same
inputs for `s = ptS q x₀` (`pt_s_pos`, `pt_s_mul_le_one`, `pt_range_iff`).
`potts_zero_free_positive_temperature` is `pt_zero_free_interval` for `s = ptS q x₀`, where
`x_s = x₀` (`pt_xs_eq`).
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- Zero-freeness of `Z_{G_n}(q,·)` near `[x_s, 1]`, `x_s = (1-(q-1)s)/(1+s)`, for every `s > 0`
with `(q-1)s ≤ 1` and `d s² < 2 c_q` (the argument of Appendix B for a general interval
`I_s`). -/
theorem pt_zero_free_interval {q : ℕ} (hq : 3 ≤ q) {d : ℝ} (hd : 0 < d) {s : ℝ} (hs0 : 0 < s)
    (hsq : ((q : ℝ) - 1) * s ≤ 1) (hds : d * s ^ 2 < 2 * cq q) :
    ∃ ρ > 0, Tendsto (fun n : ℕ => erProb n (d / n)
        {G | ∀ z : ℂ, (∃ x : ℝ, x ∈ Set.Icc ((1 - ((q : ℝ) - 1) * s) / (1 + s)) 1 ∧
          ‖z - x‖ ≤ ρ) → pottsZ G q z ≠ 0}) atTop (𝓝 1) := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hs1 : s < 1 := by
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ (q : ℝ) - 1) hs0.le]
  have hds1 : d * s ^ 2 < 1 := by have := cq_lt_half hq; linarith
  obtain ⟨r, hr, B, hmom⟩ := pt_first_moment_bound hq hd hs0 hsq hds
  exact prop_zero_free_moment (by omega) hd hs0 hs1 hsq hds1 hr hmom

/-- **Appendix B, `t`-plane form.** For `q ≥ 3`, `x₀ ∈ (0,1)` and `d` in the range
`eq:positive-temperature-range`, there is `ρ > 0` such that with probability tending to one
`Ẑ_{G_n}` has no zeros in `L_ρ(I_s)`, `I_s = t([x₀,1]) = [-(1-x₀)/(q-1+x₀), 0]` (Appendix B:
"`Ẑ_{G_n}` has no zeros in `L_{ρ'}(I_s)`"; the `z`-plane half of that sentence is
`potts_zero_free_positive_temperature`). -/
theorem pt_zero_free_tplane {q : ℕ} (hq : 3 ≤ q) {x0 : ℝ} (hx0 : 0 < x0) (hx1 : x0 < 1)
    {d : ℝ} (hd : 0 < d)
    (hdx : d < d2 q * (((q : ℝ) - 1 + x0) / (((q : ℝ) - 1) * (1 - x0))) ^ 2) :
    ∃ ρ > 0, Tendsto (fun n : ℕ => erProb n (d / n)
        {G | ∀ t ∈ tube ((1 - x0) / ((q : ℝ) - 1 + x0)) ρ, (zhat G q).eval t ≠ 0})
      atTop (𝓝 1) := by
  have hq2 : 2 ≤ q := by omega
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hs0 := pt_s_pos hq2 hx0.le hx1
  have hsq := pt_s_mul_le_one hq2 hx0.le
  have hds := (pt_range_iff hq hx0.le hx1 d).1 hdx
  have hs1 : ptS q x0 < 1 := by
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ (q : ℝ) - 1) hs0.le]
  have hds1 : d * ptS q x0 ^ 2 < 1 := by have := cq_lt_half hq; linarith
  obtain ⟨r, hr, B, hmom⟩ := pt_first_moment_bound hq hd hs0 hsq hds
  exact zero_free_of_first_moment hq2 hd hs0 hs1 hsq hds1 hr hmom

/-- **Positive-temperature zero-freeness (`eq:positive-temperature-range`, Appendix B
`app:positive-temperature`).** Fix an integer `q ≥ 3`, `x₀ ∈ (0,1)` and
`0 < d < d₂(q) ((q-1+x₀)/((q-1)(1-x₀)))²`.  There is `ρ > 0`, independent of `n`, such that
with probability tending to one over `G_n ∼ G(n, d/n)`, `Z_{G_n}(q,z) ≠ 0` whenever
`dist(z,[x₀,1]) ≤ ρ`.  (As in `potts_zero_free`, `G(n,d/n)` is only meaningful for `n ≥ d`;
the finitely many `n < d` do not affect the limit.) -/
theorem potts_zero_free_positive_temperature {q : ℕ} (hq : 3 ≤ q) {x0 : ℝ} (hx0 : 0 < x0)
    (hx1 : x0 < 1) {d : ℝ} (hd : 0 < d)
    (hdx : d < d2 q * (((q : ℝ) - 1 + x0) / (((q : ℝ) - 1) * (1 - x0))) ^ 2) :
    ∃ ρ > 0, Tendsto (fun n : ℕ => erProb n (d / n)
        {G | ∀ z : ℂ, (∃ x : ℝ, x ∈ Set.Icc x0 1 ∧ ‖z - x‖ ≤ ρ) → pottsZ G q z ≠ 0})
      atTop (𝓝 1) := by
  have hq2 : 2 ≤ q := by omega
  have hs0 := pt_s_pos hq2 hx0.le hx1
  have hsq := pt_s_mul_le_one hq2 hx0.le
  have hds := (pt_range_iff hq hx0.le hx1 d).1 hdx
  obtain ⟨ρ, hρ, hlim⟩ := pt_zero_free_interval hq hd hs0 hsq hds
  rw [pt_xs_eq hq2 hx0.le] at hlim
  exact ⟨ρ, hρ, hlim⟩

end

end ERZeroFreeness
