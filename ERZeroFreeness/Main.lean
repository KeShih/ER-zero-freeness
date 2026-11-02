/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs
import ERZeroFreeness.Normalize
import ERZeroFreeness.ErdosRenyi
import ERZeroFreeness.Transfer
import ERZeroFreeness.Entropy
import ERZeroFreeness.FirstMoment

/-!
# Potts zero-freeness on `G(n, d/n)` (`thm:zero-free`)

`prop_zero_free_moment` (`prop:zero-free-moment`) combines the `t`-plane zero-freeness
`zero_free_of_first_moment` with the return to the `z`-plane `zplane_of_tplane`.  With
`s = 1/(q-1)`, so that `x_s = 0`, and the first-moment bound `first_moment_bound`, it gives
Theorem 1.1 (`potts_zero_free`).
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- **`prop:zero-free-moment`.** A uniform first-moment bound on a tube around
`I_s = [-s,0]` (`0 < s < 1`, `(q-1)s ≤ 1`, `ds² < 1`) gives, with probability tending to one,
zero-freeness of `Z_{G_n}(q,·)` on a fixed neighbourhood of `[x_s, 1]`,
`x_s = (1-(q-1)s)/(1+s)`. -/
theorem prop_zero_free_moment {q : ℕ} (hq : 2 ≤ q) {d : ℝ} (hd : 0 < d) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hsq : ((q : ℝ) - 1) * s ≤ 1) (hds : d * s ^ 2 < 1)
    {r B : ℝ} (hr : 0 < r)
    (hmom : ∀ n : ℕ, d ≤ n → ∀ t ∈ tube s r,
      erExp n (d / n) (fun G => ‖(zhat G q).eval t‖) ≤ B) :
    ∃ ρz > 0, Tendsto (fun n : ℕ => erProb n (d / n)
        {G | ∀ z : ℂ, (∃ x : ℝ, x ∈ Set.Icc ((1 - ((q : ℝ) - 1) * s) / (1 + s)) 1 ∧
          ‖z - x‖ ≤ ρz) → pottsZ G q z ≠ 0}) atTop (𝓝 1) := by
  -- `t`-plane zero-freeness on `L_ρ(I_s)` with probability tending to one
  obtain ⟨ρ, hρ, hlim⟩ := zero_free_of_first_moment hq hd hs0 hs1 hsq hds hr hmom
  -- return to the `z`-plane, uniformly in the graph
  obtain ⟨ρz, hρz, hz⟩ := zplane_of_tplane hq hs0.le hsq hρ
  refine ⟨ρz, hρz, ?_⟩
  -- for `n ≥ d` the edge probability `d/n` lies in `[0,1]`
  have hn0 : ∀ᶠ n : ℕ in atTop, d ≤ n := by
    filter_upwards [eventually_ge_atTop ⌈d⌉₊] with n hn
    exact (Nat.le_ceil d).trans (by exact_mod_cast hn)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_ ?_
  · filter_upwards [hn0] with n hn
    obtain ⟨hp0, hp1⟩ := div_natCast_mem_Icc hd.le hn
    exact erProb_mono hp0 hp1 fun G hG => hz n G hG
  · filter_upwards [hn0] with n hn
    obtain ⟨hp0, hp1⟩ := div_natCast_mem_Icc hd.le hn
    exact erProb_le_one hp0 hp1 _

/-- **`thm:zero-free` (Theorem 1.1).** Fix an integer `q ≥ 3` and `0 < d < d₂(q)`.  There is
`ρ > 0`, independent of `n`, such that with probability tending to one over
`G_n ∼ G(n, d/n)`, `Z_{G_n}(q, z) ≠ 0` for every `z` with `dist(z, [0,1]) ≤ ρ`. -/
theorem potts_zero_free {q : ℕ} (hq : 3 ≤ q) {d : ℝ} (hd : 0 < d) (hd2 : d < d2 q) :
    ∃ ρ > 0, Tendsto (fun n : ℕ => erProb n (d / n)
        {G | ∀ z ∈ Kρ ρ, pottsZ G q z ≠ 0}) atTop (𝓝 1) := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  -- the parameter `s = 1/(q-1)`
  have hs0 : 0 < 1 / ((q : ℝ) - 1) := by positivity
  have hs1 : 1 / ((q : ℝ) - 1) < 1 := by
    rw [div_lt_one hq1]
    linarith
  have hsq1 : ((q : ℝ) - 1) * (1 / ((q : ℝ) - 1)) = 1 := by
    rw [mul_one_div, div_self hq1.ne']
  -- `d s² < 1` from `d < d₂(q) < (q-1)²`
  have hds : d * (1 / ((q : ℝ) - 1)) ^ 2 < 1 := by
    have hdq : d < ((q : ℝ) - 1) ^ 2 := hd2.trans (d2_lt_sq hq)
    rw [div_pow, one_pow, mul_one_div, div_lt_one (by positivity)]
    exact hdq
  obtain ⟨r, hr, B, hmom⟩ := first_moment_bound hq hd hd2
  obtain ⟨ρz, hρz, hlim⟩ :=
    prop_zero_free_moment (by omega : 2 ≤ q) hd hs0 hs1 hsq1.le hds hr hmom
  refine ⟨ρz, hρz, ?_⟩
  -- `x_s = (1 - (q-1)s)/(1+s) = 0`, so the interval `[x_s, 1]` is `[0, 1]`
  have hxs : (1 - ((q : ℝ) - 1) * (1 / ((q : ℝ) - 1))) / (1 + 1 / ((q : ℝ) - 1)) = 0 := by
    rw [hsq1, sub_self, zero_div]
  rw [hxs] at hlim
  exact hlim

end

end ERZeroFreeness
