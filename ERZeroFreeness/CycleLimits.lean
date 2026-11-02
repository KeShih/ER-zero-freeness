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

/-!
# Short cycles and Taylor coefficients: `lem:cycle-counts` and `lem:jets` in the paper's form

* `cycleCounts_tendsto_poisson` (**`lem:cycle-counts`**): for every `m = r + 2 ≥ 2`, the joint
  law of `(C_3(G_n), …, C_m(G_n))` converges to that of independent `Pois(d^ℓ/(2ℓ))`
  variables.  For `ℕ^r`-valued vectors, convergence in distribution is pointwise convergence
  of the mass functions, which is what is stated.
* `zhat_coeff_eq_cyclePoly_whp` (**`lem:jets`**, first assertion): with probability tending to
  one, the Taylor coefficients of `Ẑ_{G_n}` at `t = 0` through degree `m` are those of
  `∏_{3 ≤ ℓ ≤ m} (1 + (q-1) t^ℓ)^{C_ℓ(G_n)}`.

The proof of Theorem 1.1 (`Transfer`) uses the ingredients of these two statements directly:
`tendsto_erExp_cycle_descFactorial` with `tendsto_prob_eq_of_factorial_moments`, and
`zhat_coeff_eq_cyclePoly_coeff` with `tendsto_erProb_hasDenseSubgraph`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- **`lem:cycle-counts`.** For every `r`, `(C_3(G_n), …, C_{r+2}(G_n))` converges in law to
independent Poisson variables with means `λ_ℓ = d^ℓ/(2ℓ)`. -/
theorem cycleCounts_tendsto_poisson {d : ℝ} (hd : 0 < d) (r : ℕ) (x : Fin r → ℕ) :
    Tendsto (fun n : ℕ => erProb n (d / n) {G | cycleCounts r G = x}) atTop
      (𝓝 (poisProd (fun i : Fin r => cycleMean d i) x)) := by
  have hw : ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), 0 ≤ erWeight n (d / n) G := by
    filter_upwards [eventually_ge_atTop ⌈d⌉₊] with n hn G
    have hdn : d ≤ (n : ℝ) := (Nat.le_ceil d).trans (by exact_mod_cast hn)
    obtain ⟨h0, h1⟩ := div_natCast_mem_Icc hd.le hdn
    exact erWeight_nonneg h0 h1 G
  have hlam : ∀ i : Fin r, 0 ≤ cycleMean d i := fun i => by
    unfold cycleMean; positivity
  have h := tendsto_prob_eq_of_factorial_moments (fun n G => erWeight n (d / n) G) hw
    (fun n G => cycleCounts r G) hlam
    (fun k => by simpa [erExp] using tendsto_erExp_cycle_descFactorial hd r k) x
  simp only [erProb, Set.mem_ofPred_eq]
  convert h

/-- **`lem:jets`.** With probability tending to one, `Ẑ_{G_n}(t)` and
`∏_{3 ≤ ℓ ≤ r+2} (1 + (q-1) t^ℓ)^{C_ℓ(G_n)}` have the same Taylor coefficients at `0` through
degree `r + 2`. -/
theorem zhat_coeff_eq_cyclePoly_whp {q : ℕ} (hq : 2 ≤ q) {d : ℝ} (hd : 0 < d) (r : ℕ) :
    Tendsto (fun n : ℕ => erProb n (d / n)
        {G | ∀ k ≤ r + 2, (zhat G q).coeff k = (cyclePoly q r (cycleCounts r G)).coeff k})
      atTop (𝓝 1) := by
  have hbad := tendsto_erProb_hasDenseSubgraph hd (2 * (r + 2))
  have hcompl : Tendsto (fun n : ℕ => 1 - erProb n (d / n)
      {G | HasDenseSubgraph G (2 * (r + 2))}) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hbad
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hcompl tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop ⌈d⌉₊] with n hn
    have hdn : d ≤ (n : ℝ) := (Nat.le_ceil d).trans (by exact_mod_cast hn)
    obtain ⟨h0, h1⟩ := div_natCast_mem_Icc hd.le hdn
    rw [← erProb_compl]
    exact erProb_mono h0 h1 fun G hG => zhat_coeff_eq_cyclePoly_coeff hq r G hG
  · filter_upwards [eventually_ge_atTop ⌈d⌉₊] with n hn
    have hdn : d ≤ (n : ℝ) := (Nat.le_ceil d).trans (by exact_mod_cast hn)
    obtain ⟨h0, h1⟩ := div_natCast_mem_Icc hd.le hdn
    exact erProb_le_one h0 h1 _

end

end ERZeroFreeness
