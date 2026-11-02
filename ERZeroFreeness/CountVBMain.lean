/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.CountVB
import ERZeroFreeness.VBTransfer

/-! # `CountVBMain`: Theorem 1.5(ii), counting assertion, at the coefficient level
(blueprint §10.2)

Composition, as in the paper's "Proof of Theorems 1.2 and 1.5 (counting)": in Step 3 of
Section 7, `𝓘_{G_n,J}` has no zeros in `{|t| ≤ r}` for some `r ∈ (tanh β*, r_d)` w.p. → 1; then
Proposition 8.4(ii) applies.  Imports IV's `VBTransfer` for `vb_disk_zero_free` [VX3]
(`hd`, `0 ≤ R₀`, `R₀ < 1`, `d R₀² < 1`), whose event is literally the hypothesis `hzf` of
`vb_counting_real` with `r = R₀`.
Plan.  `exists_vb_radius` (proved in `docs/counting/scratch-proofs.lean`): pick `r` strictly
between `max (tanh β*) 0` and `min 1 (√(1/d))` (`exists_between`, `Real.lt_sqrt`).
`viana_bray_counting`: `exists_vb_radius`, then `vb_disk_zero_free hd hr0 hr1 hdr` and
`vb_counting_real hd hβs hr _ hB`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

section CountVBMain

/-- [VC.1] The radius of Step 3 of Section 7: if `d tanh²β* < 1`, some `r > tanh β*` has
`0 ≤ r < 1` and `d r² < 1` (i.e. `r < r_d = min{1, d^{-1/2}}`). -/
theorem exists_vb_radius {d : ℝ} (hd : 0 < d) {βs : ℝ} (hdβ : d * Real.tanh βs ^ 2 < 1) :
    ∃ r : ℝ, Real.tanh βs < r ∧ 0 ≤ r ∧ r < 1 ∧ d * r ^ 2 < 1 := by
  have hs1 : Real.tanh βs < 1 := Real.tanh_lt_one βs
  have hsqrt : 0 < Real.sqrt (1 / d) := Real.sqrt_pos.mpr (by positivity)
  have hu0 : 0 < min 1 (Real.sqrt (1 / d)) := lt_min one_pos hsqrt
  have hsu : max (Real.tanh βs) 0 < min 1 (Real.sqrt (1 / d)) := by
    refine max_lt (lt_min hs1 ?_) hu0
    rcases lt_or_ge (Real.tanh βs) 0 with h | h
    · linarith
    · rw [Real.lt_sqrt h, lt_div_iff₀ hd]
      linarith
  obtain ⟨r, hr1, hr2⟩ := exists_between hsu
  have hr0 : 0 ≤ r := (le_max_right _ _).trans hr1.le
  have hrs : r < Real.sqrt (1 / d) := lt_of_lt_of_le hr2 (min_le_right _ _)
  rw [Real.lt_sqrt hr0, lt_div_iff₀ hd] at hrs
  exact ⟨r, lt_of_le_of_lt (le_max_left _ _) hr1, hr0, lt_of_lt_of_le hr2 (min_le_left _ _),
    by linarith⟩

/-- [VC.2] **Theorem 1.5(ii) `thm:ising-applications`, counting assertion, coefficient level.**
Fix `d > 0` and `β* > 0` with `d tanh²β* < 1`, and `B > 2e(d+1)`.  There is `C` such that, with
probability tending to one over `(G_n, J)`, `eq:connected-set-bound` holds and, simultaneously
for all `β ∈ [-β*, β*]`, `ε ∈ (0,1)` and `k ≥ C log(n/ε)`,
`(1-ε) Z^{VB}_{G_n,J}(β) ≤ Z̃_k(β) ≤ (1+ε) Z^{VB}_{G_n,J}(β)` (both real), where
`Z̃_k(β) = 2^n cosh(β)^{|E|} exp(∑_{j ≤ k} ℓ_j(G_n) tanh(β)^j)` (`vbApprox`). -/
theorem viana_bray_counting {d : ℝ} (hd : 0 < d) {βs : ℝ} (hβs : 0 < βs)
    (hdβ : d * Real.tanh βs ^ 2 < 1) {B : ℝ} (hB : 2 * Real.exp 1 * (d + 1) < B) :
    ∃ C : ℝ, Tendsto (fun n : ℕ => sgProb n (d / n)
      {GJ | ConnSetBound B GJ.1 ∧
        ∀ β ∈ Set.Icc (-βs) βs, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ k : ℕ,
          C * Real.log (n / ε) ≤ k →
            ∃ x y : ℝ, vbApprox GJ.1 (fun e => boolSign (GJ.2 e)) k β = x ∧
              vbZ GJ.1 (fun e => boolSign (GJ.2 e)) β = y ∧
              (1 - ε) * y ≤ x ∧ x ≤ (1 + ε) * y})
      atTop (𝓝 1) := by
  obtain ⟨r, hr, hr0, hr1, hdr⟩ := exists_vb_radius hd hdβ
  exact vb_counting_real hd hβs hr (vb_disk_zero_free hd hr0 hr1 hdr) hB

end CountVBMain

end

end ERZeroFreeness
