/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.IsingRelation
import ERZeroFreeness.IsingRademacher

/-!
# The Viana–Bray partition function (`eq:viana-bray`)

* `exp_mul_sign`: `exp(βs) = cosh β (1 + s tanh β)` for `s = ±1`.
* `vbZ_eq`: `eq:viana-bray`, `Z^{VB}_{G,J}(β) = 2^n (cosh β)^{|E(G)|} 𝓘_{G,J}(tanh β)` for edge
  signs `J_e = ±1` and `cosh β ≠ 0`.
* `vb_beta_nbhd`: if `tanh β_* < R`, then for some `ρ > 0` every `β` with
  `dist(β, [-β_*, β_*]) ≤ ρ` has `cosh β ≠ 0` and `|tanh β| ≤ R` (continuity and compactness).
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- `exp(βs) = cosh β (1 + s tanh β)` for `s = ±1` and `cosh β ≠ 0`. -/
theorem exp_mul_sign {β : ℂ} (hβ : Complex.cosh β ≠ 0) {s : ℂ} (hs : s = 1 ∨ s = -1) :
    Complex.exp (β * s) = Complex.cosh β * (1 + s * Complex.tanh β) := by
  rw [Complex.tanh_eq_sinh_div_cosh]
  rcases hs with rfl | rfl
  · rw [mul_one, mul_add, mul_one, one_mul, mul_div_cancel₀ _ hβ, Complex.cosh_add_sinh]
  · rw [mul_neg, mul_one, mul_add, mul_one, neg_one_mul, mul_neg, mul_div_cancel₀ _ hβ,
      ← sub_eq_add_neg, Complex.cosh_sub_sinh]

/-- Evaluation of `P_{H,J}` (the statement of `signedPoly_eval`). -/
private lemma VBRelation_signedPoly_eval {V : Type*} [Fintype V] (H : SimpleGraph V) (q : ℕ)
    (J : Sym2 V → ℤ) (t : ℂ) :
    (signedPoly H q J).eval t =
      ((q : ℂ) ^ Fintype.card V)⁻¹ *
        ∑ σ : V → Fin q, ∏ e ∈ H.edgeFinset, (1 + t * ((J e : ℂ) * edgeA q σ e)) := by
  simp only [signedPoly, eval_mul, eval_C, eval_finsetSum, eval_prod, eval_add, eval_one,
    eval_X]
  congr 1
  exact Finset.sum_congr rfl fun σ _ => Finset.prod_congr rfl fun e _ => by ring

/-- For `q = 2`, `A_σ(e) = σ_u σ_v ∈ {1, -1}` (straight from the definition of `edgeA`). -/
private lemma VBRelation_edgeA_two_sign {V : Type*} (σ : V → Fin 2) (e : Sym2 V) :
    edgeA 2 σ e = 1 ∨ edgeA 2 σ e = -1 := by
  unfold edgeA
  split_ifs
  · left; norm_num
  · right; rfl

/-- A product of two signs is a sign. -/
private lemma VBRelation_sign_mul {a b : ℂ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

/-- One spin configuration: `exp(β ∑_e J_e A_e) = cosh^{|E|}β ∏_e (1 + tanh β · J_e A_e)`. -/
private lemma VBRelation_term {V : Type*} [Fintype V] (G : SimpleGraph V) (J : Sym2 V → ℤ)
    (hJ : ∀ e ∈ G.edgeFinset, J e = 1 ∨ J e = -1) {β : ℂ} (hβ : Complex.cosh β ≠ 0)
    (σ : V → Fin 2) :
    Complex.exp (β * ∑ e ∈ G.edgeFinset, (J e : ℂ) * edgeA 2 σ e) =
      Complex.cosh β ^ G.edgeFinset.card *
        ∏ e ∈ G.edgeFinset, (1 + Complex.tanh β * ((J e : ℂ) * edgeA 2 σ e)) := by
  rw [Finset.mul_sum, Complex.exp_sum, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e he => ?_
  have hs : (J e : ℂ) * edgeA 2 σ e = 1 ∨ (J e : ℂ) * edgeA 2 σ e = -1 := by
    refine VBRelation_sign_mul ?_ (VBRelation_edgeA_two_sign σ e)
    rcases hJ e he with h | h <;> simp [h]
  rw [exp_mul_sign hβ hs, mul_comm ((J e : ℂ) * edgeA 2 σ e)]

/-- **`eq:viana-bray`**: `Z^{VB}_{G,J}(β) = 2^n (cosh β)^{|E(G)|} 𝓘_{G,J}(tanh β)` for edge signs
`J_e ∈ {1, -1}` and `cosh β ≠ 0`. -/
theorem vbZ_eq {V : Type*} [Fintype V] (G : SimpleGraph V) (J : Sym2 V → ℤ)
    (hJ : ∀ e ∈ G.edgeFinset, J e = 1 ∨ J e = -1) {β : ℂ} (hβ : Complex.cosh β ≠ 0) :
    vbZ G J β = 2 ^ Fintype.card V * Complex.cosh β ^ G.edgeFinset.card *
      (signedPoly G 2 J).eval (Complex.tanh β) := by
  rw [VBRelation_signedPoly_eval]
  unfold vbZ
  rw [Finset.sum_congr rfl fun σ _ => VBRelation_term G J hJ hβ σ, ← Finset.mul_sum]
  have h2 : (2 : ℂ) ^ Fintype.card V * (((2 : ℕ) : ℂ) ^ Fintype.card V)⁻¹ = 1 := by
    rw [Nat.cast_ofNat]
    exact mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero)
  linear_combination (-(Complex.cosh β ^ G.edgeFinset.card *
    ∑ σ : V → Fin 2, ∏ e ∈ G.edgeFinset,
      (1 + Complex.tanh β * ((J e : ℂ) * edgeA 2 σ e)))) * h2

/-- For real `x` with `|x| ≤ β_*`: `|sinh x| ≤ tanh β_* · cosh x` (i.e. `|tanh x| ≤ tanh β_*`),
from `sinh(β_* - |x|) ≥ 0`. -/
private lemma VBRelation_abs_sinh_le {βs x : ℝ} (hx : |x| ≤ βs) :
    |Real.sinh x| ≤ Real.tanh βs * Real.cosh x := by
  have hc : 0 < Real.cosh βs := Real.cosh_pos βs
  have h1 : 0 ≤ Real.sinh (βs - |x|) := Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr hx)
  rw [Real.sinh_sub] at h1
  rw [Real.abs_sinh, Real.tanh_eq_sinh_div_cosh, ← Real.cosh_abs x, div_mul_eq_mul_div,
    le_div_iff₀ hc]
  linarith

/-- The set `U = {β : ‖sinh β‖ < R ‖cosh β‖}` is open. -/
private lemma VBRelation_isOpen (R : ℝ) :
    IsOpen {β : ℂ | ‖Complex.sinh β‖ < R * ‖Complex.cosh β‖} :=
  isOpen_lt Complex.continuous_sinh.norm (continuous_const.mul Complex.continuous_cosh.norm)

/-- On `U`: `cosh β ≠ 0` and `‖tanh β‖ ≤ R`. -/
private lemma VBRelation_of_mem {R : ℝ} {β : ℂ}
    (h : ‖Complex.sinh β‖ < R * ‖Complex.cosh β‖) :
    Complex.cosh β ≠ 0 ∧ ‖Complex.tanh β‖ ≤ R := by
  have hc : Complex.cosh β ≠ 0 := by
    intro h0
    rw [h0, norm_zero, mul_zero] at h
    exact absurd h (not_lt.mpr (norm_nonneg _))
  refine ⟨hc, ?_⟩
  rw [Complex.tanh_eq_sinh_div_cosh, norm_div, div_le_iff₀ (norm_pos_iff.mpr hc)]
  exact h.le

/-- The real points of `[-β_*, β_*]` lie in `U`. -/
private lemma VBRelation_real_mem {βs R : ℝ} (hR : Real.tanh βs < R) {x : ℝ}
    (hx : x ∈ Set.Icc (-βs) βs) :
    ‖Complex.sinh x‖ < R * ‖Complex.cosh x‖ := by
  rw [← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos x)]
  calc |Real.sinh x| ≤ Real.tanh βs * Real.cosh x := VBRelation_abs_sinh_le (abs_le.mpr hx)
    _ < R * Real.cosh x := mul_lt_mul_of_pos_right hR (Real.cosh_pos x)

/-- Continuity and compactness near `[-β_*, β_*]`: if `tanh β_* < R`, there is `ρ > 0` such that
`cosh β ≠ 0` and `|tanh β| ≤ R` whenever `dist(β, [-β_*, β_*]) ≤ ρ`. -/
theorem vb_beta_nbhd {βs R : ℝ} (hR : Real.tanh βs < R) :
    ∃ ρ > 0, ∀ β : ℂ, (∃ x : ℝ, x ∈ Set.Icc (-βs) βs ∧ ‖β - x‖ ≤ ρ) →
      Complex.cosh β ≠ 0 ∧ ‖Complex.tanh β‖ ≤ R := by
  set K : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Set.Icc (-βs) βs with hK
  have hKc : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hKU : K ⊆ {β : ℂ | ‖Complex.sinh β‖ < R * ‖Complex.cosh β‖} := by
    rintro _ ⟨x, hx, rfl⟩
    exact VBRelation_real_mem hR hx
  obtain ⟨ρ, hρ, hsub⟩ := hKc.exists_cthickening_subset_open (VBRelation_isOpen R) hKU
  refine ⟨ρ, hρ, fun β ⟨x, hx, hβx⟩ => VBRelation_of_mem (hsub ?_)⟩
  exact Metric.mem_cthickening_of_dist_le β x ρ K ⟨x, hx, rfl⟩ (by rwa [dist_eq_norm])

end

end ERZeroFreeness
