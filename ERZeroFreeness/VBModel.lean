/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.IsingVBDefs
import ERZeroFreeness.ErdosRenyi

/-!
# The signed Erdős–Rényi model

Basic facts about `sgWeight`, `sgProb` and `sgExp`: the law of `(G, J)` with `G ∼ G(n,p)` and
independent uniform signs `J_e` on all pairs `e ∈ Sym2 (Fin n)`, the model of the Viana–Bray
spin glass in Theorem 1.5(ii) (`thm:ising-applications`).  The weights form a probability
distribution for `0 ≤ p ≤ 1`; an event that depends on `G` only has its `G(n,p)` probability
(`sgProb_fst`); `sgProb` and `sgExp` satisfy monotonicity, the union bound and linearity.
`sum_bool_prod` averages a product of functions of independent uniform signs.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- The number of sign vectors `J : Sym2 (Fin n) → Bool` is `2^N`, `N = |Sym2 (Fin n)|`. -/
private lemma VBModel_card_signs (n : ℕ) :
    (Fintype.card (Sym2 (Fin n) → Bool) : ℝ) = 2 ^ Fintype.card (Sym2 (Fin n)) := by
  rw [Fintype.card_fun, Fintype.card_bool]
  push_cast
  rfl

/-- Summing the signed weight over the signs gives back the `G(n,p)` weight. -/
private lemma VBModel_sum_sgWeight_signs (n : ℕ) (p : ℝ) (G : SimpleGraph (Fin n)) :
    ∑ J : Sym2 (Fin n) → Bool, sgWeight n p G J = erWeight n p G := by
  have h2 : (2 : ℝ) ^ Fintype.card (Sym2 (Fin n)) ≠ 0 := pow_ne_zero _ two_ne_zero
  simp only [sgWeight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, VBModel_card_signs]
  field_simp

/-- The signed weights are nonnegative for `0 ≤ p ≤ 1`. -/
theorem sgWeight_nonneg {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (G : SimpleGraph (Fin n)) (J : Sym2 (Fin n) → Bool) : 0 ≤ sgWeight n p G J := by
  rw [sgWeight]
  exact div_nonneg (erWeight_nonneg hp0 hp1 G) (pow_nonneg zero_le_two _)

/-- The signed weights sum to `1`. -/
theorem sum_sgWeight (n : ℕ) (p : ℝ) :
    ∑ G : SimpleGraph (Fin n), ∑ J : Sym2 (Fin n) → Bool, sgWeight n p G J = 1 := by
  rw [Finset.sum_congr rfl fun G _ => VBModel_sum_sgWeight_signs n p G]
  exact sum_erWeight n p

/-- `sgProb` as a single sum over pairs `(G, J)`. -/
theorem sgProb_eq_sum (n : ℕ) (p : ℝ)
    (A : Set (SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool))) :
    sgProb n p A = ∑ GJ : SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool),
      if GJ ∈ A then sgWeight n p GJ.1 GJ.2 else 0 := by
  rw [sgProb, Fintype.sum_prod_type]

/-- `sgExp` as a single sum over pairs `(G, J)`. -/
theorem sgExp_eq_sum (n : ℕ) (p : ℝ)
    (f : SimpleGraph (Fin n) → (Sym2 (Fin n) → Bool) → ℝ) :
    sgExp n p f = ∑ GJ : SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool),
      sgWeight n p GJ.1 GJ.2 * f GJ.1 GJ.2 := by
  rw [sgExp, Fintype.sum_prod_type]

/-- An event that depends on `G` only has its `G(n,p)` probability. -/
theorem sgProb_fst (n : ℕ) (p : ℝ) (A : Set (SimpleGraph (Fin n))) :
    sgProb n p {GJ | GJ.1 ∈ A} = erProb n p A := by
  rw [sgProb, erProb]
  refine Finset.sum_congr rfl fun G _ => ?_
  by_cases hG : G ∈ A
  · have h : ∀ J : Sym2 (Fin n) → Bool, (G, J) ∈ {GJ : SimpleGraph (Fin n) ×
        (Sym2 (Fin n) → Bool) | GJ.1 ∈ A} := fun J => hG
    simp only [h, if_true, hG]
    exact VBModel_sum_sgWeight_signs n p G
  · have h : ∀ J : Sym2 (Fin n) → Bool, (G, J) ∉ {GJ : SimpleGraph (Fin n) ×
        (Sym2 (Fin n) → Bool) | GJ.1 ∈ A} := fun J => hG
    simp only [h, if_false, hG, Finset.sum_const_zero]

/-- Probabilities are nonnegative for `0 ≤ p ≤ 1`. -/
theorem sgProb_nonneg {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool))) : 0 ≤ sgProb n p A := by
  refine Finset.sum_nonneg fun G _ => Finset.sum_nonneg fun J _ => ?_
  split_ifs
  · exact sgWeight_nonneg hp0 hp1 G J
  · exact le_rfl

/-- Monotonicity of `sgProb` for `0 ≤ p ≤ 1`. -/
theorem sgProb_mono {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {A B : Set (SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool))} (h : A ⊆ B) :
    sgProb n p A ≤ sgProb n p B := by
  refine Finset.sum_le_sum fun G _ => Finset.sum_le_sum fun J _ => ?_
  by_cases hA : (G, J) ∈ A
  · rw [if_pos hA, if_pos (h hA)]
  · rw [if_neg hA]
    split_ifs
    · exact sgWeight_nonneg hp0 hp1 G J
    · exact le_rfl

/-- The union bound, for `0 ≤ p ≤ 1`. -/
theorem sgProb_union_le {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A B : Set (SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool))) :
    sgProb n p (A ∪ B) ≤ sgProb n p A + sgProb n p B := by
  rw [sgProb, sgProb, sgProb, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun G _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun J _ => ?_
  have hw := sgWeight_nonneg hp0 hp1 G J
  by_cases hA : (G, J) ∈ A
  · rw [if_pos (Set.mem_union_left B hA), if_pos hA]
    split_ifs <;> linarith
  · by_cases hB : (G, J) ∈ B
    · rw [if_pos (Set.mem_union_right A hB), if_pos hB, if_neg hA, zero_add]
    · rw [if_neg (fun h => h.elim hA hB), if_neg hA, if_neg hB, add_zero]

/-- The probability of the complement. -/
theorem sgProb_compl {n : ℕ} {p : ℝ} (A : Set (SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool))) :
    sgProb n p Aᶜ = 1 - sgProb n p A := by
  have h : sgProb n p Aᶜ + sgProb n p A = 1 := by
    rw [sgProb, sgProb, ← Finset.sum_add_distrib, ← sum_sgWeight n p]
    refine Finset.sum_congr rfl fun G _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun J _ => ?_
    by_cases hA : (G, J) ∈ A
    · rw [if_neg (Set.notMem_compl_iff.mpr hA), if_pos hA, zero_add]
    · rw [if_pos (Set.mem_compl hA), if_neg hA, add_zero]
  linarith

/-- Probabilities are at most `1` for `0 ≤ p ≤ 1`. -/
theorem sgProb_le_one {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool))) : sgProb n p A ≤ 1 := by
  have huniv : sgProb n p Set.univ = 1 := by
    simp only [sgProb, Set.mem_univ, if_true]
    exact sum_sgWeight n p
  rw [← huniv]
  exact sgProb_mono hp0 hp1 (Set.subset_univ A)

/-- Monotonicity of `sgExp` for `0 ≤ p ≤ 1`. -/
theorem sgExp_mono {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : SimpleGraph (Fin n) → (Sym2 (Fin n) → Bool) → ℝ} (h : ∀ G J, f G J ≤ g G J) :
    sgExp n p f ≤ sgExp n p g := by
  exact Finset.sum_le_sum fun G _ => Finset.sum_le_sum fun J _ =>
    mul_le_mul_of_nonneg_left (h G J) (sgWeight_nonneg hp0 hp1 G J)

/-- Additivity of `sgExp`. -/
theorem sgExp_add {n : ℕ} {p : ℝ} (f g : SimpleGraph (Fin n) → (Sym2 (Fin n) → Bool) → ℝ) :
    sgExp n p (fun G J => f G J + g G J) = sgExp n p f + sgExp n p g := by
  simp only [sgExp, mul_add, Finset.sum_add_distrib]

/-- `sgExp` commutes with multiplication by a constant. -/
theorem sgExp_const_mul {n : ℕ} {p : ℝ} (c : ℝ)
    (f : SimpleGraph (Fin n) → (Sym2 (Fin n) → Bool) → ℝ) :
    sgExp n p (fun G J => c * f G J) = c * sgExp n p f := by
  simp only [sgExp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun G _ => Finset.sum_congr rfl fun J _ => by ring

/-- The expectation of a constant. -/
theorem sgExp_const {n : ℕ} {p : ℝ} (c : ℝ) : sgExp n p (fun _ _ => c) = c := by
  rw [sgExp]
  simp_rw [← Finset.sum_mul]
  rw [sum_sgWeight, one_mul]

/-- Averaging a product of functions of independent uniform signs:
`∑_J ∏_{e ∈ S} f_e(J_e) = 2^{|α| - |S|} ∏_{e ∈ S} (f_e(true) + f_e(false))`. -/
theorem sum_bool_prod {α R : Type*} [Fintype α] [CommSemiring R] (S : Finset α)
    (f : α → Bool → R) :
    ∑ J : α → Bool, ∏ e ∈ S, f e (J e) =
      2 ^ (Fintype.card α - S.card) * ∏ e ∈ S, (f e true + f e false) := by
  set g : α → Bool → R := fun e b => if e ∈ S then f e b else 1 with hg
  have h1 : ∀ J : α → Bool, ∏ e ∈ S, f e (J e) = ∏ e, g e (J e) := by
    intro J
    rw [← Finset.prod_subset (Finset.subset_univ S)]
    · exact Finset.prod_congr rfl fun e he => by simp [hg, he]
    · intro e _ he
      simp [hg, he]
  simp_rw [h1]
  rw [← Fintype.prod_sum g]
  have h2 : ∀ e, ∑ b : Bool, g e b = if e ∈ S then f e true + f e false else 2 := by
    intro e
    by_cases he : e ∈ S <;> simp [hg, he, one_add_one_eq_two]
  simp_rw [h2]
  rw [Finset.prod_ite, Finset.prod_const, Finset.filter_mem_eq_inter, Finset.univ_inter,
    mul_comm]
  congr 2
  rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.compl_eq_univ_sdiff,
    Finset.card_compl]

end

end ERZeroFreeness
