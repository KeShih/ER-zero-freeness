/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.VBModel
import ERZeroFreeness.CycleMoments

/-!
# Factorial moments of the signed short-cycle counts

Combinatorics of the signed cycle counts `C^±_ℓ(G,J)` for Step 3 of Section 7 (Theorem 1.5(ii)):

* `card_sign_pattern`: the parities of disjoint nonempty blocks of independent uniform signs are
  independent and uniform (Fourier expansion of the indicator);
* `prod_sgDescFactorial_eq`: the product of falling factorials
  `∏_i (C^+_{i+3})_{a_i} (C^-_{i+3})_{b_i}` counts the families of distinct cycles of `G` with
  `a_i` positive and `b_i` negative cycles of length `i + 3`;
* `sgExp_prod_sgDescFactorial`: its expectation in the signed Erdős–Rényi model, with the edges
  handled by `erProb_subset_edgeFinset` and the signs by counting.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-! ### Independent parities of disjoint blocks (Fourier expansion) -/

/-- A product of signs is `±1`. -/
private lemma VBSignCount_prod_boolSign {α : Type*} (S : Finset α) (J : α → Bool) :
    ∏ e ∈ S, boolSign (J e) = 1 ∨ ∏ e ∈ S, boolSign (J e) = -1 := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha]
    cases J a <;> rcases ih with h | h <;> rw [h] <;> simp [boolSign]

/-- `2 · [s = ε] = 1 + ε s` for `s = ±1`. -/
private lemma VBSignCount_indicator (s : ℤ) (hs : s = 1 ∨ s = -1) (b : Bool) :
    (if s = boolSign b then (2 : ℤ) else 0) = 1 + boolSign b * s := by
  cases b <;> rcases hs with rfl | rfl <;> simp [boolSign]

/-- `∑_J ∏_{e ∈ U} J_e` is `2^{|α|}` if `U = ∅` and `0` otherwise. -/
private lemma VBSignCount_sum_prod_boolSign {α : Type*} [Fintype α] (U : Finset α) :
    ∑ J : α → Bool, ∏ e ∈ U, boolSign (J e) = if U = ∅ then 2 ^ Fintype.card α else 0 := by
  rw [sum_bool_prod U (fun _ b => boolSign b)]
  split_ifs with hU
  · subst hU
    simp
  · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.2 hU
    rw [Finset.prod_eq_zero he (by simp [boolSign]), mul_zero]

/-- Disjoint nonempty blocks have independent uniform parities: for every sign pattern `ε`, the
number of `J` with `∏_{e ∈ E_i} J_e = ε_i` for all `i` is `2^{|α|} / 2^{|ι|}`. -/
theorem card_sign_pattern {α ι : Type*} [Fintype α] [Fintype ι] (E : ι → Finset α)
    (hE : ∀ i, (E i).Nonempty) (hdisj : Pairwise fun i j => Disjoint (E i) (E j))
    (ε : ι → Bool) :
    (Finset.univ.filter fun J : α → Bool =>
        ∀ i, ∏ e ∈ E i, boolSign (J e) = boolSign (ε i)).card * 2 ^ Fintype.card ι =
      2 ^ Fintype.card α := by
  have key : ((Finset.univ.filter fun J : α → Bool =>
        ∀ i, ∏ e ∈ E i, boolSign (J e) = boolSign (ε i)).card : ℤ) * 2 ^ Fintype.card ι =
      2 ^ Fintype.card α := by
    rw [Finset.natCast_card_filter, Finset.sum_mul]
    have h1 : ∀ J : α → Bool,
        (if ∀ i, ∏ e ∈ E i, boolSign (J e) = boolSign (ε i) then (1 : ℤ) else 0) *
          2 ^ Fintype.card ι =
        ∑ T ∈ (Finset.univ : Finset ι).powerset,
          (∏ i ∈ T, boolSign (ε i)) * ∏ e ∈ T.biUnion E, boolSign (J e) := by
      intro J
      have h2 : ∏ i, (1 + boolSign (ε i) * ∏ e ∈ E i, boolSign (J e)) =
          ∏ i, (if ∏ e ∈ E i, boolSign (J e) = boolSign (ε i) then (2 : ℤ) else 0) :=
        Finset.prod_congr rfl fun i _ =>
          (VBSignCount_indicator _ (VBSignCount_prod_boolSign (E i) J) (ε i)).symm
      rw [Fintype.prod_ite_zero, Finset.prod_one_add] at h2
      rw [ite_mul, one_mul, zero_mul]
      have h3 : (∏ _i : ι, (2 : ℤ)) = 2 ^ Fintype.card ι := by simp
      rw [← h3, ← h2]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [Finset.prod_mul_distrib, Finset.prod_biUnion]
      intro i _ j _ hij
      exact hdisj hij
    simp_rw [h1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, VBSignCount_sum_prod_boolSign]
    rw [Finset.sum_eq_single ∅]
    · simp
    · intro T _ hT
      rw [if_neg, mul_zero]
      intro hU
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hT
      obtain ⟨e, he⟩ := hE i
      have : e ∈ T.biUnion E := Finset.mem_biUnion.2 ⟨i, hi, he⟩
      rw [hU] at this
      simp at this
    · intro h
      simp at h
  exact_mod_cast key

/-! ### Signed factorial moments count families of signed cycles -/

/-- Injective `h : Fin (a + b) → α` with `h x ∈ S true` for `x < a` and `h x ∈ S false`
otherwise number `(|S true|)_a (|S false|)_b` when `S true` and `S false` are disjoint
(`h ↦ (h ∘ castAdd, h ∘ natAdd)`, inverse `Fin.append`). -/
private lemma VBSignCount_card_append {α : Type*} [Fintype α] (S : Bool → Finset α)
    (hS : Disjoint (S true) (S false)) (a b : ℕ) :
    (Finset.univ.filter fun h : Fin (a + b) → α =>
        Function.Injective h ∧ ∀ x : Fin (a + b), h x ∈ S (decide (x.1 < a))).card =
      (S true).card.descFactorial a * (S false).card.descFactorial b := by
  rw [← CycMom.card_filter_injective (S true) a, ← CycMom.card_filter_injective (S false) b,
    ← Finset.card_product]
  refine Finset.card_nbij' (fun h => (fun x => h (Fin.castAdd b x), fun x => h (Fin.natAdd a x)))
    (fun fg => Fin.append fg.1 fg.2) ?_ ?_ ?_ ?_
  · intro h hh
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hh
    simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod,
      Set.mem_ofPred_eq]
    refine ⟨⟨hh.1.comp (Fin.castAdd_injective a b), fun x => ?_⟩,
      ⟨hh.1.comp (Fin.natAdd_injective b a), fun x => ?_⟩⟩
    · have := hh.2 (Fin.castAdd b x)
      simpa [x.2] using this
    · have := hh.2 (Fin.natAdd a x)
      simpa using this
  · rintro ⟨f, g⟩ hfg
    simp only [Finset.coe_product, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_prod,
      Set.mem_ofPred_eq] at hfg
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    obtain ⟨⟨hf, hfS⟩, ⟨hg, hgS⟩⟩ := hfg
    refine ⟨?_, fun x => ?_⟩
    · intro x y hxy
      induction x using Fin.addCases with
      | left i =>
        induction y using Fin.addCases with
        | left j =>
          rw [Fin.append_left, Fin.append_left] at hxy
          rw [hf hxy]
        | right j =>
          rw [Fin.append_left, Fin.append_right] at hxy
          have h1 := Finset.disjoint_left.1 hS (hfS i)
          rw [hxy] at h1
          exact absurd (hgS j) h1
      | right i =>
        induction y using Fin.addCases with
        | left j =>
          rw [Fin.append_right, Fin.append_left] at hxy
          have h1 := Finset.disjoint_left.1 hS (hfS j)
          rw [← hxy] at h1
          exact absurd (hgS i) h1
        | right j =>
          rw [Fin.append_right, Fin.append_right] at hxy
          rw [hg hxy]
    · induction x using Fin.addCases with
      | left i =>
        rw [Fin.append_left]
        simpa [i.2] using hfS i
      | right i =>
        rw [Fin.append_right]
        simpa using hgS i
  · intro h _
    exact Fin.append_castAdd_natAdd
  · rintro ⟨f, g⟩ _
    simp only [Fin.append_left, Fin.append_right]

/-- The `(j+3)`-cycles of `G` with sign `boolSign s`. -/
private def VBSignCount_S {V : Type*} [Fintype V] (G : SimpleGraph V) (J : Sym2 V → Bool)
    (j : ℕ) (s : Bool) : Finset (Cyc V j) :=
  Finset.univ.filter fun γ : Cyc V j => γ.edges ⊆ G.edgeFinset ∧ cycSign J γ = boolSign s

private lemma VBSignCount_S_disjoint {V : Type*} [Fintype V] (G : SimpleGraph V)
    (J : Sym2 V → Bool) (j : ℕ) :
    Disjoint (VBSignCount_S G J j true) (VBSignCount_S G J j false) := by
  rw [Finset.disjoint_left]
  intro γ h1 h2
  simp only [VBSignCount_S, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  have := h1.2.symm.trans h2.2
  simp [boolSign] at this

/-- Signed factorial moments count families of cycles with prescribed signs:
`∏_i (C^+_{i+3})_{a_i} (C^-_{i+3})_{b_i}` is the number of families `Φ` of cycles of `G` with
each `Φ i` injective, whose first `a i` cycles of length `i + 3` are positive and whose remaining
`b i` cycles are negative. -/
theorem prod_sgDescFactorial_eq {V : Type*} [Fintype V] (G : SimpleGraph V)
    (J : Sym2 V → Bool) (r : ℕ) (a b : Fin r → ℕ) :
    (∏ i : Fin r, ((sgCycleCount G J i true).descFactorial (a i) : ℝ) *
        ((sgCycleCount G J i false).descFactorial (b i) : ℝ)) =
      ∑ Φ : (i : Fin r) → Fin (a i + b i) → Cyc V i,
        if (∀ i, Function.Injective (Φ i)) ∧ CycMom.UΦ Φ ⊆ G.edgeFinset ∧
            ∀ i x, cycSign J (Φ i x) = boolSign (decide (x.1 < a i))
        then 1 else 0 := by
  rw [Finset.sum_boole]
  have hT : ∀ i : Fin r, (sgCycleCount G J i true).descFactorial (a i) *
      (sgCycleCount G J i false).descFactorial (b i) =
      (Finset.univ.filter fun h : Fin (a i + b i) → Cyc V i => Function.Injective h ∧
        ∀ x : Fin (a i + b i), h x ∈ VBSignCount_S G J i (decide (x.1 < a i))).card := by
    intro i
    rw [VBSignCount_card_append _ (VBSignCount_S_disjoint G J i)]
    rfl
  simp_rw [← Nat.cast_mul, hT]
  rw [← Nat.cast_prod, ← Fintype.card_piFinset]
  congr 2
  ext Φ
  simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    CycMom.UΦ_subset_iff, VBSignCount_S]
  constructor
  · intro h
    exact ⟨fun i => (h i).1, fun i x => ((h i).2 x).1, fun i x => ((h i).2 x).2⟩
  · rintro ⟨h1, h2, h3⟩ i
    exact ⟨h1 i, fun x => ⟨h2 i x, h3 i x⟩⟩

/-! ### The expectation -/

/-- `∑_G erWeight(G) [U ⊆ E(G)] = p^{|U|}` for the edge set `U` of a family of cycles. -/
private lemma VBSignCount_sum_erWeight_UΦ (n : ℕ) (p : ℝ) {r : ℕ} {k : Fin r → ℕ}
    (Φ : (i : Fin r) → Fin (k i) → Cyc (Fin n) i) :
    ∑ G : SimpleGraph (Fin n),
        erWeight n p G * (if CycMom.UΦ Φ ⊆ G.edgeFinset then (1 : ℝ) else 0) =
      p ^ (CycMom.UΦ Φ).card := by
  rw [← erProb_subset_edgeFinset (CycMom.UΦ Φ) (fun e he => by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top]
    exact CycMom.not_isDiag_of_mem_UΦ Φ he)]
  unfold erProb
  refine Finset.sum_congr rfl fun G _ => ?_
  have hiff : (G ∈ {G : SimpleGraph (Fin n) | CycMom.UΦ Φ ⊆ G.edgeFinset}) ↔
      CycMom.UΦ Φ ⊆ G.edgeFinset := Iff.rfl
  by_cases h : CycMom.UΦ Φ ⊆ G.edgeFinset
  · rw [if_pos (hiff.2 h), if_pos h, mul_one]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h, mul_zero]

/-- The expectation of the signed factorial moments: the sum over injective families `Φ` of
`p^{|U_Φ|}` (the edges, by `erProb_subset_edgeFinset`) times the fraction of sign vectors `J`
that give the cycles of `Φ` their prescribed signs. -/
theorem sgExp_prod_sgDescFactorial (n : ℕ) (p : ℝ) (r : ℕ) (a b : Fin r → ℕ) :
    sgExp n p (fun G J => ∏ i : Fin r, ((sgCycleCount G J i true).descFactorial (a i) : ℝ) *
        ((sgCycleCount G J i false).descFactorial (b i) : ℝ)) =
      ∑ Φ : (i : Fin r) → Fin (a i + b i) → Cyc (Fin n) i,
        if ∀ i, Function.Injective (Φ i) then
          p ^ (CycMom.UΦ Φ).card *
            (((Finset.univ.filter fun J : Sym2 (Fin n) → Bool =>
                ∀ i x, cycSign J (Φ i x) = boolSign (decide (x.1 < a i))).card : ℝ) /
              2 ^ Fintype.card (Sym2 (Fin n)))
        else 0 := by
  unfold sgExp
  simp_rw [prod_sgDescFactorial_eq, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun G _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun Φ _ => ?_
  split_ifs with hΦ
  · rw [Finset.natCast_card_filter, Finset.sum_div, ← VBSignCount_sum_erWeight_UΦ n p Φ,
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun G _ => Finset.sum_congr rfl fun J _ => ?_
    unfold sgWeight
    by_cases h1 : CycMom.UΦ Φ ⊆ G.edgeFinset
    · by_cases h2 : ∀ i x, cycSign J (Φ i x) = boolSign (decide (x.1 < a i))
      · rw [if_pos ⟨hΦ, h1, h2⟩, if_pos h1, if_pos h2]
        ring
      · rw [if_neg (fun h => h2 h.2.2), if_pos h1, if_neg h2]
        ring
    · rw [if_neg (fun h => h1 h.2.1), if_neg h1]
      ring
  · refine Finset.sum_eq_zero fun G _ => Finset.sum_eq_zero fun J _ => ?_
    rw [if_neg (fun h => hΦ h.1), mul_zero]

end

end ERZeroFreeness
