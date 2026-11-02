/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs

/-!
# Basic facts about the Erdős–Rényi weights

`SimpleGraph (Fin n)` is in bijection with the subsets of the edge set of the complete graph
`(⊤ : SimpleGraph (Fin n)).edgeFinset` (which has `n.choose 2` elements); under this bijection
`erWeight n p` is the product Bernoulli(`p`) law.  The key identity is
`sum_erWeight_mul_prod` (independence of edges), proved from `Finset.prod_add`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

variable {n : ℕ} {p : ℝ}

/-- Reindexing a sum over all graphs on `Fin n` as a sum over the subsets of the edge set of
the complete graph, through the bijection `G ↦ G.edgeFinset`, `S ↦ fromEdgeSet S`. -/
private lemma erdosRenyi_sum_graph_eq_sum_powerset {M : Type*} [AddCommMonoid M]
    (F : Finset (Sym2 (Fin n)) → M) :
    ∑ G : SimpleGraph (Fin n), F G.edgeFinset =
      ∑ t ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset.powerset, F t := by
  refine Finset.sum_nbij' (fun G => G.edgeFinset)
    (fun t => SimpleGraph.fromEdgeSet (t : Set (Sym2 (Fin n)))) ?_ ?_ ?_ ?_ ?_
  · intro G _
    rw [Finset.mem_powerset]
    exact SimpleGraph.edgeFinset_mono le_top
  · intro t _
    exact Finset.mem_univ _
  · intro G _
    simp
  · intro t ht
    rw [Finset.mem_powerset] at ht
    ext e
    have key : e ∈ (SimpleGraph.fromEdgeSet (t : Set (Sym2 (Fin n)))).edgeSet ↔ e ∈ t := by
      rw [SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, Sym2.mem_diagSet, Finset.mem_coe]
      exact ⟨fun h => h.1, fun he => ⟨he, SimpleGraph.not_isDiag_of_mem_edgeFinset (ht he)⟩⟩
    convert (SimpleGraph.mem_edgeFinset
      (G := SimpleGraph.fromEdgeSet (t : Set (Sym2 (Fin n))))).trans key
  · intro G _
    rfl

private lemma erdosRenyi_card_edgeFinset_top :
    (⊤ : SimpleGraph (Fin n)).edgeFinset.card = n.choose 2 := by
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]

private lemma erdosRenyi_edgeFinset_subset_top (G : SimpleGraph (Fin n)) :
    G.edgeFinset ⊆ (⊤ : SimpleGraph (Fin n)).edgeFinset :=
  SimpleGraph.edgeFinset_mono le_top

/-- Edges are independent (general form): each edge of `K_n` contributes the factor `a e` if it
is present and `b e` if it is absent. -/
private lemma erdosRenyi_sum_erWeight_mul_prod_ite {R : Type*} [CommRing R] [Algebra ℝ R]
    (a b : Sym2 (Fin n) → R) :
    ∑ G : SimpleGraph (Fin n), algebraMap ℝ R (erWeight n p G) *
        ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, (if e ∈ G.edgeFinset then a e else b e) =
      ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
        (algebraMap ℝ R p * a e + algebraMap ℝ R (1 - p) * b e) := by
  rw [Finset.prod_add, ← erdosRenyi_sum_graph_eq_sum_powerset
    (fun t => (∏ e ∈ t, (algebraMap ℝ R p * a e)) *
      ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset \ t, (algebraMap ℝ R (1 - p) * b e))]
  refine Finset.sum_congr rfl fun G _ => ?_
  have hG := erdosRenyi_edgeFinset_subset_top G
  have hprod : (∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
      (if e ∈ G.edgeFinset then a e else b e)) =
      (∏ e ∈ G.edgeFinset, a e) *
        ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset \ G.edgeFinset, b e := by
    have h := Finset.prod_piecewise (⊤ : SimpleGraph (Fin n)).edgeFinset G.edgeFinset a b
    rw [Finset.inter_eq_right.mpr hG] at h
    rw [← h]
    rfl
  rw [hprod, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_const, Finset.card_sdiff_of_subset hG, erdosRenyi_card_edgeFinset_top]
  simp only [erWeight, map_mul, map_pow]
  ring

theorem erWeight_nonneg (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (G : SimpleGraph (Fin n)) :
    0 ≤ erWeight n p G := by
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)

/-- Edges are independent: the `G(n,p)` average of a product over present edges. -/
theorem sum_erWeight_mul_prod {R : Type*} [CommRing R] [Algebra ℝ R] (y : Sym2 (Fin n) → R) :
    ∑ G : SimpleGraph (Fin n), algebraMap ℝ R (erWeight n p G) * ∏ e ∈ G.edgeFinset, y e =
      ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
        (algebraMap ℝ R (1 - p) + algebraMap ℝ R p * y e) := by
  have h := erdosRenyi_sum_erWeight_mul_prod_ite (n := n) (p := p) y (fun _ => (1 : R))
  have hrhs : (∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
      (algebraMap ℝ R (1 - p) + algebraMap ℝ R p * y e)) =
      ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
        (algebraMap ℝ R p * y e + algebraMap ℝ R (1 - p) * 1) :=
    Finset.prod_congr rfl fun e _ => by ring
  rw [hrhs, ← h]
  refine Finset.sum_congr rfl fun G _ => ?_
  congr 1
  rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr (erdosRenyi_edgeFinset_subset_top G)]

theorem sum_erWeight (n : ℕ) (p : ℝ) : ∑ G : SimpleGraph (Fin n), erWeight n p G = 1 := by
  have h := sum_erWeight_mul_prod (R := ℝ) (n := n) (p := p) (fun _ => 1)
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Finset.prod_const_one, mul_one,
    sub_add_cancel] at h
  exact h

theorem erProb_univ (n : ℕ) (p : ℝ) : erProb n p Set.univ = 1 := by
  simp only [erProb, Set.mem_univ, if_true]
  exact sum_erWeight n p

/-- `Pr[S ⊆ E(G)] = p^{|S|}` for a set `S` of pairs of distinct vertices. -/
theorem erProb_subset_edgeFinset (S : Finset (Sym2 (Fin n)))
    (hS : S ⊆ (⊤ : SimpleGraph (Fin n)).edgeFinset) :
    erProb n p {G | S ⊆ G.edgeFinset} = p ^ S.card := by
  have h := erdosRenyi_sum_erWeight_mul_prod_ite (R := ℝ) (n := n) (p := p) (fun _ => 1)
    (fun e => if e ∈ S then 0 else 1)
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at h
  have hrhs : (∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
      (p * 1 + (1 - p) * (if e ∈ S then (0 : ℝ) else 1))) =
      ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, (if e ∈ S then p else 1) :=
    Finset.prod_congr rfl fun e _ => by split_ifs <;> ring
  rw [hrhs, Finset.prod_ite_mem, Finset.inter_eq_right.mpr hS, Finset.prod_const] at h
  rw [← h, erProb]
  refine Finset.sum_congr rfl fun G _ => ?_
  rw [Set.mem_ofPred_eq]
  split_ifs with hSG
  · rw [Finset.prod_eq_one, mul_one]
    intro e _
    split_ifs with h1 h2
    · rfl
    · exact absurd (hSG h2) h1
    · rfl
  · rw [Finset.not_subset] at hSG
    obtain ⟨e, heS, heG⟩ := hSG
    rw [Finset.prod_eq_zero (hS heS) (by rw [if_neg heG, if_pos heS]), mul_zero]

theorem erProb_nonneg (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Set (SimpleGraph (Fin n))) :
    0 ≤ erProb n p A := by
  refine Finset.sum_nonneg fun G _ => ?_
  split_ifs
  · exact erWeight_nonneg hp0 hp1 G
  · exact le_rfl

theorem erProb_mono (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {A B : Set (SimpleGraph (Fin n))} (h : A ⊆ B) :
    erProb n p A ≤ erProb n p B := by
  refine Finset.sum_le_sum fun G _ => ?_
  by_cases hA : G ∈ A
  · rw [if_pos hA, if_pos (h hA)]
  · rw [if_neg hA]
    split_ifs
    · exact erWeight_nonneg hp0 hp1 G
    · exact le_rfl

theorem erProb_union_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A B : Set (SimpleGraph (Fin n))) :
    erProb n p (A ∪ B) ≤ erProb n p A + erProb n p B := by
  rw [erProb, erProb, erProb, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun G _ => ?_
  have hw := erWeight_nonneg hp0 hp1 G
  by_cases hA : G ∈ A
  · rw [if_pos (Set.mem_union_left B hA), if_pos hA]
    split_ifs <;> linarith
  · by_cases hB : G ∈ B
    · rw [if_pos (Set.mem_union_right A hB), if_pos hB, if_neg hA, zero_add]
    · rw [if_neg (fun h => h.elim hA hB), if_neg hA, if_neg hB, add_zero]

theorem erProb_compl (A : Set (SimpleGraph (Fin n))) : erProb n p Aᶜ = 1 - erProb n p A := by
  have h : erProb n p Aᶜ + erProb n p A = 1 := by
    rw [erProb, erProb, ← Finset.sum_add_distrib, ← sum_erWeight n p]
    refine Finset.sum_congr rfl fun G _ => ?_
    by_cases hA : G ∈ A
    · rw [if_neg (Set.notMem_compl_iff.mpr hA), if_pos hA, zero_add]
    · rw [if_pos (Set.mem_compl hA), if_neg hA, add_zero]
  linarith

theorem erProb_le_one (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Set (SimpleGraph (Fin n))) :
    erProb n p A ≤ 1 := by
  rw [← erProb_univ n p]
  exact erProb_mono hp0 hp1 (Set.subset_univ A)

theorem erExp_mono (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f g : SimpleGraph (Fin n) → ℝ}
    (h : ∀ G, f G ≤ g G) : erExp n p f ≤ erExp n p g := by
  exact Finset.sum_le_sum fun G _ => mul_le_mul_of_nonneg_left (h G) (erWeight_nonneg hp0 hp1 G)

theorem erExp_add (f g : SimpleGraph (Fin n) → ℝ) :
    erExp n p (fun G => f G + g G) = erExp n p f + erExp n p g := by
  simp only [erExp, mul_add, Finset.sum_add_distrib]

theorem erExp_const_mul (c : ℝ) (f : SimpleGraph (Fin n) → ℝ) :
    erExp n p (fun G => c * f G) = c * erExp n p f := by
  simp only [erExp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun G _ => by ring

theorem erExp_const (c : ℝ) : erExp n p (fun _ => c) = c := by
  rw [erExp, ← Finset.sum_mul, sum_erWeight, one_mul]

/-- Markov's inequality. -/
theorem erProb_le_erExp_div (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f : SimpleGraph (Fin n) → ℝ}
    (hf : ∀ G, 0 ≤ f G) {a : ℝ} (ha : 0 < a) :
    erProb n p {G | a ≤ f G} ≤ erExp n p f / a := by
  rw [erExp, erProb, Finset.sum_div]
  refine Finset.sum_le_sum fun G _ => ?_
  have hw := erWeight_nonneg hp0 hp1 G
  split_ifs with hG
  · rw [Set.mem_ofPred_eq] at hG
    rw [le_div_iff₀ ha]
    exact mul_le_mul_of_nonneg_left hG hw
  · exact div_nonneg (mul_nonneg hw (hf G)) ha.le

/-- For `0 ≤ d ≤ n`, the edge probability `d/n` of `G(n, d/n)` lies in `[0, 1]`.  The finitely
many `n < d`, for which `d/n` can exceed `1`, do not affect the limit statements. -/
theorem div_natCast_mem_Icc {d : ℝ} (hd : 0 ≤ d) {n : ℕ} (hn : d ≤ n) :
    0 ≤ d / n ∧ d / n ≤ 1 := by
  exact ⟨div_nonneg hd (Nat.cast_nonneg n), div_le_one_of_le₀ hn (Nat.cast_nonneg n)⟩

end

end ERZeroFreeness
