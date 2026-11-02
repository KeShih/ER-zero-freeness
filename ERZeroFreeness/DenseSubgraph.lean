/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs
import ERZeroFreeness.ErdosRenyi

/-!
# Small dense subgraphs are rare (`lem:jets`, probabilistic part)

The event `HasDenseSubgraph G b` (some `S ⊆ E(G)` with `|S| ≤ b` touching fewer than `|S|`
vertices) has probability `O(1/n)` in `G(n,p)`, `p = d/n`.  The paper counts copies of each
isomorphism type of connected graph; here the union bound runs directly over the edge sets of
the complete graph, grouped by the vertices they touch.

*Union bound* (`denseSubgraph_erProb_le`): `HasDenseSubgraph G b` holds iff `S ⊆ E(G)` for
some `S` in the finite family `T` of edge sets of the complete graph with `|S| ≤ b` and
`|edgeVerts S| < |S|`, and `Pr[S ⊆ E(G)] = p^{|S|}` (`erProb_subset_edgeFinset`), so the
probability is at most `∑_{S ∈ T} p^{|S|}`.

*Counting* (`denseSubgraph_sum_pow_card_le`): for `S ∈ T` we have `p^{|S|} ≤ p^{|W|+1}` with
`W = edgeVerts S`, since `|S| ≥ |W| + 1` and `0 ≤ p ≤ 1`.  Group the `S` by `W`: every `S`
with `edgeVerts S = W` is a subset of `W.sym2`, and such an `S` exists only if `|W| < b`, so
each fibre has at most `2^{binom(|W|+1, 2)} ≤ 2^{b²}` elements.  Hence
`∑_{S ∈ T} p^{|S|} ≤ 2^{b²} ∑_{W ⊆ [n]} p^{|W|+1} = 2^{b²} p (1+p)^n`.

*Limit*: for `n ≥ d` this is `≤ 2^{b²} (d/n) (1 + d/n)^n ≤ 2^{b²} e^d d / n → 0`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- The union bound for a finite family of events. -/
private lemma denseSubgraph_erProb_biUnion_le {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ι : Type*} (T : Finset ι) (A : ι → Set (SimpleGraph (Fin n))) :
    erProb n p (⋃ i ∈ T, A i) ≤ ∑ i ∈ T, erProb n p (A i) := by
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    refine (Finset.sum_eq_zero fun G _ => if_neg ?_).le
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.mem_empty_iff_false,
      not_false_eq_true]
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (erProb_union_le hp0 hp1 _ _).trans (add_le_add le_rfl ih)

/-- An edge set consists of pairs of the vertices it touches: `S ⊆ (edgeVerts S).sym2`. -/
private lemma denseSubgraph_subset_sym2_edgeVerts {n : ℕ} (S : Finset (Sym2 (Fin n))) :
    S ⊆ (edgeVerts S).sym2 := by
  intro e he
  rw [Finset.mem_sym2_iff]
  intro a ha
  simp only [edgeVerts, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨e, he, ha⟩

/-- Counting: edge sets `S` with `|S| ≤ b` touching fewer than `|S|` vertices have total weight
`∑_S p^{|S|} ≤ 2^{b²} p (1+p)^n`. -/
private lemma denseSubgraph_sum_pow_card_le {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : ℕ)
    (T : Finset (Finset (Sym2 (Fin n))))
    (hT : ∀ S ∈ T, S.card ≤ b ∧ (edgeVerts S).card < S.card) :
    ∑ S ∈ T, p ^ S.card ≤ 2 ^ (b * b) * p * (1 + p) ^ n := by
  calc ∑ S ∈ T, p ^ S.card ≤ ∑ S ∈ T, p ^ ((edgeVerts S).card + 1) :=
        Finset.sum_le_sum fun S hS => pow_le_pow_of_le_one hp0 hp1 (hT S hS).2
    _ = ∑ W : Finset (Fin n), ∑ S ∈ T with edgeVerts S = W, p ^ (W.card + 1) :=
        (Finset.sum_fiberwise' T edgeVerts (fun W => p ^ (W.card + 1))).symm
    _ ≤ ∑ W : Finset (Fin n), (2 : ℝ) ^ (b * b) * p ^ (W.card + 1) := by
        refine Finset.sum_le_sum fun W _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hp0 _)
        have hcard : (T.filter fun S => edgeVerts S = W).card ≤ 2 ^ (b * b) := by
          by_cases hW : W.card < b
          · calc (T.filter fun S => edgeVerts S = W).card ≤ W.sym2.powerset.card := by
                  refine Finset.card_le_card fun S hS => ?_
                  rw [Finset.mem_filter] at hS
                  rw [Finset.mem_powerset, ← hS.2]
                  exact denseSubgraph_subset_sym2_edgeVerts S
              _ = 2 ^ ((W.card + 1).choose 2) := by
                  rw [Finset.card_powerset, Finset.card_sym2]
              _ ≤ 2 ^ (b * b) := by
                  refine Nat.pow_le_pow_right (by norm_num) ?_
                  calc (W.card + 1).choose 2 ≤ (W.card + 1) ^ 2 := Nat.choose_le_pow _ _
                    _ ≤ b ^ 2 := Nat.pow_le_pow_left hW _
                    _ = b * b := sq b
          · -- no `S ∈ T` touches `|W| ≥ b` vertices, so the fibre is empty
            have hempty : (T.filter fun S => edgeVerts S = W) = ∅ := by
              rw [Finset.filter_eq_empty_iff]
              intro S hS hSW
              have hS' := hT S hS
              rw [hSW] at hS'
              omega
            rw [hempty, Finset.card_empty]
            exact Nat.zero_le _
        exact_mod_cast hcard
    _ = 2 ^ (b * b) * p * ∑ W : Finset (Fin n), p ^ W.card := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun W _ => ?_
        ring
    _ = 2 ^ (b * b) * p * (1 + p) ^ n := by
        congr 1
        have h := Fintype.sum_pow_mul_eq_add_pow (Fin n) p 1
        simp only [one_pow, mul_one, Fintype.card_fin] at h
        rw [h, add_comm]

/-- Union bound plus counting: `Pr[HasDenseSubgraph G b] ≤ 2^{b²} p (1+p)^n` in `G(n,p)`. -/
private lemma denseSubgraph_erProb_le {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : ℕ) :
    erProb n p {G | HasDenseSubgraph G b} ≤ 2 ^ (b * b) * p * (1 + p) ^ n := by
  set T : Finset (Finset (Sym2 (Fin n))) :=
    (⊤ : SimpleGraph (Fin n)).edgeFinset.powerset.filter
      (fun S => S.card ≤ b ∧ (edgeVerts S).card < S.card) with hTdef
  have hsub : {G : SimpleGraph (Fin n) | HasDenseSubgraph G b} ⊆
      ⋃ S ∈ T, {G | S ⊆ G.edgeFinset} := by
    rintro G ⟨S, hSG, hSb, hSv⟩
    simp only [Set.mem_iUnion]
    refine ⟨S, ?_, hSG⟩
    rw [hTdef, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hSG.trans (SimpleGraph.edgeFinset_mono le_top), hSb, hSv⟩
  calc erProb n p {G | HasDenseSubgraph G b}
      ≤ erProb n p (⋃ S ∈ T, {G | S ⊆ G.edgeFinset}) := erProb_mono hp0 hp1 hsub
    _ ≤ ∑ S ∈ T, erProb n p {G | S ⊆ G.edgeFinset} :=
        denseSubgraph_erProb_biUnion_le hp0 hp1 T _
    _ = ∑ S ∈ T, p ^ S.card := by
        refine Finset.sum_congr rfl fun S hS => ?_
        rw [hTdef, Finset.mem_filter, Finset.mem_powerset] at hS
        exact erProb_subset_edgeFinset S hS.1
    _ ≤ 2 ^ (b * b) * p * (1 + p) ^ n := by
        refine denseSubgraph_sum_pow_card_le hp0 hp1 b T fun S hS => ?_
        rw [hTdef, Finset.mem_filter] at hS
        exact hS.2

/-- In `G(n, d/n)`, the probability that some set of at most `b` edges touches fewer vertices
than it has edges tends to `0`; for `n ≥ d` it is at most `2^{b²} e^d d/n`. -/
theorem tendsto_erProb_hasDenseSubgraph {d : ℝ} (hd : 0 < d) (b : ℕ) :
    Tendsto (fun n : ℕ => erProb n (d / n) {G | HasDenseSubgraph G b}) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => (2 : ℝ) ^ (b * b) * (d / n) * Real.exp d) atTop (𝓝 0) := by
    have h := ((tendsto_const_div_atTop_nhds_zero_nat d).const_mul ((2 : ℝ) ^ (b * b))).mul_const
      (Real.exp d)
    rwa [mul_zero, zero_mul] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_ge_atTop ⌈d⌉₊] with n hn
    have hdn : d ≤ n := (Nat.le_ceil d).trans (by exact_mod_cast hn)
    obtain ⟨h0, h1⟩ := div_natCast_mem_Icc hd.le hdn
    exact erProb_nonneg h0 h1 _
  · filter_upwards [eventually_ge_atTop ⌈d⌉₊] with n hn
    have hdn : d ≤ n := (Nat.le_ceil d).trans (by exact_mod_cast hn)
    obtain ⟨h0, h1⟩ := div_natCast_mem_Icc hd.le hdn
    have hn0 : (n : ℝ) ≠ 0 := (lt_of_lt_of_le hd hdn).ne'
    refine (denseSubgraph_erProb_le h0 h1 b).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    -- `(1 + d/n)^n ≤ (e^{d/n})^n = e^d`
    calc (1 + d / n) ^ n ≤ Real.exp (d / n) ^ n := by
          refine pow_le_pow_left₀ (by positivity) ?_ n
          linarith [Real.add_one_le_exp (d / n)]
      _ = Real.exp d := by
          rw [← Real.exp_nat_mul, mul_div_cancel₀ d hn0]

end

end ERZeroFreeness
