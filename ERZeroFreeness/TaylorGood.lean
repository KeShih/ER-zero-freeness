/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs
import ERZeroFreeness.CycleStructure
import ERZeroFreeness.EdgeExpansion

/-!
# Taylor coefficients from short cycles (`lem:jets`, deterministic part)

Let `q ≥ 2`.  If `G` has no set of at most `2(r+2)` edges touching fewer vertices than it has
edges (`HasDenseSubgraph`), the coefficients of `Ẑ_G` of degree `≤ m = r+2` agree with those
of `∏_{3 ≤ ℓ ≤ m} (1+(q-1)t^ℓ)^{C_ℓ(G)}` (`zhat_coeff_eq_cyclePoly_coeff`).

Proof.  By `zhat_coeff`, the coefficient of degree `k ≤ m` is `∑_{S ⊆ E(G), |S| = k} w(S)`.
If `w(S) ≠ 0` then no touched vertex has degree 1 (`edgeWeight_eq_zero_of_edgeDeg_eq_one`),
so all touched degrees are `≥ 2`; by the handshake lemma `|edgeVerts S| ≤ |S|`, and
non-density (`|S| ≤ m ≤ 2m`) gives `|edgeVerts S| ≥ |S|`, so every touched degree is
exactly `2`.  Then `S` is a union of pairwise vertex-disjoint cycles (`exists_cycle_decomp`),
uniquely (`eq_of_biUnion_edges_eq`), with `w(S) = (q-1)^{#cycles}`
(`edgeWeight_biUnion_cycles`); each cycle has length `≤ k ≤ m`, i.e. index `j < r`.
Conversely, any two distinct cycles of `G` of length `≤ m` are vertex-disjoint (otherwise
their union is dense, `card_edgeVerts_lt_of_not_pairwiseDisjoint`).  Expand
`cyclePoly q r (cycleCounts r G) = ∏_{i<r} ∏_{γ : Cyc V i, γ ⊆ G} (1 + (q-1) X^{i+3})`
as a sum over sets `Γ` of short cycles of `G`; the map `Γ ↦ ⋃_{γ ∈ Γ} γ.edges` matches the
sets `Γ` of total length `k` with the edge sets `S` of size `k` and `w(S) ≠ 0`, term by term.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

section TaylorGoodHelpers

variable {V : Type*} [Fintype V]

/-- The short cycles of `G`: the cycles of length `j + 3` with `j < r` whose edges lie in `G`. -/
private def tgShortCycles (r : ℕ) (G : SimpleGraph V) : Finset (AnyCyc V) :=
  (Finset.range r).sigma fun j => Finset.univ.filter fun γ : Cyc V j => γ.edges ⊆ G.edgeFinset

private theorem tg_mem_shortCycles {r : ℕ} {G : SimpleGraph V} {γ : AnyCyc V} :
    γ ∈ tgShortCycles r G ↔ γ.1 < r ∧ γ.edges ⊆ G.edgeFinset := by
  simp [tgShortCycles, Finset.mem_sigma, AnyCyc.edges]

/-- `Q_{r+2}(X; C(G)) = ∏_{γ short cycle of G} (1 + (q-1) X^{|γ|})`. -/
private theorem tg_cyclePoly_eq_prod (q r : ℕ) (G : SimpleGraph V) :
    cyclePoly q r (cycleCounts r G) =
      ∏ γ ∈ tgShortCycles r G, (1 + C ((q : ℂ) - 1) * X ^ (γ.1 + 3)) := by
  rw [tgShortCycles, Finset.prod_sigma, cyclePoly]
  simp only [Finset.prod_const]
  rw [← Fin.prod_univ_eq_prod_range]
  rfl

private theorem tg_mem_verts_of_mem {γ : AnyCyc V} {e : Sym2 V} {v : V} (he : e ∈ γ.edges)
    (hv : v ∈ e) : v ∈ γ.verts := by
  simp only [AnyCyc.verts, edgeVerts, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨e, he, hv⟩

/-- Vertex-disjoint cycles are edge-disjoint. -/
private theorem tg_edges_disjoint {γ₁ γ₂ : AnyCyc V} (h : Disjoint γ₁.verts γ₂.verts) :
    Disjoint γ₁.edges γ₂.edges := by
  rw [Finset.disjoint_left]
  intro e h₁ h₂
  obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨_, Sym2.out_fst_mem e⟩
  exact Finset.disjoint_left.1 h (tg_mem_verts_of_mem h₁ hv) (tg_mem_verts_of_mem h₂ hv)

/-- The number of edges of a union of pairwise vertex-disjoint cycles is the total length. -/
private theorem tg_card_biUnion {Γ : Finset (AnyCyc V)}
    (hΓ : (Γ : Set (AnyCyc V)).PairwiseDisjoint AnyCyc.verts) :
    (Γ.biUnion AnyCyc.edges).card = ∑ γ ∈ Γ, (γ.1 + 3) := by
  rw [Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun γ _ => γ.card_edges
  · intro γ₁ h₁ γ₂ h₂ hne
    exact tg_edges_disjoint (hΓ h₁ h₂ hne)

/-- Without dense subgraphs, distinct short cycles of `G` are vertex-disjoint. -/
private theorem tg_pairwiseDisjoint {r : ℕ} {G : SimpleGraph V}
    (hG : ¬ HasDenseSubgraph G (2 * (r + 2))) :
    ((tgShortCycles r G : Finset (AnyCyc V)) : Set (AnyCyc V)).PairwiseDisjoint
      AnyCyc.verts := by
  intro γ₁ h₁ γ₂ h₂ hne
  by_contra hnd
  apply hG
  have h₁' := tg_mem_shortCycles.1 (Finset.mem_coe.1 h₁)
  have h₂' := tg_mem_shortCycles.1 (Finset.mem_coe.1 h₂)
  refine ⟨({γ₁, γ₂} : Finset (AnyCyc V)).biUnion AnyCyc.edges, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨γ, hγ, heγ⟩ := Finset.mem_biUnion.1 he
    rw [Finset.mem_insert, Finset.mem_singleton] at hγ
    rcases hγ with hγ | hγ
    · exact h₁'.2 (hγ ▸ heγ)
    · exact h₂'.2 (hγ ▸ heγ)
  · calc _ ≤ ∑ γ ∈ ({γ₁, γ₂} : Finset (AnyCyc V)), γ.edges.card := Finset.card_biUnion_le
      _ = γ₁.edges.card + γ₂.edges.card := Finset.sum_pair hne
      _ ≤ 2 * (r + 2) := by rw [γ₁.card_edges, γ₂.card_edges]; omega
  · apply card_edgeVerts_lt_of_not_pairwiseDisjoint
    intro hpd
    exact hnd (hpd (by simp) (by simp) hne)

/-- Without dense subgraphs, an edge set of `G` with at most `r + 2` edges and nonzero weight
is a union of short cycles of `G`. -/
private theorem tg_exists_decomp {q r : ℕ} {G : SimpleGraph V}
    (hG : ¬ HasDenseSubgraph G (2 * (r + 2))) {S : Finset (Sym2 V)} (hS : S ⊆ G.edgeFinset)
    (hcard : S.card ≤ r + 2) (hw : edgeWeight q S ≠ 0) :
    ∃ Γ ⊆ tgShortCycles r G, Γ.biUnion AnyCyc.edges = S := by
  have hdiag : ∀ e ∈ S, ¬ e.IsDiag := fun e he =>
    G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.1 (hS he))
  have hne1 : ∀ v, edgeDeg S v ≠ 1 := fun v hv =>
    hw (edgeWeight_eq_zero_of_edgeDeg_eq_one hdiag hv)
  have hge : ∀ v ∈ edgeVerts S, 2 ≤ edgeDeg S v := by
    intro v hv
    have hpos : 0 < edgeDeg S v := by
      simp only [edgeVerts, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      obtain ⟨e, he, hve⟩ := hv
      exact Finset.card_pos.2 ⟨e, Finset.mem_filter.2 ⟨he, hve⟩⟩
    have := hne1 v
    omega
  have hzero : ∀ v ∉ edgeVerts S, edgeDeg S v = 0 := by
    intro v hv
    rw [edgeDeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he hve
    exact hv (by
      simp only [edgeVerts, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨e, he, hve⟩)
  have hsum : ∑ v ∈ edgeVerts S, edgeDeg S v = 2 * S.card := by
    rw [← sum_edgeDeg S hdiag]
    exact Finset.sum_subset (Finset.subset_univ _) fun v _ hv => hzero v hv
  have hnd : ¬ (edgeVerts S).card < S.card := fun h => hG ⟨S, hS, by omega, h⟩
  have heq : ∀ v ∈ edgeVerts S, edgeDeg S v = 2 := by
    have hle : ∑ v ∈ edgeVerts S, edgeDeg S v ≤ ∑ v ∈ edgeVerts S, 2 := by
      rw [hsum, Finset.sum_const, smul_eq_mul]
      omega
    have := (Finset.sum_eq_sum_iff_of_le hge).1 (le_antisymm (Finset.sum_le_sum hge) hle)
    exact fun v hv => (this v hv).symm
  obtain ⟨Γ, -, hΓu⟩ := exists_cycle_decomp S hdiag heq
  refine ⟨Γ, ?_, hΓu⟩
  intro γ hγ
  have hsub : γ.edges ⊆ S := hΓu ▸ Finset.subset_biUnion_of_mem _ hγ
  have hc := Finset.card_le_card hsub
  rw [γ.card_edges] at hc
  exact tg_mem_shortCycles.2 ⟨by omega, hsub.trans hS⟩

end TaylorGoodHelpers

/-- **`lem:jets`, deterministic part.**  If no set of at most `2(r+2)` edges of `G` touches
fewer vertices than it has edges, then `Ẑ_G` and `∏_{3 ≤ ℓ ≤ r+2} (1+(q-1)t^ℓ)^{C_ℓ(G)}`
(`cyclePoly q r (cycleCounts r G)`) have the same coefficients in all degrees `≤ r + 2`. -/
theorem zhat_coeff_eq_cyclePoly_coeff {q : ℕ} (hq : 2 ≤ q) (r : ℕ) {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : ¬ HasDenseSubgraph G (2 * (r + 2))) :
    ∀ k ≤ r + 2, (zhat G q).coeff k = (cyclePoly q r (cycleCounts r G)).coeff k := by
  intro k hk
  have hsubpd : ∀ Γ ⊆ tgShortCycles r G,
      (Γ : Set (AnyCyc V)).PairwiseDisjoint AnyCyc.verts :=
    fun Γ hΓ => (tg_pairwiseDisjoint hG).subset (Finset.coe_subset.2 hΓ)
  have hq1 : ((q : ℂ) - 1) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have := Nat.cast_eq_one.1 h
    omega
  have hterm : ∀ Γ : Finset (AnyCyc V), (∏ γ ∈ Γ, C ((q : ℂ) - 1) * X ^ (γ.1 + 3)) =
      C (((q : ℂ) - 1) ^ Γ.card) * X ^ (∑ γ ∈ Γ, (γ.1 + 3)) := by
    intro Γ
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, C_pow]
  -- Expand both sides: edge subsets `S` of size `k` versus sets `Γ` of short cycles of total
  -- length `k`; the map `Γ ↦ ⋃ Γ` matches the nonzero terms.
  rw [zhat_coeff, tg_cyclePoly_eq_prod, Finset.prod_one_add, finsetSum_coeff]
  simp_rw [hterm, coeff_C_mul_X_pow]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij_ne_zero (fun Γ _ _ => Γ.biUnion AnyCyc.edges)
  · intro Γ hΓ _
    rw [Finset.mem_filter, Finset.mem_powerset] at hΓ
    rw [Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro e he
      obtain ⟨γ, hγ, he⟩ := Finset.mem_biUnion.1 he
      exact (tg_mem_shortCycles.1 (hΓ.1 hγ)).2 he
    · rw [tg_card_biUnion (hsubpd Γ hΓ.1)]
      exact hΓ.2.symm
  · intro Γ₁ h₁ _ Γ₂ h₂ _ h
    rw [Finset.mem_filter, Finset.mem_powerset] at h₁ h₂
    exact eq_of_biUnion_edges_eq (hsubpd _ h₁.1) (hsubpd _ h₂.1) h
  · intro S hS hw
    rw [Finset.mem_powersetCard] at hS
    obtain ⟨Γ, hΓ, rfl⟩ := tg_exists_decomp hG hS.1 (by omega) hw
    refine ⟨Γ, ?_, pow_ne_zero _ hq1, rfl⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨hΓ, ?_⟩
    rw [← tg_card_biUnion (hsubpd Γ hΓ)]
    exact hS.2.symm
  · intro Γ hΓ _
    rw [Finset.mem_filter, Finset.mem_powerset] at hΓ
    exact (edgeWeight_biUnion_cycles (by omega) Γ (hsubpd Γ hΓ.1)).symm

end

end ERZeroFreeness
