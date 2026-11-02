/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.IsingVBDefs
import ERZeroFreeness.EdgeExpansion
import ERZeroFreeness.CycleStructure

/-! # `VBTaylor`: part of Theorem 1.5 (`thm:ising-applications`), zero-freeness

Proof plans for the statements of this module: `docs/ising-vb/blueprint.md`, section
"Module `VBTaylor`" (and Appendix A for proofs already checked).  Frozen statements carry their
blueprint item numbers in the comments. -/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-! ### Edge-subset expansion (copy of the private `edgeExp_coeff_prod_one_add`) -/

/-- The coefficient of `X^k` in `∏_{i ∈ s} (1 + a_i X)` is the `k`-th elementary symmetric sum
(copy of the private `edgeExp_coeff_prod_one_add` of `EdgeExpansion`). -/
private lemma VBTaylor_coeff_prod_one_add {ι : Type*} (s : Finset ι) (a : ι → ℂ) (k : ℕ) :
    (∏ i ∈ s, (1 + C (a i) * X)).coeff k = ∑ t ∈ s.powersetCard k, ∏ i ∈ t, a i := by
  rw [Finset.prod_one_add, finsetSum_coeff]
  have h : ∀ t ∈ s.powerset, (∏ i ∈ t, C (a i) * X).coeff k =
      if t.card = k then ∏ i ∈ t, a i else 0 := by
    intro t _
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← map_prod, coeff_C_mul_X_pow]
    by_cases h : t.card = k
    · simp [h]
    · simp [h, Ne.symm h]
  rw [Finset.sum_congr rfl h, ← Finset.sum_filter, Finset.powersetCard_eq_filter]

-- [VT1] edge-subset expansion of `P_{H,J}`: the signs factor out of the colour average.
theorem signedPoly_coeff_edgeWeight {V : Type*} [Fintype V] (H : SimpleGraph V) (q : ℕ)
    (J : Sym2 V → ℤ) (k : ℕ) :
    (signedPoly H q J).coeff k =
      ∑ S ∈ H.edgeFinset.powersetCard k, (∏ e ∈ S, (J e : ℂ)) * edgeWeight q S := by
  rw [signedPoly, coeff_C_mul, finsetSum_coeff]
  simp_rw [VBTaylor_coeff_prod_one_add]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [edgeWeight, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

/-! ### Short cycles of `G` (copies of the private `tg_*` helpers of `TaylorGood`) -/

/-- The short cycles of `G`: the cycles of length `j + 3` with `j < r` whose edges lie in `G`. -/
private def VBTaylor_shortCycles {V : Type*} [Fintype V] (r : ℕ) (G : SimpleGraph V) :
    Finset (AnyCyc V) :=
  (Finset.range r).sigma fun j => Finset.univ.filter fun γ : Cyc V j => γ.edges ⊆ G.edgeFinset

private theorem VBTaylor_mem_shortCycles {V : Type*} [Fintype V] {r : ℕ} {G : SimpleGraph V}
    {γ : AnyCyc V} : γ ∈ VBTaylor_shortCycles r G ↔ γ.1 < r ∧ γ.edges ⊆ G.edgeFinset := by
  simp [VBTaylor_shortCycles, Finset.mem_sigma, AnyCyc.edges]

private theorem VBTaylor_mem_verts_of_mem {V : Type*} [Fintype V] {γ : AnyCyc V} {e : Sym2 V}
    {v : V} (he : e ∈ γ.edges) (hv : v ∈ e) : v ∈ γ.verts := by
  simp only [AnyCyc.verts, edgeVerts, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨e, he, hv⟩

/-- Vertex-disjoint cycles are edge-disjoint. -/
private theorem VBTaylor_edges_disjoint {V : Type*} [Fintype V] {γ₁ γ₂ : AnyCyc V}
    (h : Disjoint γ₁.verts γ₂.verts) : Disjoint γ₁.edges γ₂.edges := by
  rw [Finset.disjoint_left]
  intro e h₁ h₂
  obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨_, Sym2.out_fst_mem e⟩
  exact Finset.disjoint_left.1 h (VBTaylor_mem_verts_of_mem h₁ hv)
    (VBTaylor_mem_verts_of_mem h₂ hv)

private theorem VBTaylor_pairwiseDisjoint_edges {V : Type*} [Fintype V] {Γ : Finset (AnyCyc V)}
    (hΓ : (Γ : Set (AnyCyc V)).PairwiseDisjoint AnyCyc.verts) :
    (Γ : Set (AnyCyc V)).PairwiseDisjoint AnyCyc.edges :=
  fun _ h₁ _ h₂ hne => VBTaylor_edges_disjoint (hΓ h₁ h₂ hne)

/-- The number of edges of a union of pairwise vertex-disjoint cycles is the total length. -/
private theorem VBTaylor_card_biUnion {V : Type*} [Fintype V] {Γ : Finset (AnyCyc V)}
    (hΓ : (Γ : Set (AnyCyc V)).PairwiseDisjoint AnyCyc.verts) :
    (Γ.biUnion AnyCyc.edges).card = ∑ γ ∈ Γ, (γ.1 + 3) := by
  rw [Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun γ _ => γ.card_edges
  · intro γ₁ h₁ γ₂ h₂ hne
    exact VBTaylor_edges_disjoint (hΓ h₁ h₂ hne)

/-- Without dense subgraphs, distinct short cycles of `G` are vertex-disjoint. -/
private theorem VBTaylor_pairwiseDisjoint {V : Type*} [Fintype V] {r : ℕ} {G : SimpleGraph V}
    (hG : ¬ HasDenseSubgraph G (2 * (r + 2))) :
    ((VBTaylor_shortCycles r G : Finset (AnyCyc V)) : Set (AnyCyc V)).PairwiseDisjoint
      AnyCyc.verts := by
  intro γ₁ h₁ γ₂ h₂ hne
  by_contra hnd
  apply hG
  have h₁' := VBTaylor_mem_shortCycles.1 (Finset.mem_coe.1 h₁)
  have h₂' := VBTaylor_mem_shortCycles.1 (Finset.mem_coe.1 h₂)
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
private theorem VBTaylor_exists_decomp {V : Type*} [Fintype V] {q r : ℕ} {G : SimpleGraph V}
    (hG : ¬ HasDenseSubgraph G (2 * (r + 2))) {S : Finset (Sym2 V)} (hS : S ⊆ G.edgeFinset)
    (hcard : S.card ≤ r + 2) (hw : edgeWeight q S ≠ 0) :
    ∃ Γ ⊆ VBTaylor_shortCycles r G, Γ.biUnion AnyCyc.edges = S := by
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
  exact VBTaylor_mem_shortCycles.2 ⟨by omega, hsub.trans hS⟩

/-! ### Signs of cycles and the product side -/

private theorem VBTaylor_boolSign_cases (b : Bool) : boolSign b = 1 ∨ boolSign b = -1 := by
  cases b <;> simp [boolSign]

/-- A cycle sign is `±1`. -/
private theorem VBTaylor_cycSign_cases {V : Type*} (J : Sym2 V → Bool) {j : ℕ} (γ : Cyc V j) :
    cycSign J γ = 1 ∨ cycSign J γ = -1 := by
  unfold cycSign
  exact Finset.prod_induction _ (fun x : ℤ => x = 1 ∨ x = -1)
    (fun a b ha hb => by rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp)
    (Or.inl rfl) (fun e _ => VBTaylor_boolSign_cases _)

private theorem VBTaylor_cycSign_ne_zero {V : Type*} (J : Sym2 V → Bool) {j : ℕ}
    (γ : Cyc V j) : ((cycSign J γ : ℤ) : ℂ) ≠ 0 := by
  rcases VBTaylor_cycSign_cases J γ with h | h <;> simp [h]

/-- For one length: `∏_{γ ⊆ G} (1 + J(γ) X^ℓ) = (1 + X^ℓ)^{C^+} (1 - X^ℓ)^{C^-}`. -/
private theorem VBTaylor_prod_split {V : Type*} [Fintype V] (G : SimpleGraph V)
    (J : Sym2 V → Bool) (j : ℕ) :
    ∏ γ ∈ Finset.univ.filter (fun γ : Cyc V j => γ.edges ⊆ G.edgeFinset),
        (1 + C ((cycSign J γ : ℤ) : ℂ) * X ^ (j + 3)) =
      (1 + X ^ (j + 3)) ^ sgCycleCount G J j true *
        (1 - X ^ (j + 3)) ^ sgCycleCount G J j false := by
  rw [← Finset.prod_filter_mul_prod_filter_not _ (fun γ : Cyc V j => cycSign J γ = 1)]
  congr 1
  · rw [Finset.prod_congr rfl (g := fun _ => (1 + X ^ (j + 3) : ℂ[X])), Finset.prod_const]
    · congr 1
      rw [sgCycleCount, Finset.filter_filter]
      rfl
    · intro γ hγ
      rw [Finset.mem_filter] at hγ
      rw [hγ.2]
      simp
  · rw [Finset.prod_congr rfl (g := fun _ => (1 - X ^ (j + 3) : ℂ[X])), Finset.prod_const]
    · congr 1
      rw [sgCycleCount, Finset.filter_filter]
      congr 1
      refine Finset.filter_congr fun γ _ => ?_
      rcases VBTaylor_cycSign_cases J γ with h | h <;> simp [h, boolSign]
    · intro γ hγ
      rw [Finset.mem_filter] at hγ
      have h := (VBTaylor_cycSign_cases J γ).resolve_left hγ.2
      rw [h]
      simp [sub_eq_add_neg]

/-- `Q^{sg}_{r+2}(X; C^±(G,J)) = ∏_{γ short cycle of G} (1 + J(γ) X^{|γ|})`. -/
private theorem VBTaylor_sgCyclePoly_eq_prod {V : Type*} [Fintype V] (r : ℕ)
    (G : SimpleGraph V) (J : Sym2 V → Bool) :
    sgCyclePoly r (sgCycleCounts r G J) =
      ∏ γ ∈ VBTaylor_shortCycles r G, (1 + C ((cycSign J γ.2 : ℤ) : ℂ) * X ^ (γ.1 + 3)) := by
  rw [VBTaylor_shortCycles, Finset.prod_sigma, sgCyclePoly, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [sgCycleCounts, Fin.append_left, Fin.append_right, VBTaylor_prod_split]

-- [VT2] signed `lem:jets` (deterministic part): without dense edge sets of size `≤ 2(r+2)`,
-- `I_{G,J} ≡ ∏_{ℓ ≤ r+2} (1+t^ℓ)^{C^+_ℓ} (1-t^ℓ)^{C^-_ℓ}  (mod t^{r+3})`.
theorem signedPoly_coeff_eq_sgCyclePoly_coeff (r : ℕ) {V : Type*} [Fintype V]
    (G : SimpleGraph V) (J : Sym2 V → Bool) (hG : ¬ HasDenseSubgraph G (2 * (r + 2))) :
    ∀ k ≤ r + 2, (signedPoly G 2 (fun e => boolSign (J e))).coeff k =
      (sgCyclePoly r (sgCycleCounts r G J)).coeff k := by
  intro k hk
  have hsubpd : ∀ Γ ⊆ VBTaylor_shortCycles r G,
      (Γ : Set (AnyCyc V)).PairwiseDisjoint AnyCyc.verts :=
    fun Γ hΓ => (VBTaylor_pairwiseDisjoint hG).subset (Finset.coe_subset.2 hΓ)
  have hterm : ∀ Γ : Finset (AnyCyc V),
      (∏ γ ∈ Γ, C ((cycSign J γ.2 : ℤ) : ℂ) * X ^ (γ.1 + 3)) =
        C (∏ γ ∈ Γ, ((cycSign J γ.2 : ℤ) : ℂ)) * X ^ (∑ γ ∈ Γ, (γ.1 + 3)) := by
    intro Γ
    rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
  -- Expand both sides: edge subsets `S` of size `k` versus sets `Γ` of short cycles of total
  -- length `k`; the map `Γ ↦ ⋃ Γ` matches the nonzero terms.
  rw [signedPoly_coeff_edgeWeight, VBTaylor_sgCyclePoly_eq_prod, Finset.prod_one_add,
    finsetSum_coeff]
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
      exact (VBTaylor_mem_shortCycles.1 (hΓ.1 hγ)).2 he
    · rw [VBTaylor_card_biUnion (hsubpd Γ hΓ.1)]
      exact hΓ.2.symm
  · intro Γ₁ h₁ _ Γ₂ h₂ _ h
    rw [Finset.mem_filter, Finset.mem_powerset] at h₁ h₂
    exact eq_of_biUnion_edges_eq (hsubpd _ h₁.1) (hsubpd _ h₂.1) h
  · intro S hS hw
    rw [Finset.mem_powersetCard] at hS
    obtain ⟨Γ, hΓ, rfl⟩ := VBTaylor_exists_decomp hG hS.1 (by omega) (right_ne_zero_of_mul hw)
    refine ⟨Γ, ?_, ?_, rfl⟩
    · rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨hΓ, ?_⟩
      rw [← VBTaylor_card_biUnion (hsubpd Γ hΓ)]
      exact hS.2.symm
    · exact Finset.prod_ne_zero_iff.2 fun γ _ => VBTaylor_cycSign_ne_zero J γ.2
  · intro Γ hΓ _
    rw [Finset.mem_filter, Finset.mem_powerset] at hΓ
    rw [edgeWeight_biUnion_cycles (by norm_num) Γ (hsubpd Γ hΓ.1),
      Finset.prod_biUnion (VBTaylor_pairwiseDisjoint_edges (hsubpd Γ hΓ.1))]
    have h21 : ((2 : ℕ) : ℂ) - 1 = 1 := by norm_num
    rw [h21, one_pow, mul_one]
    refine Finset.prod_congr rfl fun γ _ => ?_
    rw [cycSign, Int.cast_prod]
    rfl

-- [VT3] the same congruence as an `IsBigO` statement at `t = 0`.
theorem signedPoly_sub_sgCyclePoly_isBigO (r : ℕ) {V : Type*} [Fintype V]
    (G : SimpleGraph V) (J : Sym2 V → Bool) (hG : ¬ HasDenseSubgraph G (2 * (r + 2))) :
    (fun t => (signedPoly G 2 (fun e => boolSign (J e))).eval t -
        (sgCyclePoly r (sgCycleCounts r G J)).eval t) =O[𝓝 0] fun t => t ^ (r + 3) := by
  have hdvd : X ^ (r + 3) ∣
      signedPoly G 2 (fun e => boolSign (J e)) - sgCyclePoly r (sgCycleCounts r G J) := by
    rw [X_pow_dvd_iff]
    intro j hj
    rw [coeff_sub, signedPoly_coeff_eq_sgCyclePoly_coeff r G J hG j (by omega), sub_self]
  obtain ⟨R, hR⟩ := hdvd
  have heq : (fun t => (signedPoly G 2 (fun e => boolSign (J e))).eval t -
      (sgCyclePoly r (sgCycleCounts r G J)).eval t) = fun t => t ^ (r + 3) * R.eval t := by
    funext t
    rw [← eval_sub, hR, eval_mul, eval_pow, eval_X]
  rw [heq]
  have h1 : (fun t : ℂ => R.eval t) =O[𝓝 0] (fun _ => (1 : ℂ)) :=
    (R.continuous.tendsto 0).isBigO_one ℂ
  have h2 := (Asymptotics.isBigO_refl (fun t : ℂ => t ^ (r + 3)) (𝓝 0)).mul h1
  simp only [mul_one] at h2
  exact h2

end

end ERZeroFreeness
