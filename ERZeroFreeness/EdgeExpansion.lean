/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs
import ERZeroFreeness.CycleStructure

/-!
# Edge-subset expansion of `Ẑ_G` (proof of `lem:jets`)

* `zhat_coeff`: the coefficient of `t^k` in `Ẑ_G(t)` is `∑_{S ⊆ E(G), |S| = k} w(S)`, where
  `w(S) = E_σ ∏_{e ∈ S} A_{σe}` (`edgeWeight`); expand `∏_e (1 + A_{σe} X)` over edge subsets
  (`Finset.prod_one_add`).
* `edgeWeight_eq_zero_of_edgeDeg_eq_one`: if a vertex `v` lies on exactly one edge `uv` of a
  loopless edge set `S`, then `w(S) = 0`.  Split off the colour of `v` (`Equiv.funSplitAt`)
  and sum over it first; the columns of `A` sum to zero (`∑_c A_{ci} = (q-1) - (q-1) = 0`).
* `edgeWeight_biUnion_cycles`: a union of `k` pairwise vertex-disjoint cycles has weight
  `(q-1)^k`.  With representatives `c_γ`, reindex the colour sum through the injective map
  `Σ_γ ℤ/ℓ_γ → V`: for injective `c : ι → V`,
  `Σ_{σ : V → [q]} F(σ ∘ c) = q^{|V|-|ι|} Σ_{x : ι → [q]} F x`.  The sum then factorizes
  over the cycles, and for one cycle
  `Σ_{x : ℤ/ℓ → [q]} ∏_i A_{x_i x_{i+1}} = tr(A^ℓ) = q^ℓ (q-1)`, since `A² = qA` and
  `tr A = q(q-1)`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V]

/-! ### Edge-subset expansion -/

/-- The coefficient of `X^k` in `∏_{i ∈ s} (1 + a_i X)` is the `k`-th elementary symmetric sum. -/
private lemma edgeExp_coeff_prod_one_add {ι : Type*} (s : Finset ι) (a : ι → ℂ) (k : ℕ) :
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

theorem zhat_coeff (G : SimpleGraph V) (q : ℕ) (k : ℕ) :
    (zhat G q).coeff k = ∑ S ∈ G.edgeFinset.powersetCard k, edgeWeight q S := by
  rw [zhat, coeff_C_mul, finsetSum_coeff]
  simp_rw [edgeExp_coeff_prod_one_add, edgeWeight, ← Finset.mul_sum]
  rw [Finset.sum_comm]

/-! ### The matrix `A = q·Id − J` -/

/-- The entries of `A = q·Id − J`. -/
private def cycB (q : ℕ) (a b : Fin q) : ℂ := if a = b then (q : ℂ) - 1 else -1

private lemma cycB_eq (q : ℕ) (a b : Fin q) :
    cycB q a b = (if a = b then (q : ℂ) else 0) - 1 := by
  unfold cycB; split_ifs <;> ring

/-- Each column of `A` sums to zero. -/
private lemma cycB_sum_left (q : ℕ) (b : Fin q) : ∑ a : Fin q, cycB q a b = 0 := by
  simp_rw [cycB_eq, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp

/-- `A² = q A`. -/
private lemma cycB_sq (q : ℕ) (a c : Fin q) :
    ∑ b, cycB q a b * cycB q b c = q * cycB q a c := by
  simp only [cycB_eq, sub_mul, mul_sub, Finset.sum_sub_distrib, ite_mul, zero_mul, mul_ite,
    mul_zero, one_mul, mul_one]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- Path sums: `∑_y ∏_{i ≤ n} A_{y_i y_{i+1}} g(y_0, y_{n+1}) = q^n ∑_{a,b} A_{ab} g(a,b)`. -/
private lemma cycB_path (q : ℕ) : ∀ (n : ℕ) (g : Fin q → Fin q → ℂ),
    ∑ y : Fin (n + 2) → Fin q,
      (∏ i : Fin (n + 1), cycB q (y i.castSucc) (y i.succ)) * g (y 0) (y (Fin.last (n + 1))) =
    (q : ℂ) ^ n * ∑ a, ∑ b, cycB q a b * g a b
  | 0, g => by
    rw [← (Fin.consEquiv fun _ => Fin q).sum_comp, Fintype.sum_prod_type]
    simp only [pow_zero, one_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← (Fin.consEquiv fun _ => Fin q).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [Fin.consEquiv_apply]
  | n + 1, g => by
    rw [← (Fin.consEquiv fun _ => Fin q).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ (n := n + 1), Fin.cons_zero, Fin.cons_succ,
      Fin.castSucc_zero, ← Fin.succ_castSucc, Fin.cons_last]
    calc _ = ∑ x : Fin q, (q : ℂ) ^ n * ∑ a, ∑ b, cycB q a b * (cycB q x a * g x b) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← cycB_path q n (fun a b => cycB q x a * g x b)]
          refine Finset.sum_congr rfl fun y _ => ?_
          ring
      _ = ∑ x : Fin q, (q : ℂ) ^ n * ∑ b, (∑ a, cycB q x a * cycB q a b) * g x b := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          ring
      _ = _ := by
          simp_rw [cycB_sq, Finset.mul_sum, pow_succ]
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun b _ => ?_
          ring

/-- The cyclic trace `∑_{y : ℤ/(j+3) → [q]} ∏_i A_{y_i y_{i+1}} = tr(A^{j+3}) = q^{j+3}(q-1)`. -/
private lemma cycB_trace (q j : ℕ) :
    ∑ y : ZMod (j + 3) → Fin q, ∏ i : ZMod (j + 3), cycB q (y i) (y (i + 1)) =
      (q : ℂ) ^ (j + 3) * ((q : ℂ) - 1) := by
  change ∑ y : Fin (j + 3) → Fin q, ∏ i : Fin (j + 3), cycB q (y i) (y (i + 1)) = _
  have h : ∀ y : Fin (j + 3) → Fin q, ∏ i : Fin (j + 3), cycB q (y i) (y (i + 1)) =
      (∏ i : Fin (j + 2), cycB q (y i.castSucc) (y i.succ)) *
        cycB q (y (Fin.last (j + 2))) (y 0) := by
    intro y
    rw [Fin.prod_univ_castSucc, Fin.last_add_one]
    simp only [Fin.coeSucc_eq_succ]
  simp_rw [h]
  rw [cycB_path q (j + 1) (fun a b => cycB q b a)]
  simp_rw [cycB_sq]
  simp only [cycB, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

omit [Fintype V] in
private lemma edgeExp_edgeA_mk (q : ℕ) (σ : V → Fin q) (a b : V) :
    edgeA q σ s(a, b) = cycB q (σ a) (σ b) := by
  simp only [edgeA, Sym2.map_mk, Sym2.mk_isDiag_iff, cycB]

/-! ### Leaves -/

/-- A leaf annihilates the weight. -/
theorem edgeWeight_eq_zero_of_edgeDeg_eq_one {q : ℕ} {S : Finset (Sym2 V)}
    (hdiag : ∀ e ∈ S, ¬ e.IsDiag) {v : V} (hv : edgeDeg S v = 1) : edgeWeight q S = 0 := by
  obtain ⟨e₀, he₀⟩ := Finset.card_eq_one.mp hv
  have he₀mem : e₀ ∈ S.filter fun e => v ∈ e := by
    rw [he₀]; exact Finset.mem_singleton_self e₀
  rw [Finset.mem_filter] at he₀mem
  obtain ⟨he₀S, hve₀⟩ := he₀mem
  obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp hve₀
  have huv : u ≠ v := by
    intro h; subst h; exact hdiag _ he₀S (Sym2.mk_isDiag_iff.mpr rfl)
  have hother : ∀ e ∈ S.erase s(v, u), v ∉ e := by
    intro e he hve
    have : e ∈ S.filter fun e => v ∈ e :=
      Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase he, hve⟩
    rw [he₀, Finset.mem_singleton] at this
    exact (Finset.ne_of_mem_erase he) this
  unfold edgeWeight
  rw [mul_eq_zero]; right
  -- split off the colour of `v`
  rw [← (Equiv.funSplitAt v (Fin q)).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_eq_zero fun τ _ => ?_
  set σ : Fin q → V → Fin q := fun c => (Equiv.funSplitAt v (Fin q)).symm (c, τ) with hσ
  have hσv : ∀ c, σ c v = c := by
    intro c; simp [hσ, Equiv.funSplitAt_symm_apply]
  have hσw : ∀ c w (hw : w ≠ v), σ c w = τ ⟨w, hw⟩ := by
    intro c w hw; simp [hσ, Equiv.funSplitAt_symm_apply, hw]
  -- the edges other than `vu` do not see the colour of `v`
  have hrest : ∀ c, ∏ e ∈ S.erase s(v, u), edgeA q (σ c) e =
      ∏ e ∈ S.erase s(v, u), edgeA q (σ (τ ⟨u, huv⟩)) e := by
    intro c
    refine Finset.prod_congr rfl fun e he => ?_
    unfold edgeA
    rw [Sym2.map_congr (g := σ (τ ⟨u, huv⟩))]
    intro w hw
    have hwv : w ≠ v := fun h => hother e he (h ▸ hw)
    rw [hσw c w hwv, hσw _ w hwv]
  calc ∑ c, ∏ e ∈ S, edgeA q (σ c) e
      = ∑ c, edgeA q (σ c) s(v, u) * ∏ e ∈ S.erase s(v, u), edgeA q (σ (τ ⟨u, huv⟩)) e := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← Finset.mul_prod_erase S _ he₀S, hrest c]
    _ = (∑ c, edgeA q (σ c) s(v, u)) *
          ∏ e ∈ S.erase s(v, u), edgeA q (σ (τ ⟨u, huv⟩)) e := by
        rw [Finset.sum_mul]
    _ = 0 := by
        rw [mul_eq_zero]; left
        simp_rw [edgeExp_edgeA_mk, hσv, hσw _ u huv]
        exact cycB_sum_left q _

/-! ### Unions of vertex-disjoint cycles -/

/-- Reindexing a colour sum through an injective map `c : ι → V`:
`∑_{σ : V → [q]} F(σ ∘ c) = q^{|V| - |ι|} ∑_{x : ι → [q]} F x`. -/
private lemma edgeExp_sum_comp_injective {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℕ)
    {c : ι → V} (hc : Function.Injective c) (F : (ι → Fin q) → ℂ) :
    ∑ σ : V → Fin q, F (σ ∘ c) =
      (q : ℂ) ^ (Fintype.card V - Fintype.card ι) * ∑ x : ι → Fin q, F x := by
  let E := (Equiv.piEquivPiSubtypeProd (fun v => v ∈ Set.range c) (fun _ => Fin q)).trans
    (Equiv.prodCongr (Equiv.arrowCongr (Equiv.ofInjective c hc).symm (Equiv.refl (Fin q)))
      (Equiv.refl _))
  have hE : ∀ σ : V → Fin q, (E σ).1 = σ ∘ c := by
    intro σ; ext i
    simp [E, Equiv.arrowCongr_apply]
  rw [Fintype.sum_equiv E (fun σ => F (σ ∘ c)) (fun p => F p.1) (fun σ => by rw [hE]),
    Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow, ← Finset.mul_sum]
  congr 2
  rw [Fintype.card_subtype_compl]
  congr 1
  convert Set.card_range_of_injective hc

/-- A chosen representative cyclic sequence of a cycle. -/
private def edgeExpRep (γ : AnyCyc V) : ZMod (γ.1 + 3) → V :=
  (Quotient.out (s := CycSeq.setoid V γ.1) γ.2).1

omit [Fintype V] in
private lemma edgeExpRep_injective (γ : AnyCyc V) : Function.Injective (edgeExpRep γ) :=
  (Quotient.out (s := CycSeq.setoid V γ.1) γ.2).2

omit [Fintype V] in
private lemma edgeExpRep_edges (γ : AnyCyc V) :
    γ.edges = Finset.univ.image fun i => s(edgeExpRep γ i, edgeExpRep γ (i + 1)) := by
  have h : γ.2 =
      Quotient.mk (CycSeq.setoid V γ.1) (Quotient.out (s := CycSeq.setoid V γ.1) γ.2) :=
    (Quotient.out_eq _).symm
  show Cyc.edges γ.2 = _
  rw [h]
  rfl

private lemma edgeExpRep_mem_verts (γ : AnyCyc V) (i : ZMod (γ.1 + 3)) :
    edgeExpRep γ i ∈ γ.verts := by
  simp only [AnyCyc.verts, edgeVerts, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨s(edgeExpRep γ i, edgeExpRep γ (i + 1)), ?_, Sym2.mem_mk_left _ _⟩
  rw [edgeExpRep_edges]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

private lemma edgeExp_two_ne_zero (j : ℕ) : (2 : ZMod (j + 3)) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod (j + 3)) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  omega

omit [Fintype V] in
/-- For an injective cyclic sequence of length `≥ 3`, `i ↦ c_i c_{i+1}` is injective. -/
private lemma edgeExp_injective_edge {j : ℕ} {c : ZMod (j + 3) → V}
    (hc : Function.Injective c) : Function.Injective fun i => s(c i, c (i + 1)) := by
  intro i i' h
  simp only [Sym2.eq_iff] at h
  rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact hc h1
  · exfalso
    have e1 := hc h1
    have e2 := hc h2
    apply edgeExp_two_ne_zero j
    linear_combination e2 - e1

omit [Fintype V] in
private lemma edgeExp_prod_edges (q : ℕ) (σ : V → Fin q) (γ : AnyCyc V) :
    ∏ e ∈ γ.edges, edgeA q σ e =
      ∏ i : ZMod (γ.1 + 3), cycB q (σ (edgeExpRep γ i)) (σ (edgeExpRep γ (i + 1))) := by
  rw [edgeExpRep_edges, Finset.prod_image fun i _ i' _ h =>
    edgeExp_injective_edge (edgeExpRep_injective γ) h]
  simp only [edgeExp_edgeA_mk]

/-- A union of pairwise vertex-disjoint cycles has weight `(q-1)^{#cycles}`. -/
theorem edgeWeight_biUnion_cycles {q : ℕ} (hq : 1 ≤ q) (Γ : Finset (AnyCyc V))
    (hΓ : (Γ : Set (AnyCyc V)).PairwiseDisjoint AnyCyc.verts) :
    edgeWeight q (Γ.biUnion AnyCyc.edges) = ((q : ℂ) - 1) ^ Γ.card := by
  -- vertex-disjoint cycles are edge-disjoint
  have hedges : (Γ : Set (AnyCyc V)).PairwiseDisjoint AnyCyc.edges := by
    intro γ hγ γ' hγ' hne
    have hd : Disjoint γ.verts γ'.verts := hΓ hγ hγ' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    induction e using Sym2.ind with
    | h a b =>
      have ha : a ∈ γ.verts := by
        simp only [AnyCyc.verts, edgeVerts, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨_, he, Sym2.mem_mk_left _ _⟩
      have ha' : a ∈ γ'.verts := by
        simp only [AnyCyc.verts, edgeVerts, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨_, he', Sym2.mem_mk_left _ _⟩
      exact Finset.disjoint_left.mp hd ha ha'
  -- the combined injective map `Σ_γ ℤ/ℓ_γ → V`
  let ι := Σ γ : Γ, ZMod (γ.1.1 + 3)
  let C : ι → V := fun x => edgeExpRep x.1.1 x.2
  have hC : Function.Injective C := by
    rintro ⟨⟨γ, hγ⟩, i⟩ ⟨⟨γ', hγ'⟩, i'⟩ h
    simp only [C] at h
    by_cases hne : γ = γ'
    · subst hne
      have := edgeExpRep_injective γ h
      subst this
      rfl
    · exfalso
      have hd : Disjoint γ.verts γ'.verts := hΓ hγ hγ' hne
      exact Finset.disjoint_left.mp hd (edgeExpRep_mem_verts γ i)
        (h ▸ edgeExpRep_mem_verts γ' i')
  let F : (ι → Fin q) → ℂ := fun x =>
    ∏ γ : Γ, ∏ i : ZMod (γ.1.1 + 3), cycB q (x ⟨γ, i⟩) (x ⟨γ, i + 1⟩)
  have hprod : ∀ σ : V → Fin q, ∏ e ∈ Γ.biUnion AnyCyc.edges, edgeA q σ e = F (σ ∘ C) := by
    intro σ
    rw [Finset.prod_biUnion hedges, ← Finset.prod_coe_sort Γ]
    refine Finset.prod_congr rfl fun γ _ => ?_
    rw [edgeExp_prod_edges]
    rfl
  -- the colour sum factorizes over the cycles
  have hsum : ∑ x : ι → Fin q, F x =
      ∏ γ : Γ, ∑ y : ZMod (γ.1.1 + 3) → Fin q, ∏ i, cycB q (y i) (y (i + 1)) := by
    rw [Fintype.prod_sum]
    exact Fintype.sum_equiv (Equiv.piCurry fun (γ : Γ) (_ : ZMod (γ.1.1 + 3)) => Fin q) _ _
      (fun x => rfl)
  have hcard : Fintype.card ι = ∑ γ : Γ, (γ.1.1 + 3) := by
    simp [ι, Fintype.card_sigma, ZMod.card]
  have hle : Fintype.card ι ≤ Fintype.card V := Fintype.card_le_of_injective C hC
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  unfold edgeWeight
  simp_rw [hprod]
  rw [edgeExp_sum_comp_injective q hC F, hsum]
  simp_rw [cycB_trace]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_const, Finset.card_univ,
    Fintype.card_coe, ← hcard, ← mul_assoc ((q : ℂ) ^ (Fintype.card V - Fintype.card ι)),
    ← pow_add, Nat.sub_add_cancel hle, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq0), one_mul]

end

end ERZeroFreeness
