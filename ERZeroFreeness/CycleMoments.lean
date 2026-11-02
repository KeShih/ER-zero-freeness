/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs
import ERZeroFreeness.ErdosRenyi
import ERZeroFreeness.CycleStructure

/-!
# Factorial moments of short cycle counts (`lem:cycle-counts`)

For `G_n ∼ G(n, d/n)` with `d > 0`, `E ∏_{i<r} (C_{i+3}(G_n))_{k_i} → ∏_i λ_{i+3}^{k_i}` with
`λ_ℓ = d^ℓ/(2ℓ)` (`tendsto_erExp_cycle_descFactorial`).

Proof.  `∏_i (C_{i+3})_{k_i}` counts tuples `Φ ∈ ∏_i (Fin k_i ↪ {γ : Cyc V i | γ ⊆ G})`
(`Fintype.card_embedding_eq`), so its expectation is `∑_Φ p^{|⋃ edges(Φ)|}`, `p = d/n`, over
tuples of cycles of the complete graph (`erProb_subset_edgeFinset`).  Lift each cycle to its
`2(i+3)` representatives (`card_fiber_mk`); with `L = ∑ (i+3) k_i`:
* vertex-disjoint tuples correspond to injective maps `(Σ_i Fin k_i × ℤ/(i+3)) → Fin n`;
  there are `(n)_L` of them, each with `|⋃ edges| = L`, contributing
  `(n)_L (d/n)^L / ∏ (2(i+3))^{k_i} → ∏ λ^{k}`;
* tuples of distinct cycles that are not vertex-disjoint have
  `|⋃ edges| ≥ |⋃ verts| + 1` (`card_edgeVerts_lt_of_not_pairwiseDisjoint`); as at most `L^L`
  vertex maps have a given image, they contribute `O(p (1+p)^n) = O(1/n)` (for `n ≥ d`).

Implementation (namespace `CycMom`).  A family of cyclic sequences is
`Ψ : (i : Fin r) → Fin (k i) → CycSeq V i`; it is flattened to `flat Ψ : Idx r k → V` with
`Idx r k = Σ i, Fin (k i) × ZMod (i+3)`, `|Idx r k| = L`.  `erExp_eq` and `sum_lift` give
`M · E_n = ∑_Ψ [cycles distinct] p^{|⋃ edges|}` with `M = ∏ (2(i+3))^{k_i}`
(`main_identity`); the injective `flat Ψ` contribute `(n)_L p^L` (`card_filter_flat_injective`,
`card_UΦ_of_flat`), and the rest `Rem` satisfies
`0 ≤ Rem ≤ p ∑_{f : Idx → Fin n} p^{|f(Idx)|} ≤ p L^L (1+p)^n ≤ (d/n) L^L e^d`
(`card_image_flat_lt`, `sum_pow_card_image_le`).
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

namespace CycMom

/-! ### Elementary counting -/

lemma self_ne_add_one (m : ℕ) (x : ZMod (m + 3)) : x ≠ x + 1 := by
  intro h
  have h1 : ((1 : ℕ) : ZMod (m + 3)) = 0 := by push_cast; linear_combination -h
  rw [ZMod.natCast_eq_zero_iff] at h1
  have := Nat.le_of_dvd (by norm_num) h1
  omega

lemma self_ne_add_two (m : ℕ) (x : ZMod (m + 3)) : x ≠ x + 1 + 1 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod (m + 3)) = 0 := by push_cast; linear_combination -h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

/-- The number of injective maps `Fin m → α` with values in a finset `S` is `(|S|)_m`. -/
lemma card_filter_injective {α : Type*} [Fintype α] (S : Finset α) (m : ℕ) :
    (Finset.univ.filter fun f : Fin m → α => Function.Injective f ∧ ∀ a, f a ∈ S).card =
      S.card.descFactorial m := by
  rw [← Fintype.card_subtype]
  have e : {f : Fin m → α // Function.Injective f ∧ ∀ a, f a ∈ S} ≃ (Fin m ↪ S) :=
    { toFun := fun f => ⟨fun a => ⟨f.1 a, f.2.2 a⟩, fun a b h => f.2.1 (congrArg Subtype.val h)⟩
      invFun := fun e => ⟨fun a => (e a).1, fun a b h => e.injective (Subtype.ext h),
        fun a => (e a).2⟩
      left_inv := fun f => rfl
      right_inv := fun e => rfl }
  rw [Fintype.card_congr e, Fintype.card_embedding_eq]
  simp

/-- Maps `J → W` with a prescribed image `T` number at most `|J|^|J|`. -/
lemma card_fiber_image_le {J W : Type*} [Fintype J] [Fintype W] [DecidableEq J] [DecidableEq W]
    (T : Finset W) :
    (Finset.univ.filter fun f : J → W => Finset.univ.image f = T).card ≤
      Fintype.card J ^ Fintype.card J := by
  by_cases hT : T.card ≤ Fintype.card J
  · calc _ ≤ (Fintype.piFinset fun _ : J => T).card := by
          apply Finset.card_le_card
          intro f hf
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
          simp only [Fintype.mem_piFinset]
          intro j
          rw [← hf]
          exact Finset.mem_image_of_mem f (Finset.mem_univ j)
      _ = T.card ^ Fintype.card J := by simp [Fintype.card_piFinset]
      _ ≤ _ := Nat.pow_le_pow_left hT _
  · have : (Finset.univ.filter fun f : J → W => Finset.univ.image f = T) = ∅ := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hf
      apply hT
      rw [← hf]
      exact Finset.card_image_le.trans (by simp)
    simp [this]

/-- `∑_{f : J → W} p^{|f(J)|} ≤ |J|^{|J|} (1+p)^{|W|}`. -/
lemma sum_pow_card_image_le {J W : Type*} [Fintype J] [Fintype W] [DecidableEq J] [DecidableEq W]
    {p : ℝ} (hp : 0 ≤ p) :
    ∑ f : J → W, p ^ (Finset.univ.image f).card ≤
      (Fintype.card J : ℝ) ^ Fintype.card J * (p + 1) ^ Fintype.card W := by
  rw [← Finset.sum_fiberwise Finset.univ (fun f : J → W => Finset.univ.image f)]
  calc ∑ T : Finset W, ∑ f ∈ Finset.univ with Finset.univ.image f = T,
          p ^ (Finset.univ.image f).card
      = ∑ T : Finset W, ((Finset.univ.filter fun f : J → W => Finset.univ.image f = T).card : ℝ) *
          p ^ T.card := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [Finset.sum_congr rfl (g := fun _ => p ^ T.card)
          (fun f hf => by rw [(Finset.mem_filter.1 hf).2]), Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ T : Finset W, (Fintype.card J : ℝ) ^ Fintype.card J * p ^ T.card := by
        refine Finset.sum_le_sum fun T _ => ?_
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp _)
        exact_mod_cast card_fiber_image_le T
    _ = _ := by
        rw [← Finset.mul_sum]
        congr 1
        have := Fintype.sum_pow_mul_eq_add_pow W p 1
        simpa using this

/-! ### Families of cycles and of cyclic sequences -/

variable {V : Type*}

/-- The union of the edge sets of a family of cycles `Φ i a` (`a < k i`, of length `i + 3`). -/
def UΦ {r : ℕ} {k : Fin r → ℕ} (Φ : (i : Fin r) → Fin (k i) → Cyc V i) : Finset (Sym2 V) :=
  Finset.univ.biUnion fun ia : (Σ i : Fin r, Fin (k i)) => (Φ ia.1 ia.2).edges

lemma UΦ_subset_iff {r : ℕ} {k : Fin r → ℕ} (Φ : (i : Fin r) → Fin (k i) → Cyc V i)
    (E : Finset (Sym2 V)) : UΦ Φ ⊆ E ↔ ∀ i a, (Φ i a).edges ⊆ E := by
  simp [UΦ, Sigma.forall]

/-- The edges of a cycle are not loops. -/
lemma not_isDiag_of_mem_edges {j : ℕ} (γ : Cyc V j) {e : Sym2 V} (he : e ∈ γ.edges) :
    ¬ e.IsDiag := by
  induction γ using Quotient.inductionOn with
  | h c =>
    change e ∈ c.edges at he
    simp only [CycSeq.edges, Finset.mem_image, Finset.mem_univ, true_and] at he
    obtain ⟨x, rfl⟩ := he
    rw [Sym2.mk_isDiag_iff]
    exact fun h => self_ne_add_one j x (c.2 h)

lemma not_isDiag_of_mem_UΦ {r : ℕ} {k : Fin r → ℕ} (Φ : (i : Fin r) → Fin (k i) → Cyc V i)
    {e : Sym2 V} (he : e ∈ UΦ Φ) : ¬ e.IsDiag := by
  simp only [UΦ, Finset.mem_biUnion, Finset.mem_univ, true_and] at he
  obtain ⟨ia, he⟩ := he
  exact not_isDiag_of_mem_edges (Φ ia.1 ia.2) he

/-- The cycles represented by a family of cyclic sequences. -/
def mkΨ {r : ℕ} {k : Fin r → ℕ} (Ψ : (i : Fin r) → Fin (k i) → CycSeq V i) :
    (i : Fin r) → Fin (k i) → Cyc V i :=
  fun i a => Quotient.mk _ (Ψ i a)

/-- The index set `Σ_i Fin k_i × ℤ/(i+3)` of the vertices of a family of cyclic sequences. -/
abbrev Idx (r : ℕ) (k : Fin r → ℕ) : Type := Σ i : Fin r, Fin (k i) × ZMod (i.1 + 3)

/-- The next index along the same cyclic sequence. -/
def Idx.nxt {r : ℕ} {k : Fin r → ℕ} (j : Idx r k) : Idx r k := ⟨j.1, (j.2.1, j.2.2 + 1)⟩

/-- All vertices of a family of cyclic sequences, as one map `Idx r k → V`. -/
def flat {r : ℕ} {k : Fin r → ℕ} (Ψ : (i : Fin r) → Fin (k i) → CycSeq V i) : Idx r k → V :=
  fun j => (Ψ j.1 j.2.1).1 j.2.2

lemma card_Idx (r : ℕ) (k : Fin r → ℕ) :
    Fintype.card (Idx r k) = ∑ i : Fin r, k i * (i.1 + 3) := by
  simp [Fintype.card_sigma, Fintype.card_prod, ZMod.card]

lemma flat_injective {r : ℕ} {k : Fin r → ℕ} :
    Function.Injective (flat : ((i : Fin r) → Fin (k i) → CycSeq V i) → Idx r k → V) := by
  intro Ψ Ψ' h
  funext i a
  apply Subtype.ext
  funext x
  exact congrFun h ⟨i, (a, x)⟩

/-- Vertex-disjoint cyclic sequences represent distinct cycles. -/
lemma mkΨ_injective_of_flat {r : ℕ} {k : Fin r → ℕ} (Ψ : (i : Fin r) → Fin (k i) → CycSeq V i)
    (h : Function.Injective (flat Ψ)) (i : Fin r) : Function.Injective (mkΨ Ψ i) := by
  intro a b hab
  have hrel : CycSeq.Rel (Ψ i a) (Ψ i b) := Quotient.exact hab
  obtain ⟨s, hs | hs⟩ := hrel
  · have := @h ⟨i, (b, 0)⟩ ⟨i, (a, s + 0)⟩ (hs 0)
    simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at this
    exact this.1.symm
  · have := @h ⟨i, (b, 0)⟩ ⟨i, (a, s - 0)⟩ (hs 0)
    simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at this
    exact this.1.symm

lemma UΦ_mkΨ_eq_image {r : ℕ} {k : Fin r → ℕ} (Ψ : (i : Fin r) → Fin (k i) → CycSeq V i) :
    UΦ (mkΨ Ψ) = Finset.univ.image fun j : Idx r k => s(flat Ψ j, flat Ψ j.nxt) := by
  ext e
  simp only [UΦ, mkΨ, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Sigma.exists, Prod.exists]
  constructor
  · rintro ⟨i, a, he⟩
    change e ∈ (Ψ i a).edges at he
    simp only [CycSeq.edges, Finset.mem_image, Finset.mem_univ, true_and] at he
    obtain ⟨x, rfl⟩ := he
    exact ⟨i, a, x, rfl⟩
  · rintro ⟨i, a, x, rfl⟩
    refine ⟨i, a, ?_⟩
    change _ ∈ (Ψ i a).edges
    exact Finset.mem_image_of_mem _ (Finset.mem_univ x)

/-- Vertex-disjoint cyclic sequences span exactly `L = |Idx r k|` edges. -/
lemma card_UΦ_of_flat {r : ℕ} {k : Fin r → ℕ} (Ψ : (i : Fin r) → Fin (k i) → CycSeq V i)
    (h : Function.Injective (flat Ψ)) : (UΦ (mkΨ Ψ)).card = Fintype.card (Idx r k) := by
  rw [UΦ_mkΨ_eq_image, Finset.card_image_of_injective _ ?_, Finset.card_univ]
  intro j j' hjj'
  simp only [Sym2.eq_iff] at hjj'
  rcases hjj' with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact h h1
  · have e1 := h h1
    have e2 := h h2
    subst e2
    obtain ⟨i, a, x⟩ := j
    simp only [Idx.nxt, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at e1
    exact absurd e1 (self_ne_add_two _ x)

variable [Fintype V]

/-- `∏_i (C_{i+3}(G))_{k_i}` counts the families of cycles of `G`, injective in each length. -/
lemma prod_descFactorial_eq (G : SimpleGraph V) (r : ℕ) (k : Fin r → ℕ) :
    (∏ i, ((cycleCounts r G i).descFactorial (k i) : ℝ)) =
      ∑ Φ : (i : Fin r) → Fin (k i) → Cyc V i,
        if (∀ i, Function.Injective (Φ i)) ∧ UΦ Φ ⊆ G.edgeFinset then 1 else 0 := by
  rw [Finset.sum_boole]
  have hT : ∀ i : Fin r, (cycleCounts r G i).descFactorial (k i) =
      (Finset.univ.filter fun f : Fin (k i) → Cyc V i => Function.Injective f ∧
        ∀ a, f a ∈ Finset.univ.filter fun γ : Cyc V i => γ.edges ⊆ G.edgeFinset).card := by
    intro i
    rw [card_filter_injective]
    rfl
  simp_rw [hT]
  rw [← Nat.cast_prod, ← Fintype.card_piFinset]
  congr 2
  ext Φ
  simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and, UΦ_subset_iff]
  constructor
  · intro h
    exact ⟨fun i => (h i).1, fun i a => (h i).2 a⟩
  · intro h i
    exact ⟨h.1 i, fun a => h.2 i a⟩

/-- Each family of cycles is represented by `∏_i (2(i+3))^{k_i}` families of sequences. -/
lemma card_fiber_mkΨ {r : ℕ} {k : Fin r → ℕ} (Φ : (i : Fin r) → Fin (k i) → Cyc V i) :
    (Finset.univ.filter fun Ψ : (i : Fin r) → Fin (k i) → CycSeq V i => mkΨ Ψ = Φ).card =
      ∏ i : Fin r, (2 * (i.1 + 3)) ^ k i := by
  have : (Finset.univ.filter fun Ψ : (i : Fin r) → Fin (k i) → CycSeq V i => mkΨ Ψ = Φ) =
      Fintype.piFinset fun i : Fin r => Fintype.piFinset fun a : Fin (k i) =>
        Finset.univ.filter fun c : CycSeq V i.1 => (Quotient.mk _ c : Cyc V i.1) = Φ i a := by
    ext Ψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro rfl i a
      rfl
    · intro h
      funext i a
      exact h i a
  rw [this, Fintype.card_piFinset]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.card_piFinset]
  simp [card_fiber_mk]

lemma sum_lift {r : ℕ} {k : Fin r → ℕ} (F : ((i : Fin r) → Fin (k i) → Cyc V i) → ℝ) :
    ∑ Ψ : (i : Fin r) → Fin (k i) → CycSeq V i, F (mkΨ Ψ) =
      (∏ i : Fin r, (2 * ((i : ℝ) + 3)) ^ k i) * ∑ Φ, F Φ := by
  rw [← Finset.sum_fiberwise Finset.univ mkΨ (fun Ψ => F (mkΨ Ψ)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun Φ _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => F Φ) (fun Ψ hΨ => by rw [(Finset.mem_filter.1 hΨ).2]),
    Finset.sum_const, card_fiber_mkΨ, nsmul_eq_mul]
  push_cast
  ring

/-- There are `(|V|)_L` vertex-disjoint families of cyclic sequences. -/
lemma card_filter_flat_injective (r : ℕ) (k : Fin r → ℕ) :
    (Finset.univ.filter fun Ψ : (i : Fin r) → Fin (k i) → CycSeq V i =>
        Function.Injective (flat Ψ)).card =
      (Fintype.card V).descFactorial (Fintype.card (Idx r k)) := by
  rw [← Fintype.card_subtype, ← Fintype.card_embedding_eq]
  refine Fintype.card_congr
    { toFun := fun Ψ => ⟨flat Ψ.1, Ψ.2⟩
      invFun := fun e => ⟨fun i a => ⟨fun x => e ⟨i, (a, x)⟩, fun x y hxy => by
          have := e.injective hxy
          simpa using this⟩, e.injective⟩
      left_inv := fun Ψ => rfl
      right_inv := fun e => rfl }

lemma mem_verts_mk {j : ℕ} (c : CycSeq V j) (x : ZMod (j + 3)) :
    c.1 x ∈ AnyCyc.verts (⟨j, Quotient.mk _ c⟩ : AnyCyc V) := by
  simp only [AnyCyc.verts, edgeVerts, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨s(c.1 x, c.1 (x + 1)), ?_, Sym2.mem_mk_left _ _⟩
  change _ ∈ c.edges
  exact Finset.mem_image_of_mem _ (Finset.mem_univ x)

/-- Distinct cycles that are not vertex-disjoint span more edges than vertices. -/
lemma card_image_flat_lt {r : ℕ} {k : Fin r → ℕ} (Ψ : (i : Fin r) → Fin (k i) → CycSeq V i)
    (hflat : ¬ Function.Injective (flat Ψ)) (hinj : ∀ i, Function.Injective (mkΨ Ψ i)) :
    (Finset.univ.image (flat Ψ)).card < (UΦ (mkΨ Ψ)).card := by
  set Γ : Finset (AnyCyc V) := Finset.univ.image
    fun ia : (Σ i : Fin r, Fin (k i)) => (⟨ia.1.1, mkΨ Ψ ia.1 ia.2⟩ : AnyCyc V) with hΓ
  have hU : Γ.biUnion AnyCyc.edges = UΦ (mkΨ Ψ) := by
    rw [hΓ, Finset.image_biUnion]
    rfl
  have hnd : ¬ (Γ : Set (AnyCyc V)).PairwiseDisjoint AnyCyc.verts := by
    intro hpd
    apply hflat
    rintro ⟨i, a, x⟩ ⟨i', a', x'⟩ hjj'
    by_cases hc : (⟨i.1, mkΨ Ψ i a⟩ : AnyCyc V) = ⟨i'.1, mkΨ Ψ i' a'⟩
    · rw [Sigma.mk.inj_iff] at hc
      obtain ⟨h1, h2⟩ := hc
      obtain rfl : i = i' := Fin.ext h1
      obtain rfl : a = a' := hinj i (eq_of_heq h2)
      obtain rfl : x = x' := (Ψ i a).2 hjj'
      rfl
    · exfalso
      have hmem : ∀ (i : Fin r) (a : Fin (k i)), (⟨i.1, mkΨ Ψ i a⟩ : AnyCyc V) ∈ Γ := by
        intro i a
        rw [hΓ]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ (⟨i, a⟩ : Σ i : Fin r, Fin (k i)))
      have hdis := hpd (hmem i a) (hmem i' a') hc
      have hv : flat Ψ ⟨i, (a, x)⟩ ∈ AnyCyc.verts (⟨i.1, mkΨ Ψ i a⟩ : AnyCyc V) :=
        mem_verts_mk (Ψ i a) x
      have hv' : flat Ψ ⟨i, (a, x)⟩ ∈ AnyCyc.verts (⟨i'.1, mkΨ Ψ i' a'⟩ : AnyCyc V) := by
        rw [hjj']
        exact mem_verts_mk (Ψ i' a') x'
      exact Finset.disjoint_left.1 hdis hv hv'
  have hlt := card_edgeVerts_lt_of_not_pairwiseDisjoint Γ hnd
  rw [hU] at hlt
  refine lt_of_le_of_lt (Finset.card_le_card ?_) hlt
  intro v hv
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv
  obtain ⟨⟨i, a, x⟩, rfl⟩ := hv
  simp only [edgeVerts, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨s(flat Ψ ⟨i, (a, x)⟩, flat Ψ (Idx.nxt ⟨i, (a, x)⟩)), ?_, Sym2.mem_mk_left _ _⟩
  rw [UΦ_mkΨ_eq_image]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

/-! ### The expectation -/

/-- `E ∏_i (C_{i+3})_{k_i} = ∑_Φ p^{|⋃ edges(Φ)|}` over families of cycles of `K_n` that are
injective in each length. -/
lemma erExp_eq (n : ℕ) (p : ℝ) (r : ℕ) (k : Fin r → ℕ) :
    erExp n p (fun G => ∏ i, ((cycleCounts r G i).descFactorial (k i) : ℝ)) =
      ∑ Φ : (i : Fin r) → Fin (k i) → Cyc (Fin n) i,
        if (∀ i, Function.Injective (Φ i)) then p ^ (UΦ Φ).card else 0 := by
  unfold erExp
  simp_rw [prod_descFactorial_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Φ _ => ?_
  split_ifs with hΦ
  · rw [← erProb_subset_edgeFinset (UΦ Φ) (fun e he => by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top]
      exact not_isDiag_of_mem_UΦ Φ he)]
    unfold erProb
    refine Finset.sum_congr rfl fun G _ => ?_
    have hiff : (G ∈ {G : SimpleGraph (Fin n) | UΦ Φ ⊆ G.edgeFinset}) ↔
        UΦ Φ ⊆ G.edgeFinset := by
      simp only [Set.mem_ofPred_eq, Finset.subset_iff, SimpleGraph.mem_edgeFinset]
    by_cases h : UΦ Φ ⊆ G.edgeFinset
    · rw [if_pos (hiff.2 h), if_pos ⟨hΦ, h⟩, mul_one]
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg (fun h' => h h'.2), mul_zero]
  · refine Finset.sum_eq_zero fun G _ => ?_
    rw [if_neg (fun h => hΦ h.1), mul_zero]

/-- The contribution of families of distinct cycles that are not vertex-disjoint. -/
def Rem (n : ℕ) (p : ℝ) (r : ℕ) (k : Fin r → ℕ) : ℝ :=
  ∑ Ψ : (i : Fin r) → Fin (k i) → CycSeq (Fin n) i,
    if ¬ Function.Injective (flat Ψ) ∧ (∀ i, Function.Injective (mkΨ Ψ i)) then
      p ^ (UΦ (mkΨ Ψ)).card else 0

lemma main_identity (n : ℕ) (p : ℝ) (r : ℕ) (k : Fin r → ℕ) :
    (∏ i : Fin r, (2 * ((i : ℝ) + 3)) ^ k i) *
        erExp n p (fun G => ∏ i, ((cycleCounts r G i).descFactorial (k i) : ℝ)) =
      (n.descFactorial (Fintype.card (Idx r k)) : ℝ) * p ^ Fintype.card (Idx r k) +
        Rem n p r k := by
  have hlift := sum_lift (V := Fin n) (r := r) (k := k)
    (fun Φ => if (∀ i, Function.Injective (Φ i)) then p ^ (UΦ Φ).card else 0)
  rw [erExp_eq, ← hlift]
  have hsplit : ∀ Ψ : (i : Fin r) → Fin (k i) → CycSeq (Fin n) i,
      (if (∀ i, Function.Injective (mkΨ Ψ i)) then p ^ (UΦ (mkΨ Ψ)).card else 0) =
        (if Function.Injective (flat Ψ) then p ^ Fintype.card (Idx r k) else 0) +
        (if ¬ Function.Injective (flat Ψ) ∧ (∀ i, Function.Injective (mkΨ Ψ i)) then
          p ^ (UΦ (mkΨ Ψ)).card else 0) := by
    intro Ψ
    by_cases h : Function.Injective (flat Ψ)
    · rw [if_pos (mkΨ_injective_of_flat Ψ h), if_pos h, if_neg (fun h' => h'.1 h), add_zero,
        card_UΦ_of_flat Ψ h]
    · rw [if_neg h, zero_add]
      by_cases h' : ∀ i, Function.Injective (mkΨ Ψ i)
      · rw [if_pos h', if_pos ⟨h, h'⟩]
      · rw [if_neg h', if_neg (fun h'' => h' h''.2)]
  have hcard : (Finset.univ.filter fun Ψ : (i : Fin r) → Fin (k i) → CycSeq (Fin n) i =>
      Function.Injective (flat Ψ)).card = n.descFactorial (Fintype.card (Idx r k)) := by
    have h := card_filter_flat_injective (V := Fin n) r k
    rw [Fintype.card_fin] at h
    convert h
  rw [Finset.sum_congr rfl (fun Ψ _ => hsplit Ψ), Finset.sum_add_distrib, Finset.sum_ite,
    Finset.sum_const_zero, add_zero, Finset.sum_const, hcard, nsmul_eq_mul]
  rfl

lemma Rem_nonneg {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (r : ℕ) (k : Fin r → ℕ) : 0 ≤ Rem n p r k :=
  Finset.sum_nonneg fun Ψ _ => by split_ifs <;> positivity

lemma Rem_le {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (r : ℕ) (k : Fin r → ℕ) :
    Rem n p r k ≤
      p * ((Fintype.card (Idx r k) : ℝ) ^ Fintype.card (Idx r k) * (p + 1) ^ n) := by
  unfold Rem
  calc ∑ Ψ : (i : Fin r) → Fin (k i) → CycSeq (Fin n) i,
        (if ¬ Function.Injective (flat Ψ) ∧ (∀ i, Function.Injective (mkΨ Ψ i)) then
          p ^ (UΦ (mkΨ Ψ)).card else 0)
      ≤ ∑ Ψ : (i : Fin r) → Fin (k i) → CycSeq (Fin n) i,
          p * p ^ (Finset.univ.image (flat Ψ)).card := by
        refine Finset.sum_le_sum fun Ψ _ => ?_
        split_ifs with h
        · rw [← pow_succ']
          refine pow_le_pow_of_le_one hp0 hp1 (Nat.succ_le_of_lt ?_)
          convert card_image_flat_lt Ψ h.1 h.2 using 3
        · positivity
    _ = ∑ f ∈ Finset.univ.image flat, p * p ^ (Finset.univ.image f).card := by
        rw [Finset.sum_image (fun Ψ _ Ψ' _ h => flat_injective h)]
    _ ≤ ∑ f : Idx r k → Fin n, p * p ^ (Finset.univ.image f).card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => by positivity)
    _ = p * ∑ f : Idx r k → Fin n, p ^ (Finset.univ.image f).card := by rw [Finset.mul_sum]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hp0
        have := sum_pow_card_image_le (J := Idx r k) (W := Fin n) hp0
        simpa using this

/-! ### Asymptotics -/

lemma one_add_div_pow_le_exp {d : ℝ} (hd : 0 ≤ d) {n : ℕ} (hn : n ≠ 0) :
    (d / n + 1) ^ n ≤ Real.exp d := by
  calc (d / n + 1) ^ n ≤ Real.exp (d / n) ^ n :=
        pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) n
    _ = Real.exp d := by
        rw [← Real.exp_nat_mul, mul_div_cancel₀]
        exact_mod_cast hn

lemma tendsto_descFactorial_mul_pow (d : ℝ) (L : ℕ) :
    Tendsto (fun n : ℕ => (n.descFactorial L : ℝ) * (d / n) ^ L) atTop (𝓝 (d ^ L)) := by
  have h1 := (isEquivalent_descFactorial L).mul
    (Asymptotics.IsEquivalent.refl (u := fun n : ℕ => (d / n) ^ L) (l := atTop))
  have h2 : Tendsto (fun n : ℕ => (n : ℝ) ^ L * (d / n) ^ L) atTop (𝓝 (d ^ L)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [← mul_pow, mul_div_cancel₀]
    exact_mod_cast (by omega : n ≠ 0)
  exact h1.symm.tendsto_nhds h2

lemma prod_cycleMean_pow (d : ℝ) (r : ℕ) (k : Fin r → ℕ) :
    ∏ i : Fin r, cycleMean d i ^ k i =
      (∏ i : Fin r, (2 * ((i : ℝ) + 3)) ^ k i)⁻¹ * (d ^ Fintype.card (Idx r k) + 0) := by
  rw [add_zero, card_Idx, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold cycleMean
  rw [div_pow, ← pow_mul, mul_comm (k i), div_eq_mul_inv, mul_comm]

end CycMom

/-- **Factorial moments of the short cycle counts** (limit form of `eq:cycle-factorials`): for
`G_n ∼ G(n, d/n)`, `E ∏_{i<r} (C_{i+3}(G_n))_{k_i} → ∏_i λ_{i+3}^{k_i}`, `λ_ℓ = d^ℓ/(2ℓ)`. -/
theorem tendsto_erExp_cycle_descFactorial {d : ℝ} (hd : 0 < d) (r : ℕ) (k : Fin r → ℕ) :
    Tendsto (fun n : ℕ => erExp n (d / n)
        fun G => ∏ i, ((cycleCounts r G i).descFactorial (k i) : ℝ))
      atTop (𝓝 (∏ i : Fin r, cycleMean d i ^ k i)) := by
  set L := Fintype.card (CycMom.Idx r k) with hL
  set M : ℝ := ∏ i : Fin r, (2 * ((i : ℝ) + 3)) ^ k i with hM
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (by positivity)
  rw [CycMom.prod_cycleMean_pow]
  have hA := CycMom.tendsto_descFactorial_mul_pow d L
  have hR : Tendsto (fun n : ℕ => CycMom.Rem n (d / n) r k) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun n : ℕ => d * ((L : ℝ) ^ L * Real.exp d) / n)
    · filter_upwards with n
      exact CycMom.Rem_nonneg (by positivity) r k
    · filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈d⌉₊] with n hn hnd
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hdn : d ≤ n := (Nat.le_ceil d).trans (by exact_mod_cast hnd)
      have hp0 : 0 ≤ d / n := by positivity
      have hp1 : d / n ≤ 1 := (div_le_one hn0).2 hdn
      calc CycMom.Rem n (d / n) r k ≤ d / n * ((L : ℝ) ^ L * (d / n + 1) ^ n) :=
            CycMom.Rem_le hp0 hp1 r k
        _ ≤ d / n * ((L : ℝ) ^ L * Real.exp d) := by
            gcongr
            exact CycMom.one_add_div_pow_le_exp hd.le (by omega)
        _ = _ := by ring
    · exact tendsto_const_div_atTop_nhds_zero_nat _
  refine ((hA.add hR).const_mul M⁻¹).congr' ?_
  filter_upwards with n
  rw [← CycMom.main_identity n (d / n) r k, ← mul_assoc, inv_mul_cancel₀ hM0, one_mul]

end

end ERZeroFreeness
