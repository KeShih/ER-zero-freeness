/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs

/-!
# Structure of cycles and of 2-regular edge sets

Facts about the cycles `AnyCyc V` (injective cyclic sequences `c : ℤ/(j+3) → V` up to the
dihedral action) used in `lem:cycle-counts` and `lem:jets`.

Proofs.
* For an injective cyclic sequence `c` of length `ℓ ≥ 3`, `i ↦ s(c i, c (i+1))` is injective,
  so `|edges| = ℓ`; the edges at `c a` are exactly `s(c(a-1), c a)` and `s(c a, c(a+1))`.
* `AnyCyc.edges_subset_of_edgeDeg_le_two` (walking lemma): in an edge set of maximum degree
  `2`, the two edges of a cycle at any of its vertices are all the edges of the set there; so
  if two cycles in the set share a vertex, walking along the first one never leaves the
  second, and the first is contained in the second.
* `AnyCyc.eq_of_edges_subset`: if `γ.edges ⊆ γ'.edges`, the walking lemma in `γ'.edges`
  gives the reverse inclusion, so both cycles have the same length.  For sequences `c, c'`
  of the same length with `edges c' ⊆ edges c`, write `c' 0 = c a`; the neighbour `c' 1` is
  `c (a + ε)` with `ε = ±1`, and by induction `c' i = c (a + ε i)` (the next vertex is the
  neighbour different from the previous one), so `c'` is a rotation or a reflection of `c`.
* `exists_cycle_decomp`: strong induction on `|S|`.  A nonempty loopless edge set in which
  every touched vertex has degree `2` contains a cycle: run a non-backtracking walk
  `v₀, v₁, …` (`v_{i+1}` the neighbour of `v_i` other than `v_{i-1}`) and stop at the first
  repetition `v_j = v_i`, `i < j`; then `v_i, …, v_{j-1}` is an injective cyclic sequence of
  length `j - i ≥ 3` whose edges lie in `S`.  Removing its edges leaves a 2-regular set on
  the remaining vertices.
* `card_edgeVerts_lt_of_not_pairwiseDisjoint`: every vertex of `H = ⋃ edges` has
  `H`-degree at least `2`, so `|edgeVerts H| ≤ |H|` by the handshake lemma; equality forces
  every vertex to have `H`-degree `2`, and then a cycle sharing a vertex with another one is
  contained in it (walking lemma), hence equal to it by `AnyCyc.eq_of_edges_subset`.
* `card_fiber_mk`: the `2(j+3)` maps `i ↦ c (a ± i)` are pairwise distinct for injective `c`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V]

/-! ### Helper lemmas: indices, cyclic sequences, edge sets -/

private theorem cs_zmod_one_ne_zero (j : ℕ) : (1 : ZMod (j + 3)) ≠ 0 := by
  intro h
  have h' : ((1 : ℕ) : ZMod (j + 3)) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd one_pos h'
  omega

private theorem cs_zmod_two_ne_zero (j : ℕ) : (2 : ZMod (j + 3)) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod (j + 3)) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd two_pos h'
  omega

omit [Fintype V] in
private theorem cs_congr {j : ℕ} (c : CycSeq V j) {x y : ZMod (j + 3)} (h : x = y) :
    c.1 x = c.1 y :=
  congrArg c.1 h

omit [Fintype V] in
private theorem cs_mem_edges {j : ℕ} {c : CycSeq V j} {e : Sym2 V} :
    e ∈ c.edges ↔ ∃ i, s(c.1 i, c.1 (i + 1)) = e := by
  simp [CycSeq.edges]

omit [Fintype V] in
private theorem cs_mk_mem_edges {j : ℕ} (c : CycSeq V j) (i : ZMod (j + 3)) :
    s(c.1 i, c.1 (i + 1)) ∈ c.edges :=
  cs_mem_edges.2 ⟨i, rfl⟩

omit [Fintype V] in
private theorem cs_apply_ne_apply_add_one {j : ℕ} (c : CycSeq V j) (i : ZMod (j + 3)) :
    c.1 i ≠ c.1 (i + 1) := by
  intro h
  have h' := c.2 h
  apply cs_zmod_one_ne_zero j
  linear_combination -h'

omit [Fintype V] in
/-- The edges of `c` at the vertex `c a` go to `c (a + 1)` and `c (a - 1)`. -/
private theorem cs_mk_mem_edges_iff {j : ℕ} (c : CycSeq V j) (a : ZMod (j + 3)) (x : V) :
    s(c.1 a, x) ∈ c.edges ↔ x = c.1 (a + 1) ∨ x = c.1 (a - 1) := by
  rw [cs_mem_edges]
  constructor
  · rintro ⟨i, hi⟩
    rcases Sym2.eq_iff.1 hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h3 := c.2 h1
      subst h3
      exact Or.inl h2.symm
    · have h3 := c.2 h2
      right
      rw [← h1]
      exact cs_congr c (by linear_combination h3)
  · rintro (rfl | rfl)
    · exact ⟨a, rfl⟩
    · exact ⟨a - 1, by rw [sub_add_cancel, Sym2.eq_swap]⟩

omit [Fintype V] in
private theorem cs_edges_card {j : ℕ} (c : CycSeq V j) : c.edges.card = j + 3 := by
  rw [CycSeq.edges, Finset.card_image_of_injective, Finset.card_univ, ZMod.card]
  intro i k h
  dsimp only at h
  rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact c.2 h1
  · have e1 := c.2 h1
    have e2 := c.2 h2
    exfalso
    apply cs_zmod_two_ne_zero j
    linear_combination e2 - e1

private theorem cs_mem_edgeVerts_iff {S : Finset (Sym2 V)} {v : V} :
    v ∈ edgeVerts S ↔ ∃ e ∈ S, v ∈ e := by
  simp [edgeVerts]

private theorem cs_edgeVerts_mono {S T : Finset (Sym2 V)} (h : S ⊆ T) :
    edgeVerts S ⊆ edgeVerts T := by
  intro v hv
  obtain ⟨e, he, hve⟩ := cs_mem_edgeVerts_iff.1 hv
  exact cs_mem_edgeVerts_iff.2 ⟨e, h he, hve⟩

private theorem cs_edgeDeg_eq_zero {S : Finset (Sym2 V)} {v : V} (hv : v ∉ edgeVerts S) :
    edgeDeg S v = 0 := by
  rw [edgeDeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e he hve
  exact hv (cs_mem_edgeVerts_iff.2 ⟨e, he, hve⟩)

private theorem cs_mem_edgeVerts {j : ℕ} (c : CycSeq V j) (v : V) :
    v ∈ edgeVerts c.edges ↔ ∃ i, c.1 i = v := by
  rw [cs_mem_edgeVerts_iff]
  constructor
  · rintro ⟨e, he, hv⟩
    obtain ⟨i, rfl⟩ := cs_mem_edges.1 he
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact ⟨i, rfl⟩
    · exact ⟨i + 1, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, cs_mk_mem_edges c i, Sym2.mem_mk_left _ _⟩

omit [Fintype V] in
private theorem cs_filter_edges {j : ℕ} (c : CycSeq V j) (a : ZMod (j + 3)) :
    c.edges.filter (fun e => c.1 a ∈ e) = {s(c.1 a, c.1 (a + 1)), s(c.1 a, c.1 (a - 1))} := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨he, hv⟩
    obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.1 hv
    rcases (cs_mk_mem_edges_iff c a x).1 he with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨(cs_mk_mem_edges_iff c a _).2 (Or.inl rfl), Sym2.mem_mk_left _ _⟩
    · exact ⟨(cs_mk_mem_edges_iff c a _).2 (Or.inr rfl), Sym2.mem_mk_left _ _⟩

omit [Fintype V] in
private theorem cs_edgeDeg {j : ℕ} (c : CycSeq V j) (a : ZMod (j + 3)) :
    edgeDeg c.edges (c.1 a) = 2 := by
  rw [edgeDeg, cs_filter_edges, Finset.card_pair]
  intro h
  rcases Sym2.eq_iff.1 h with ⟨-, h⟩ | ⟨h, -⟩
  · have h' := c.2 h
    apply cs_zmod_two_ne_zero j
    linear_combination h'
  · have h' := c.2 h
    apply cs_zmod_one_ne_zero j
    linear_combination h'

/-! ### Representatives of cycles -/

omit [Fintype V] in
private theorem cs_anyCyc_exists_rep (γ : AnyCyc V) :
    ∃ (j : ℕ) (c : CycSeq V j), γ = ⟨j, Quotient.mk _ c⟩ := by
  obtain ⟨j, q⟩ := γ
  obtain ⟨c, rfl⟩ := Quotient.exists_rep q
  exact ⟨j, c, rfl⟩

omit [Fintype V] in
private theorem cs_anyCyc_edges_mk {j : ℕ} (c : CycSeq V j) :
    AnyCyc.edges (⟨j, Quotient.mk _ c⟩ : AnyCyc V) = c.edges := rfl

private theorem cs_anyCyc_mem_verts {γ : AnyCyc V} {e : Sym2 V} {v : V} (he : e ∈ γ.edges)
    (hv : v ∈ e) : v ∈ γ.verts :=
  cs_mem_edgeVerts_iff.2 ⟨e, he, hv⟩

theorem AnyCyc.card_edges (γ : AnyCyc V) : γ.edges.card = γ.1 + 3 := by
  obtain ⟨j, c, rfl⟩ := cs_anyCyc_exists_rep γ
  exact cs_edges_card c

theorem AnyCyc.card_verts (γ : AnyCyc V) : γ.verts.card = γ.1 + 3 := by
  obtain ⟨j, c, rfl⟩ := cs_anyCyc_exists_rep γ
  have h : edgeVerts c.edges = Finset.univ.image c.1 := by
    ext v
    rw [cs_mem_edgeVerts]
    simp
  show (edgeVerts c.edges).card = j + 3
  rw [h, Finset.card_image_of_injective _ c.2, Finset.card_univ, ZMod.card]

theorem AnyCyc.not_isDiag (γ : AnyCyc V) {e : Sym2 V} (he : e ∈ γ.edges) : ¬ e.IsDiag := by
  obtain ⟨j, c, rfl⟩ := cs_anyCyc_exists_rep γ
  rw [cs_anyCyc_edges_mk] at he
  obtain ⟨i, rfl⟩ := cs_mem_edges.1 he
  rw [Sym2.mk_isDiag_iff]
  exact cs_apply_ne_apply_add_one c i

theorem AnyCyc.edgeDeg_eq_two (γ : AnyCyc V) {v : V} (hv : v ∈ γ.verts) :
    edgeDeg γ.edges v = 2 := by
  obtain ⟨j, c, rfl⟩ := cs_anyCyc_exists_rep γ
  obtain ⟨a, rfl⟩ := (cs_mem_edgeVerts c v).1 hv
  exact cs_edgeDeg c a

/-! ### The walking lemmas -/

/-- If two cycles lie in an edge set of maximum degree `2` and share the vertex `w`, they have
the same edges at `w`. -/
private theorem cs_anyCyc_filter_eq {γ γ' : AnyCyc V} {S : Finset (Sym2 V)}
    (hγ : γ.edges ⊆ S) (hγ' : γ'.edges ⊆ S) (hS : ∀ v, edgeDeg S v ≤ 2) {w : V}
    (hw : w ∈ γ.verts) (hw' : w ∈ γ'.verts) :
    γ.edges.filter (fun e => w ∈ e) = γ'.edges.filter (fun e => w ∈ e) := by
  have h1 : γ.edges.filter (fun e => w ∈ e) = S.filter (fun e => w ∈ e) := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset_filter _ hγ)
    have h2 := hS w
    have h3 := γ.edgeDeg_eq_two hw
    unfold edgeDeg at h2 h3
    omega
  have h2 : γ'.edges.filter (fun e => w ∈ e) = S.filter (fun e => w ∈ e) := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset_filter _ hγ')
    have h2 := hS w
    have h3 := γ'.edgeDeg_eq_two hw'
    unfold edgeDeg at h2 h3
    omega
  rw [h1, h2]

/-- In an edge set of maximum degree `2`, a cycle sharing a vertex with another cycle is
contained in it (walk along the first cycle). -/
private theorem cs_anyCyc_edges_subset {γ γ' : AnyCyc V} {S : Finset (Sym2 V)}
    (hγ : γ.edges ⊆ S) (hγ' : γ'.edges ⊆ S) (hS : ∀ v, edgeDeg S v ≤ 2)
    (hv : ¬ Disjoint γ.verts γ'.verts) : γ.edges ⊆ γ'.edges := by
  obtain ⟨w, hw, hw'⟩ := Finset.not_disjoint_iff.1 hv
  have step : ∀ x y, x ∈ γ'.verts → s(x, y) ∈ γ.edges → s(x, y) ∈ γ'.edges := by
    intro x y hx hxy
    have hx' : x ∈ γ.verts := cs_anyCyc_mem_verts hxy (Sym2.mem_mk_left _ _)
    have hmem : s(x, y) ∈ γ.edges.filter (fun e => x ∈ e) :=
      Finset.mem_filter.2 ⟨hxy, Sym2.mem_mk_left _ _⟩
    rw [cs_anyCyc_filter_eq hγ hγ' hS hx' hx] at hmem
    exact (Finset.mem_filter.1 hmem).1
  obtain ⟨j, c, rfl⟩ := cs_anyCyc_exists_rep γ
  obtain ⟨a, rfl⟩ := (cs_mem_edgeVerts c w).1 hw
  have key : ∀ n : ℕ, c.1 (a + n) ∈ γ'.verts := by
    intro n
    induction n with
    | zero => simpa using hw'
    | succ n ih =>
      have h1 := step _ _ ih (cs_mk_mem_edges c (a + n))
      have h2 := cs_anyCyc_mem_verts h1 (Sym2.mem_mk_right _ _)
      rw [Nat.cast_succ, ← add_assoc]
      exact h2
  have hall : ∀ i, c.1 i ∈ γ'.verts := by
    intro i
    have h1 := key (i - a).val
    have h2 : a + (((i - a).val : ℕ) : ZMod (j + 3)) = i := by
      rw [ZMod.natCast_zmod_val]
      ring
    rwa [h2] at h1
  intro e he
  rw [cs_anyCyc_edges_mk] at he
  obtain ⟨i, rfl⟩ := cs_mem_edges.1 he
  exact step _ _ (hall i) he

omit [Fintype V] in
/-- The walking lemma for sequences of the same length: if the edges of `c'` are edges of `c`,
then `c'` is a rotation or a reflection of `c`. -/
private theorem cs_rel_of_edges_subset {j : ℕ} {c c' : CycSeq V j} (h : c'.edges ⊆ c.edges) :
    CycSeq.Rel c c' := by
  obtain ⟨i₀, hi₀⟩ := cs_mem_edges.1 (h (cs_mk_mem_edges c' 0))
  obtain ⟨a, ε, hε, h0, h1⟩ : ∃ a ε : ZMod (j + 3), (ε = 1 ∨ ε = -1) ∧
      c'.1 0 = c.1 a ∧ c'.1 1 = c.1 (a + ε) := by
    rw [zero_add] at hi₀
    rcases Sym2.eq_iff.1 hi₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨i₀, 1, Or.inl rfl, h1.symm, h2.symm⟩
    · refine ⟨i₀ + 1, -1, Or.inr rfl, h2.symm, ?_⟩
      rw [← h1]
      exact cs_congr c (by ring)
  have key : ∀ n : ℕ, c'.1 n = c.1 (a + ε * n) ∧
      c'.1 ((n : ZMod (j + 3)) + 1) = c.1 (a + ε * ((n : ZMod (j + 3)) + 1)) := by
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero, mul_zero, add_zero, zero_add, mul_one]
      exact ⟨h0, h1⟩
    | succ n ih =>
      push_cast
      refine ⟨ih.2, ?_⟩
      have hmem : s(c.1 (a + ε * ((n : ZMod (j + 3)) + 1)),
          c'.1 ((n : ZMod (j + 3)) + 1 + 1)) ∈ c.edges := by
        rw [← ih.2]
        exact h (cs_mk_mem_edges c' _)
      have hne : c'.1 ((n : ZMod (j + 3)) + 1 + 1) ≠ c'.1 n := by
        intro h'
        have h'' := c'.2 h'
        apply cs_zmod_two_ne_zero j
        linear_combination h''
      rw [ih.1] at hne
      rcases (cs_mk_mem_edges_iff c _ _).1 hmem with h2 | h2 <;>
        rcases hε with rfl | rfl
      · rw [h2]; exact cs_congr c (by ring)
      · exfalso; apply hne; rw [h2]; exact cs_congr c (by ring)
      · exfalso; apply hne; rw [h2]; exact cs_congr c (by ring)
      · rw [h2]; exact cs_congr c (by ring)
  refine ⟨a, ?_⟩
  have hall : ∀ i : ZMod (j + 3), c'.1 i = c.1 (a + ε * i) := by
    intro i
    have := (key i.val).1
    rwa [ZMod.natCast_zmod_val] at this
  rcases hε with rfl | rfl
  · exact Or.inl fun i => by rw [hall, one_mul]
  · exact Or.inr fun i => by rw [hall]; exact cs_congr c (by ring)

/-- A cycle is determined by its edge set, and no cycle's edges are a proper subset of
another cycle's edges. -/
theorem AnyCyc.eq_of_edges_subset {γ γ' : AnyCyc V} (h : γ.edges ⊆ γ'.edges) : γ = γ' := by
  have hdeg : ∀ v, edgeDeg γ'.edges v ≤ 2 := by
    intro v
    by_cases hv : v ∈ γ'.verts
    · rw [γ'.edgeDeg_eq_two hv]
    · rw [cs_edgeDeg_eq_zero hv]
      omega
  have hne : γ.edges.Nonempty := by
    rw [← Finset.card_pos, γ.card_edges]
    omega
  obtain ⟨e, he⟩ := hne
  obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨_, Sym2.out_fst_mem e⟩
  have hdis : ¬ Disjoint γ'.verts γ.verts := Finset.not_disjoint_iff.2
    ⟨v, cs_anyCyc_mem_verts (h he) hv, cs_anyCyc_mem_verts he hv⟩
  have h' : γ'.edges ⊆ γ.edges := cs_anyCyc_edges_subset (Finset.Subset.refl _) h hdeg hdis
  obtain ⟨j, c, rfl⟩ := cs_anyCyc_exists_rep γ
  obtain ⟨j', c', rfl⟩ := cs_anyCyc_exists_rep γ'
  rw [cs_anyCyc_edges_mk, cs_anyCyc_edges_mk] at h h'
  have hj : j = j' := by
    have h1 := Finset.card_le_card h
    have h2 := Finset.card_le_card h'
    rw [cs_edges_card, cs_edges_card] at h1 h2
    omega
  subst hj
  exact congrArg (Sigma.mk j) (Quotient.sound (cs_rel_of_edges_subset h'))

/-- In an edge set of maximum degree `2`, a cycle sharing a vertex with another cycle is
contained in it. -/
theorem AnyCyc.edges_subset_of_edgeDeg_le_two {γ γ' : AnyCyc V} {S : Finset (Sym2 V)}
    (hγ : γ.edges ⊆ S) (hγ' : γ'.edges ⊆ S) (hS : ∀ v, edgeDeg S v ≤ 2)
    (hv : ¬ Disjoint γ.verts γ'.verts) : γ.edges ⊆ γ'.edges :=
  cs_anyCyc_edges_subset hγ hγ' hS hv

/-- Handshake lemma for loopless edge sets. -/
theorem sum_edgeDeg (S : Finset (Sym2 V)) (hdiag : ∀ e ∈ S, ¬ e.IsDiag) :
    ∑ v, edgeDeg S v = 2 * S.card := by
  have h1 : ∀ v, edgeDeg S v = ∑ e ∈ S, if v ∈ e then 1 else 0 := fun v => by
    rw [edgeDeg, Finset.card_filter]
  have h2 : ∀ e ∈ S, (∑ v : V, if v ∈ e then 1 else 0) = 2 := by
    intro e he
    rw [← Finset.card_filter]
    have : Finset.univ.filter (fun v => v ∈ e) = e.toFinset := by
      ext v
      simp [Sym2.mem_toFinset]
    rw [this, Sym2.card_toFinset_of_not_isDiag e (hdiag e he)]
  simp_rw [h1]
  rw [Finset.sum_comm, Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]

/-! ### Finding a cycle in a 2-regular edge set -/

/-- The next vertex of a non-backtracking walk: a neighbour of `x` in `S` other than `y`. -/
private def cs_nxt {V : Type*} (S : Finset (Sym2 V)) (y x : V) : V :=
  if h : ∃ z, z ≠ y ∧ s(x, z) ∈ S then h.choose else y

/-- The non-backtracking walk `v₀ = u`, `v₁ = w`, `v_{n+2} = nxt v_n v_{n+1}`. -/
private def cs_walk {V : Type*} (nxt : V → V → V) (u w : V) : ℕ → V
  | 0 => u
  | 1 => w
  | n + 2 => nxt (cs_walk nxt u w n) (cs_walk nxt u w (n + 1))

private theorem cs_walk_add_two {V : Type*} (nxt : V → V → V) (u w : V) (n : ℕ) :
    cs_walk nxt u w (n + 2) = nxt (cs_walk nxt u w n) (cs_walk nxt u w (n + 1)) := by
  rw [cs_walk]

private theorem cs_exists_next {S : Finset (Sym2 V)} (hS : ∀ v ∈ edgeVerts S, edgeDeg S v = 2)
    {x y : V} (h : s(y, x) ∈ S) : ∃ z, z ≠ y ∧ s(x, z) ∈ S := by
  have hx : x ∈ edgeVerts S := cs_mem_edgeVerts_iff.2 ⟨_, h, Sym2.mem_mk_right _ _⟩
  have h2 := hS x hx
  obtain ⟨e, he, hne⟩ := Finset.exists_mem_ne (s := S.filter fun e => x ∈ e)
    (by show 1 < edgeDeg S x; rw [h2]; norm_num) s(y, x)
  rw [Finset.mem_filter] at he
  obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.1 he.2
  refine ⟨z, ?_, he.1⟩
  rintro rfl
  exact hne Sym2.eq_swap

private theorem cs_nxt_spec {S : Finset (Sym2 V)} (hS : ∀ v ∈ edgeVerts S, edgeDeg S v = 2)
    {x y : V} (h : s(y, x) ∈ S) : cs_nxt S y x ≠ y ∧ s(x, cs_nxt S y x) ∈ S := by
  have hex := cs_exists_next hS h
  unfold cs_nxt
  rw [dif_pos hex]
  exact hex.choose_spec

/-- A nonempty loopless edge set in which every touched vertex has degree `2` contains the
edges of a cycle. -/
private theorem cs_exists_cyc_subset {S : Finset (Sym2 V)} (hdiag : ∀ e ∈ S, ¬ e.IsDiag)
    (hS : ∀ v ∈ edgeVerts S, edgeDeg S v = 2) (hne : S.Nonempty) :
    ∃ γ : AnyCyc V, γ.edges ⊆ S := by
  obtain ⟨e₀, he₀⟩ := hne
  obtain ⟨u, w, huw⟩ := (Sym2.exists (f := fun e => e ∈ S)).1 ⟨e₀, he₀⟩
  set v := cs_walk (cs_nxt S) u w with hv_def
  have hv2 : ∀ n, v (n + 2) = cs_nxt S (v n) (v (n + 1)) := fun n => cs_walk_add_two _ _ _ n
  have hedge : ∀ n, s(v n, v (n + 1)) ∈ S := by
    intro n
    induction n with
    | zero => exact huw
    | succ n ih =>
      rw [show n + 1 + 1 = n + 2 from rfl, hv2]
      exact (cs_nxt_spec hS ih).2
  have hback : ∀ n, v (n + 2) ≠ v n := fun n => by
    rw [hv2]
    exact (cs_nxt_spec hS (hedge n)).1
  have hloop : ∀ n, v (n + 1) ≠ v n := fun n h =>
    hdiag _ (hedge n) (Sym2.mk_isDiag_iff.2 h.symm)
  have hP : ∃ J, ∃ I < J, v I = v J := by
    obtain ⟨x, y, hxy, hxy'⟩ := Finite.exists_ne_map_eq_of_infinite v
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨y, x, h, hxy'⟩
    · exact ⟨x, y, h, hxy'.symm⟩
  obtain ⟨I, hIJ, hIv⟩ := Nat.find_spec hP
  set J := Nat.find hP with hJ
  have hinj : ∀ a b, a < J → b < J → v a = v b → a = b := by
    intro a b ha hb hab
    rcases lt_trichotomy a b with h | h | h
    · exact (Nat.find_min hP hb ⟨a, h, hab⟩).elim
    · exact h
    · exact (Nat.find_min hP ha ⟨b, h, hab.symm⟩).elim
  have hlen : I + 3 ≤ J := by
    by_contra hcon
    have : J = I + 1 ∨ J = I + 2 := by omega
    rcases this with h | h
    · exact hloop I (by rw [← h]; exact hIv.symm)
    · exact hback I (by rw [← h]; exact hIv.symm)
  obtain ⟨m, hm⟩ : ∃ m, J = I + (m + 3) := ⟨J - I - 3, by omega⟩
  let c : ZMod (m + 3) → V := fun k => v (I + k.val)
  have hc : Function.Injective c := by
    intro k k' h
    apply ZMod.val_injective
    have hk := ZMod.val_lt k
    have hk' := ZMod.val_lt k'
    have := hinj (I + k.val) (I + k'.val) (by omega) (by omega) h
    omega
  let cs : CycSeq V m := ⟨c, hc⟩
  refine ⟨⟨m, Quotient.mk _ cs⟩, ?_⟩
  intro e he
  rw [cs_anyCyc_edges_mk] at he
  obtain ⟨k, rfl⟩ := cs_mem_edges.1 he
  have hk1 : (k + 1).val = (k.val + 1) % (m + 3) := by
    have : k + 1 = ((k.val + 1 : ℕ) : ZMod (m + 3)) := by
      rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
    rw [this, ZMod.val_natCast]
  have hk := ZMod.val_lt k
  show s(v (I + k.val), v (I + (k + 1).val)) ∈ S
  rcases Nat.lt_or_ge (k.val + 1) (m + 3) with hlt | hge
  · rw [hk1, Nat.mod_eq_of_lt hlt, ← add_assoc]
    exact hedge _
  · have hkv : k.val + 1 = m + 3 := by omega
    rw [hk1, hkv, Nat.mod_self, add_zero, hIv]
    have : I + k.val + 1 = J := by omega
    rw [← this]
    exact hedge _

/-- A loopless edge set in which every touched vertex has degree exactly `2` is a union of
pairwise vertex-disjoint cycles. -/
theorem exists_cycle_decomp (S : Finset (Sym2 V)) (hdiag : ∀ e ∈ S, ¬ e.IsDiag)
    (hS : ∀ v ∈ edgeVerts S, edgeDeg S v = 2) :
    ∃ Γ : Finset (AnyCyc V), (Γ : Set (AnyCyc V)).PairwiseDisjoint AnyCyc.verts ∧
      Γ.biUnion AnyCyc.edges = S := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, by simp, by simp⟩
  obtain ⟨γ, hγ⟩ := cs_exists_cyc_subset hdiag hS hne
  have hγne : γ.edges.Nonempty := by
    rw [← Finset.card_pos, γ.card_edges]
    omega
  have hout : ∀ v ∈ edgeVerts (S \ γ.edges), v ∉ γ.verts := by
    intro v hv hvγ
    obtain ⟨e, he, hve⟩ := cs_mem_edgeVerts_iff.1 hv
    rw [Finset.mem_sdiff] at he
    have hvS : v ∈ edgeVerts S := cs_mem_edgeVerts_iff.2 ⟨e, he.1, hve⟩
    have heq : γ.edges.filter (fun e => v ∈ e) = S.filter (fun e => v ∈ e) := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset_filter _ hγ)
      have h1 := hS v hvS
      have h2 := γ.edgeDeg_eq_two hvγ
      unfold edgeDeg at h1 h2
      omega
    have hmem : e ∈ S.filter (fun e => v ∈ e) := Finset.mem_filter.2 ⟨he.1, hve⟩
    rw [← heq] at hmem
    exact he.2 (Finset.mem_filter.1 hmem).1
  have hS' : ∀ v ∈ edgeVerts (S \ γ.edges), edgeDeg (S \ γ.edges) v = 2 := by
    intro v hv
    have hvγ := hout v hv
    have hvS : v ∈ edgeVerts S := cs_edgeVerts_mono Finset.sdiff_subset hv
    rw [← hS v hvS, edgeDeg, edgeDeg]
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨he, -⟩, hve⟩
      exact ⟨he, hve⟩
    · rintro ⟨he, hve⟩
      exact ⟨⟨he, fun heγ => hvγ (cs_anyCyc_mem_verts heγ hve)⟩, hve⟩
  have hlt : (S \ γ.edges).card < n := by
    rw [← hn]
    exact Finset.card_lt_card (Finset.sdiff_ssubset hγ hγne)
  obtain ⟨Γ', hΓ'd, hΓ'u⟩ := ih _ hlt (S \ γ.edges)
    (fun e he => hdiag e (Finset.sdiff_subset he)) hS' rfl
  refine ⟨insert γ Γ', ?_, ?_⟩
  · rw [Finset.coe_insert]
    refine hΓ'd.insert fun γ'' hγ'' _ => ?_
    rw [Finset.disjoint_left]
    intro v hv hv''
    apply hout v _ hv
    have hsub : γ''.edges ⊆ S \ γ.edges := by
      rw [← hΓ'u]
      exact Finset.subset_biUnion_of_mem _ hγ''
    exact cs_edgeVerts_mono hsub hv''
  · rw [Finset.biUnion_insert, hΓ'u, Finset.union_sdiff_of_subset hγ]

/-- The union of the edges of pairwise vertex-disjoint cycles has maximum degree `2`. -/
private theorem cs_edgeDeg_biUnion_le_two {Γ : Finset (AnyCyc V)}
    (hΓ : (Γ : Set (AnyCyc V)).PairwiseDisjoint AnyCyc.verts) (v : V) :
    edgeDeg (Γ.biUnion AnyCyc.edges) v ≤ 2 := by
  by_cases h : ∃ γ ∈ Γ, v ∈ γ.verts
  · obtain ⟨γ, hγ, hv⟩ := h
    rw [← γ.edgeDeg_eq_two hv]
    apply Finset.card_le_card
    intro e he
    rw [Finset.mem_filter, Finset.mem_biUnion] at he
    obtain ⟨⟨γ', hγ', he'⟩, hve⟩ := he
    have hv' : v ∈ γ'.verts := cs_anyCyc_mem_verts he' hve
    have : γ' = γ := by
      by_contra hne
      exact Finset.disjoint_left.1 (hΓ hγ' hγ hne) hv' hv
    subst this
    exact Finset.mem_filter.2 ⟨he', hve⟩
  · push Not at h
    rw [cs_edgeDeg_eq_zero]
    · omega
    · intro hv
      obtain ⟨e, he, hve⟩ := cs_mem_edgeVerts_iff.1 hv
      obtain ⟨γ, hγ, he⟩ := Finset.mem_biUnion.1 he
      exact h γ hγ (cs_anyCyc_mem_verts he hve)

/-- The decomposition into pairwise vertex-disjoint cycles is unique. -/
theorem eq_of_biUnion_edges_eq {Γ Γ' : Finset (AnyCyc V)}
    (hΓ : (Γ : Set (AnyCyc V)).PairwiseDisjoint AnyCyc.verts)
    (hΓ' : (Γ' : Set (AnyCyc V)).PairwiseDisjoint AnyCyc.verts)
    (h : Γ.biUnion AnyCyc.edges = Γ'.biUnion AnyCyc.edges) : Γ = Γ' := by
  have key : ∀ {Γ Γ' : Finset (AnyCyc V)}, (Γ : Set (AnyCyc V)).PairwiseDisjoint AnyCyc.verts →
      Γ.biUnion AnyCyc.edges = Γ'.biUnion AnyCyc.edges → Γ ⊆ Γ' := by
    intro Γ Γ' hΓ h γ hγ
    obtain ⟨e, he⟩ : γ.edges.Nonempty := by
      rw [← Finset.card_pos, γ.card_edges]
      omega
    have he' : e ∈ Γ'.biUnion AnyCyc.edges := by
      rw [← h]
      exact Finset.mem_biUnion.2 ⟨γ, hγ, he⟩
    obtain ⟨γ', hγ', he'⟩ := Finset.mem_biUnion.1 he'
    obtain ⟨v, hv⟩ : ∃ v, v ∈ e := ⟨_, Sym2.out_fst_mem e⟩
    have hsub' : γ'.edges ⊆ Γ.biUnion AnyCyc.edges := by
      rw [h]
      exact Finset.subset_biUnion_of_mem _ hγ'
    have hsub := cs_anyCyc_edges_subset (Finset.subset_biUnion_of_mem _ hγ) hsub'
      (cs_edgeDeg_biUnion_le_two hΓ)
      (Finset.not_disjoint_iff.2 ⟨v, cs_anyCyc_mem_verts he hv, cs_anyCyc_mem_verts he' hv⟩)
    rw [AnyCyc.eq_of_edges_subset hsub]
    exact hγ'
  exact Finset.Subset.antisymm (key hΓ h) (key hΓ' h.symm)

/-- Distinct cycles that are not pairwise vertex-disjoint span more edges than vertices. -/
theorem card_edgeVerts_lt_of_not_pairwiseDisjoint (Γ : Finset (AnyCyc V))
    (h : ¬ (Γ : Set (AnyCyc V)).PairwiseDisjoint AnyCyc.verts) :
    (edgeVerts (Γ.biUnion AnyCyc.edges)).card < (Γ.biUnion AnyCyc.edges).card := by
  set H := Γ.biUnion AnyCyc.edges with hH
  have hdiag : ∀ e ∈ H, ¬ e.IsDiag := by
    intro e he
    obtain ⟨γ, -, he⟩ := Finset.mem_biUnion.1 he
    exact γ.not_isDiag he
  have hge : ∀ v ∈ edgeVerts H, 2 ≤ edgeDeg H v := by
    intro v hv
    obtain ⟨e, he, hve⟩ := cs_mem_edgeVerts_iff.1 hv
    obtain ⟨γ, hγ, he⟩ := Finset.mem_biUnion.1 he
    rw [← γ.edgeDeg_eq_two (cs_anyCyc_mem_verts he hve)]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_biUnion_of_mem _ hγ))
  by_contra hcon
  push Not at hcon
  have hsum : ∑ v ∈ edgeVerts H, edgeDeg H v = 2 * H.card := by
    rw [← sum_edgeDeg H hdiag]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    exact cs_edgeDeg_eq_zero hv
  have heq2 : ∀ v ∈ edgeVerts H, edgeDeg H v = 2 := by
    have hle : ∑ v ∈ edgeVerts H, edgeDeg H v ≤ ∑ v ∈ edgeVerts H, 2 := by
      rw [hsum, Finset.sum_const, smul_eq_mul]
      omega
    have := (Finset.sum_eq_sum_iff_of_le hge).1 (le_antisymm (Finset.sum_le_sum hge) hle)
    intro v hv
    exact (this v hv).symm
  have hdeg : ∀ v, edgeDeg H v ≤ 2 := by
    intro v
    by_cases hv : v ∈ edgeVerts H
    · rw [heq2 v hv]
    · rw [cs_edgeDeg_eq_zero hv]
      omega
  rw [Set.PairwiseDisjoint, Set.Pairwise] at h
  push Not at h
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hne, hnd⟩ := h
  apply hne
  apply AnyCyc.eq_of_edges_subset
  exact cs_anyCyc_edges_subset (Finset.subset_biUnion_of_mem _ hγ₁)
    (Finset.subset_biUnion_of_mem _ hγ₂) hdeg hnd

/-- Each `(j+3)`-cycle is represented by exactly `2(j+3)` cyclic sequences. -/
theorem card_fiber_mk (j : ℕ) (γ : Cyc V j) :
    (Finset.univ.filter fun c : CycSeq V j => (Quotient.mk _ c : Cyc V j) = γ).card =
      2 * (j + 3) := by
  obtain ⟨c₀, rfl⟩ := Quotient.exists_rep γ
  let rot : ZMod (j + 3) → CycSeq V j := fun a =>
    ⟨fun i => c₀.1 (a + i), c₀.2.comp (add_right_injective a)⟩
  let refl : ZMod (j + 3) → CycSeq V j := fun a =>
    ⟨fun i => c₀.1 (a - i), c₀.2.comp (sub_right_injective)⟩
  have hrot : Function.Injective rot := by
    intro a b h
    have h0 := congrArg (fun c : CycSeq V j => c.1 0) h
    simp only [rot, add_zero] at h0
    exact c₀.2 h0
  have hrefl : Function.Injective refl := by
    intro a b h
    have h0 := congrArg (fun c : CycSeq V j => c.1 0) h
    simp only [refl, sub_zero] at h0
    exact c₀.2 h0
  have hdis : ∀ a b, rot a ≠ refl b := by
    intro a b h
    have h0 := congrArg (fun c : CycSeq V j => c.1 0) h
    have h1 := congrArg (fun c : CycSeq V j => c.1 1) h
    simp only [rot, refl, add_zero, sub_zero] at h0 h1
    have e0 := c₀.2 h0
    have e1 := c₀.2 h1
    apply cs_zmod_two_ne_zero j
    linear_combination e1 - e0
  have hcard : (Finset.univ.image (Sum.elim rot refl)).card = 2 * (j + 3) := by
    rw [Finset.card_image_of_injective _ (hrot.sumElim hrefl hdis), Finset.card_univ,
      Fintype.card_sum, ZMod.card]
    ring
  rw [← hcard]
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  rw [Quotient.eq]
  constructor
  · intro hc
    obtain ⟨a, ha | ha⟩ := (CycSeq.rel_equivalence j).symm hc
    · exact ⟨Sum.inl a, Subtype.ext (funext fun i => (ha i).symm)⟩
    · exact ⟨Sum.inr a, Subtype.ext (funext fun i => (ha i).symm)⟩
  · rintro ⟨x, rfl⟩
    cases x with
    | inl a => exact (CycSeq.rel_equivalence j).symm ⟨a, Or.inl fun i => rfl⟩
    | inr a => exact (CycSeq.rel_equivalence j).symm ⟨a, Or.inr fun i => rfl⟩

end

end ERZeroFreeness
