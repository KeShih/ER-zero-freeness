/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.CountSignedPoly
import ERZeroFreeness.CountMobius

/-! # Lemma 8.1: local decomposition

`local_decomposition` (`lem:local-decomposition`): for every finite graph `G` with edge signs and
every `j ≥ 1`, `ℓ_j(G) = ∑ ω_j(G[S])` over the vertex sets `S` with `1 ≤ |S| ≤ 2j` and `G[S]`
connected.  Along the way: `ω_j(H) = 0` if `H` is disconnected
(`omegaCoeff_eq_zero_of_not_connected`) or if `|V(H)| > 2j` (`omegaCoeff_eq_zero_of_card_lt`).

## Proof

Write `f_H(T) = logCoeff (signedPoly (spanInduce H T) q J) j` (`T : Finset V`).
Bridges: `signedPoly_induce_eq` is `Count.signedPoly_comap` for `Function.Embedding.subtype`
(`(spanInduce H T).comap val = H.induce T`); then `ω_j(H) = μf_H(univ)` and, for the induced
graph `G[S]` (a graph on `↥S`, whose induced subgraphs live on double subtypes),
`ω_j(G[S]) = μf_G(S)` (reindex `Finset ↥S ≃ S.powerset` by `Finset.map (Embedding.subtype _)`;
termwise, apply `Count.signedPoly_comap` with `ι_S` to `spanInduce G (T'.map ι_S)`, whose
pull-back is `spanInduce (G[S]) T'`).
Support bound: `T ↦ a_i(H[T])` is `2i`-local (`Count.signedPoly_coeff`,
`Count.edgeFinset_spanInduce`; group the `F` by `edgeVerts F`, and `|edgeVerts F| ≤ 2|F|`);
`T ↦ ℓ_j(H[T])` is `2j`-local by strong induction on `j` through `logCoeff_eq`
(`MobiusLocal.mul` with `2r + 2(j-r) = 2j`).
Disconnected graphs: pick `u, v` not reachable from each other, let `A` be the set of vertices
reachable from `u` and `B = Aᶜ`; for every `T`, `f(T) = f(T ∩ A) + f(T ∩ B)`
(`logCoeff_spanInduce_union`), and `vtxMobius_eq_zero_of_insert` with `b = v` (resp. `b = u`)
kills both parts; the empty vertex type is the case `f(∅) = logCoeff 1 j = 0`
(`Count.signedPoly_eq_one`, `logCoeff_one`).
Lemma 8.1: `ℓ_j(G) = f_G(univ) = ∑_S μf_G(S) = ∑_S ω_j(G[S])`; drop the vanishing terms.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

section CountLocal

variable {V : Type*} [Fintype V]

/-- `G[V(G)] = G`. -/
theorem spanInduce_univ (H : SimpleGraph V) : spanInduce H Finset.univ = H := by
  ext u v; simp [spanInduce]

/-- `H[T]` (on the subtype `T`) and `spanInduce H T` (on `V`) have the same
polynomial. -/
theorem signedPoly_induce_eq {q : ℕ} (hq : 1 ≤ q) (H : SimpleGraph V) (J : Sym2 V → ℤ)
    (T : Finset V) :
    signedPoly (H.induce (T : Set V)) q (fun e => J (e.map Subtype.val)) =
      signedPoly (spanInduce H T) q J := by
  have h := Count.signedPoly_comap hq (Function.Embedding.subtype (· ∈ (T : Set V)))
    (spanInduce H T) J (fun u v huv => ⟨⟨⟨u, huv.2.1⟩, rfl⟩, ⟨⟨v, huv.2.2⟩, rfl⟩⟩)
  rw [← h]
  congr 1
  ext u v
  simp [spanInduce]

private lemma CountLocal_mem_edgeVerts {F : Finset (Sym2 V)} {v : V} :
    v ∈ edgeVerts F ↔ ∃ e ∈ F, v ∈ e := by
  simp [edgeVerts]

/-- `|edgeVerts F| ≤ 2|F|`: every edge has at most two endpoints. -/
private lemma CountLocal_card_edgeVerts_le (F : Finset (Sym2 V)) :
    (edgeVerts F).card ≤ 2 * F.card := by
  have hsub : edgeVerts F ⊆ F.biUnion (fun e => e.toFinset) := by
    intro v hv
    obtain ⟨e, he, hve⟩ := CountLocal_mem_edgeVerts.mp hv
    exact Finset.mem_biUnion.mpr ⟨e, he, Sym2.mem_toFinset.mpr hve⟩
  have hle : ∀ e ∈ F, e.toFinset.card ≤ 2 := by
    intro e _
    rw [Sym2.card_toFinset]
    split_ifs <;> omega
  calc (edgeVerts F).card ≤ (F.biUnion (fun e => e.toFinset)).card := Finset.card_le_card hsub
    _ ≤ ∑ e ∈ F, e.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ F, 2 := Finset.sum_le_sum hle
    _ = 2 * F.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- "The degree-`i` terms involve at most `i` edges, so they touch at most `2i`
vertices": `T ↦ a_i(H[T])` is `2i`-local. -/
theorem mobiusLocal_coeff_spanInduce (H : SimpleGraph V) (q : ℕ) (J : Sym2 V → ℤ) (i : ℕ) :
    MobiusLocal (2 * i) (fun T => (signedPoly (spanInduce H T) q J).coeff i) := by
  refine ⟨fun U => ∑ F ∈ (H.edgeFinset.powersetCard i).filter (fun F => edgeVerts F = U),
    signedEdgeWeight q J F, ?_, ?_⟩
  · intro U hU
    refine Finset.sum_eq_zero fun F hF => ?_
    exfalso
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hF
    have h2 := CountLocal_card_edgeVerts_le F
    rw [hF.2, hF.1.2] at h2
    omega
  · intro T
    dsimp only
    rw [Count.signedPoly_coeff, Count.edgeFinset_spanInduce]
    have hmaps : ∀ F ∈ (H.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ T).powersetCard i,
        edgeVerts F ∈ T.powerset := by
      intro F hF
      rw [Finset.mem_powersetCard] at hF
      rw [Finset.mem_powerset]
      intro v hv
      obtain ⟨e, he, hve⟩ := CountLocal_mem_edgeVerts.mp hv
      exact (Finset.mem_filter.mp (hF.1 he)).2 v hve
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun U hU => ?_
    rw [Finset.mem_powerset] at hU
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext F
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hF, hc⟩, hU'⟩
      exact ⟨⟨hF.trans (Finset.filter_subset _ _), hc⟩, hU'⟩
    · rintro ⟨⟨hF, hc⟩, hU'⟩
      refine ⟨⟨fun e he => Finset.mem_filter.mpr ⟨hF he, fun v hv => hU ?_⟩, hc⟩, hU'⟩
      rw [← hU']
      exact CountLocal_mem_edgeVerts.mpr ⟨e, he, hv⟩

/-- `T ↦ ℓ_j(H[T])` is `2j`-local. -/
theorem mobiusLocal_logCoeff_spanInduce (H : SimpleGraph V) (q : ℕ) (J : Sym2 V → ℤ) (j : ℕ) :
    MobiusLocal (2 * j) (fun T => logCoeff (signedPoly (spanInduce H T) q J) j) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp only [logCoeff_zero]
      exact mobiusLocal_const _ 0
    · have hfun : (fun T => logCoeff (signedPoly (spanInduce H T) q J) j) = fun T =>
          (signedPoly (spanInduce H T) q J).coeff j + (-(1 / (j : ℂ))) *
            ∑ r ∈ Finset.Ico 1 j, (r : ℂ) * logCoeff (signedPoly (spanInduce H T) q J) r *
              (signedPoly (spanInduce H T) q J).coeff (j - r) := by
        funext T
        rw [logCoeff_eq _ hj]
        ring
      rw [hfun]
      refine (mobiusLocal_coeff_spanInduce H q J j).add (MobiusLocal.const_mul ?_ _)
      refine MobiusLocal.sum _ fun r hr => ?_
      rw [Finset.mem_Ico] at hr
      have h1 := ((ih r hr.2).const_mul (r : ℂ)).mul (mobiusLocal_coeff_spanInduce H q J (j - r))
      exact h1.mono (by omega)

/-- Additivity of `ℓ_j` over two parts with no edge between them. -/
theorem logCoeff_spanInduce_union {q : ℕ} (hq : 1 ≤ q) (H : SimpleGraph V) (J : Sym2 V → ℤ)
    (j : ℕ) {A B : Finset V} (hAB : Disjoint A B) (hno : ∀ a ∈ A, ∀ b ∈ B, ¬ H.Adj a b) :
    logCoeff (signedPoly (spanInduce H (A ∪ B)) q J) j =
      logCoeff (signedPoly (spanInduce H A) q J) j +
        logCoeff (signedPoly (spanInduce H B) q J) j := by
  rw [Count.signedPoly_spanInduce_union hq H J hAB hno]
  exact logCoeff_mul (Count.signedPoly_coeff_zero hq _ J) (Count.signedPoly_coeff_zero hq _ J) j

/-- `ω_j(H) = μf_H(V)`. -/
theorem omegaCoeff_eq_vtxMobius {q : ℕ} (hq : 1 ≤ q) (H : SimpleGraph V) (J : Sym2 V → ℤ)
    (j : ℕ) :
    omegaCoeff H q J j =
      vtxMobius (fun T => logCoeff (signedPoly (spanInduce H T) q J) j) Finset.univ := by
  unfold omegaCoeff vtxMobius
  rw [Finset.powerset_univ, Finset.card_univ]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [ellCoeff, signedPoly_induce_eq hq H J T]

/-- The termwise step of `omegaCoeff_induce_eq_vtxMobius`: `(G[S])[T'] = G[T']` for `T' ⊆ S`,
at the level of polynomials (spanning forms, double subtype). -/
private lemma CountLocal_signedPoly_spanInduce_induce {q : ℕ} (hq : 1 ≤ q) (G : SimpleGraph V)
    (J : Sym2 V → ℤ) (S : Finset V) (T' : Finset ↥(S : Set V)) :
    signedPoly (spanInduce (G.induce (S : Set V)) T') q (fun e => J (e.map Subtype.val)) =
      signedPoly (spanInduce G (T'.map (Function.Embedding.subtype (· ∈ (S : Set V))))) q J := by
  have h := Count.signedPoly_comap hq (Function.Embedding.subtype (· ∈ (S : Set V)))
    (spanInduce G (T'.map (Function.Embedding.subtype (· ∈ (S : Set V))))) J ?_
  · rw [← h]
    congr 1
    ext u v
    simp [spanInduce]
  · intro u v huv
    obtain ⟨_, hu, hv⟩ := huv
    rw [Finset.mem_map] at hu hv
    obtain ⟨u', _, rfl⟩ := hu
    obtain ⟨v', _, rfl⟩ := hv
    exact ⟨⟨u', rfl⟩, ⟨v', rfl⟩⟩

/-- `ω_j(G[S]) = μf_G(S)` (`(G[S])[T] = G[T]` for `T ⊆ S`). -/
theorem omegaCoeff_induce_eq_vtxMobius {q : ℕ} (hq : 1 ≤ q) (G : SimpleGraph V)
    (J : Sym2 V → ℤ) (j : ℕ) (S : Finset V) :
    omegaCoeff (G.induce (S : Set V)) q (fun e => J (e.map Subtype.val)) j =
      vtxMobius (fun T => logCoeff (signedPoly (spanInduce G T) q J) j) S := by
  rw [omegaCoeff_eq_vtxMobius hq]
  unfold vtxMobius
  rw [Finset.powerset_univ, Finset.card_univ]
  refine Finset.sum_nbij' (fun T' => T'.map (Function.Embedding.subtype (· ∈ (S : Set V))))
    (fun T => T.subtype (· ∈ (S : Set V))) ?_ ?_ ?_ ?_ ?_
  · intro T' _
    rw [Finset.mem_powerset]
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_coe.mp a.2
  · intro T _
    exact Finset.mem_univ _
  · intro T' _
    ext x
    simp
  · intro T hT
    rw [Finset.mem_powerset] at hT
    exact Finset.subtype_map_of_mem fun x hx => Finset.mem_coe.mpr (hT hx)
  · intro T' _
    dsimp only
    rw [CountLocal_signedPoly_spanInduce_induce hq G J S T', Finset.card_map]
    congr 2
    simp

/-- "Multiplicativity of `P_{H,J}` over connected components makes `ω_j(H)` vanish on
disconnected graphs" (including the graph with no vertices). -/
theorem omegaCoeff_eq_zero_of_not_connected {q : ℕ} (hq : 1 ≤ q) (H : SimpleGraph V)
    (J : Sym2 V → ℤ) (j : ℕ) (hH : ¬ H.Connected) : omegaCoeff H q J j = 0 := by
  rw [omegaCoeff_eq_vtxMobius hq]
  set f : Finset V → ℂ := fun T => logCoeff (signedPoly (spanInduce H T) q J) j with hf
  rcases isEmpty_or_nonempty V with hV | hV
  · have hu : (Finset.univ : Finset V) = ∅ := Finset.univ_eq_empty
    rw [hu]
    unfold vtxMobius
    rw [Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, Nat.sub_self, pow_zero,
      one_mul, hf]
    have he : (spanInduce H ∅).edgeFinset = ∅ := by
      rw [Count.edgeFinset_spanInduce]
      refine Finset.filter_false_of_mem fun e _ h => ?_
      induction e using Sym2.ind with
      | _ a b => simpa using h a (Sym2.mem_mk_left a b)
    show logCoeff (signedPoly (spanInduce H ∅) q J) j = 0
    rw [Count.signedPoly_eq_one hq he J, logCoeff_one]
  · have hpre : ¬ H.Preconnected := fun hp => hH ⟨hp⟩
    obtain ⟨u, v, huv⟩ : ∃ u v, ¬ H.Reachable u v := by
      by_contra hcon
      push Not at hcon
      exact hpre hcon
    set A : Finset V := Finset.univ.filter (fun x => H.Reachable u x) with hA
    set B : Finset V := Finset.univ.filter (fun x => ¬ H.Reachable u x) with hB
    have hsplit : ∀ T : Finset V, f T = f (T ∩ A) + f (T ∩ B) := by
      intro T
      have hT : T ∩ A ∪ T ∩ B = T := by
        ext x
        simp only [hA, hB, Finset.mem_union, Finset.mem_inter, Finset.mem_filter,
          Finset.mem_univ, true_and]
        tauto
      have hdisj : Disjoint (T ∩ A) (T ∩ B) := by
        rw [Finset.disjoint_left]
        intro x hxA hxB
        simp only [hA, hB, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
          true_and] at hxA hxB
        exact hxB.2 hxA.2
      have hno : ∀ a ∈ T ∩ A, ∀ b ∈ T ∩ B, ¬ H.Adj a b := by
        intro a ha b hb hab
        simp only [hA, hB, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
          true_and] at ha hb
        exact hb.2 (ha.2.trans hab.reachable)
      have h := logCoeff_spanInduce_union hq H J j hdisj hno
      rw [hT] at h
      exact h
    rw [vtxMobius_congr (fun T _ => hsplit T),
      vtxMobius_add (fun T => f (T ∩ A)) (fun T => f (T ∩ B))]
    have h1 : vtxMobius (fun T => f (T ∩ A)) Finset.univ = 0 := by
      refine vtxMobius_eq_zero_of_insert (b := v) (Finset.mem_univ v) fun T _ => ?_
      have hvA : v ∉ A := by simp [hA, huv]
      show f (insert v T ∩ A) = f (T ∩ A)
      rw [Finset.insert_inter_of_notMem hvA]
    have h2 : vtxMobius (fun T => f (T ∩ B)) Finset.univ = 0 := by
      refine vtxMobius_eq_zero_of_insert (b := u) (Finset.mem_univ u) fun T _ => ?_
      have huB : u ∉ B := by simp [hB]
      show f (insert u T ∩ B) = f (T ∩ B)
      rw [Finset.insert_inter_of_notMem huB]
    rw [h1, h2, add_zero]

/-- `ω_j(H) = 0` whenever `|V(H)| > 2j`. -/
theorem omegaCoeff_eq_zero_of_card_lt {q : ℕ} (hq : 1 ≤ q) (H : SimpleGraph V)
    (J : Sym2 V → ℤ) {j : ℕ} (hj : 2 * j < Fintype.card V) : omegaCoeff H q J j = 0 := by
  rw [omegaCoeff_eq_vtxMobius hq]
  exact (mobiusLocal_logCoeff_spanInduce H q J j).vtxMobius_eq_zero
    (by rw [Finset.card_univ]; exact hj)

/-- **Lemma 8.1 `lem:local-decomposition`.** For every finite graph `G` with edge signs
and every integer `j ≥ 1`,
`ℓ_j(G) = ∑_{S ⊆ V(G), 1 ≤ |S| ≤ 2j, G[S] connected} ω_j(G[S])`. -/
theorem local_decomposition {q : ℕ} (hq : 1 ≤ q) (G : SimpleGraph V) (J : Sym2 V → ℤ) {j : ℕ}
    (hj : 1 ≤ j) :
    ellCoeff G q J j =
      ∑ S ∈ Finset.univ.filter (fun S : Finset V =>
          1 ≤ S.card ∧ S.card ≤ 2 * j ∧ (G.induce (S : Set V)).Connected),
        omegaCoeff (G.induce (S : Set V)) q (fun e => J (e.map Subtype.val)) j := by
  -- The hypothesis `1 ≤ j` of the paper is not needed (for `j = 0` both sides vanish).
  set f : Finset V → ℂ := fun T => logCoeff (signedPoly (spanInduce G T) q J) j with hf
  have h1 : ellCoeff G q J j = f Finset.univ := by
    show ellCoeff G q J j = logCoeff (signedPoly (spanInduce G Finset.univ) q J) j
    rw [spanInduce_univ]
    rfl
  have h2 : ∀ S : Finset V,
      omegaCoeff (G.induce (S : Set V)) q (fun e => J (e.map Subtype.val)) j ≠ 0 →
        1 ≤ S.card ∧ S.card ≤ 2 * j ∧ (G.induce (S : Set V)).Connected := by
    intro S hS
    by_cases hc : (G.induce (S : Set V)).Connected
    · refine ⟨?_, ?_, hc⟩
      · obtain ⟨x⟩ := hc.nonempty
        exact Finset.card_pos.mpr ⟨x.1, x.2⟩
      · by_contra hlt
        apply hS
        apply omegaCoeff_eq_zero_of_card_lt hq
        simpa using (not_le.mp hlt)
    · exact absurd (omegaCoeff_eq_zero_of_not_connected hq _ _ j hc) hS
  rw [h1, ← sum_powerset_vtxMobius f Finset.univ, Finset.powerset_univ,
    Finset.sum_filter_of_ne (fun S _ hS => h2 S hS)]
  exact Finset.sum_congr rfl fun S _ => (omegaCoeff_induce_eq_vtxMobius hq G J j S).symm

end CountLocal

end

end ERZeroFreeness
