/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.CountDefs

/-! # `CountMobius`: subset Möbius inversion and locality (blueprint §6)

Proof.  Both inversion formulas are proved by induction on the set (`Finset.induction_on`,
generalizing the function), from the recursion (`a ∉ S`, `Finset.sum_powerset_insert`)
`μF(insert a S) = μ(F(insert a ·))(S) - μF(S)` (`CountMobius_insert`), together with
congruence and additivity of `μ` (private copies `CountMobius_congr`, `CountMobius_add` of
`vtxMobius_congr`, `vtxMobius_add`, which come later in the file).  `vtxMobius_eq_zero` from
`vtxMobius_sum_powerset`.  Closure: sum and scalar multiple of the `φ`'s; product:
`(∑_{U⊆T} φ U)(∑_{U'⊆T} ψ U') = ∑_{W⊆T} χ W` with `χ W = ∑_{U, U' ⊆ W, U ∪ U' = W} φ U ψ U'`
(`Finset.sum_fiberwise_of_maps_to`, `CountMobius_mul_aux`), and `|U ∪ U'| ≤ |U| + |U'|`.
`vtxMobius_eq_zero_of_insert`: `Finset.sum_powerset_insert` on `S = insert b (S.erase b)`; the
two halves cancel (from `docs/counting/scratch-proofs.lean`).
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

section CountMobius

variable {V : Type*}

/-- `μf(S)` only depends on `f` on the subsets of `S` (private copy of `vtxMobius_congr`, needed
before the frozen statement). -/
private lemma CountMobius_congr {f g : Finset V → ℂ} {S : Finset V} (h : ∀ T ⊆ S, f T = g T) :
    vtxMobius f S = vtxMobius g S := by
  unfold vtxMobius
  exact Finset.sum_congr rfl fun T hT => by rw [h T (Finset.mem_powerset.mp hT)]

/-- Additivity of `μ` (private copy of `vtxMobius_add`). -/
private lemma CountMobius_add (f g : Finset V → ℂ) (S : Finset V) :
    vtxMobius (fun T => f T + g T) S = vtxMobius f S + vtxMobius g S := by
  unfold vtxMobius
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun T _ => by ring

/-- The Möbius transform at `insert a S` (`a ∉ S`):
`μF(S ∪ {a}) = μ(F(· ∪ {a}))(S) - μF(S)`. -/
private lemma CountMobius_insert (F : Finset V → ℂ) {a : V} {S : Finset V} (ha : a ∉ S) :
    vtxMobius F (insert a S) = vtxMobius (fun T => F (insert a T)) S - vtxMobius F S := by
  unfold vtxMobius
  rw [Finset.sum_powerset_insert ha, Finset.card_insert_of_notMem ha]
  have h1 : ∀ T ∈ S.powerset, (-1 : ℂ) ^ (S.card + 1 - T.card) * F T =
      -((-1) ^ (S.card - T.card) * F T) := by
    intro T hT
    have hle : T.card ≤ S.card := Finset.card_le_card (Finset.mem_powerset.mp hT)
    rw [show S.card + 1 - T.card = (S.card - T.card) + 1 by omega, pow_succ]
    ring
  have h2 : ∀ T ∈ S.powerset, (-1 : ℂ) ^ (S.card + 1 - (insert a T).card) * F (insert a T) =
      (-1) ^ (S.card - T.card) * F (insert a T) := by
    intro T hT
    have haT : a ∉ T := fun h => ha (Finset.mem_powerset.mp hT h)
    rw [Finset.card_insert_of_notMem haT, Nat.add_sub_add_right]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_neg_distrib]
  ring

/-- [MO.1] Möbius inversion, first form: `μ(∑_{U ⊆ ·} φ U) = φ`. -/
theorem vtxMobius_sum_powerset (φ : Finset V → ℂ) (S : Finset V) :
    vtxMobius (fun T => ∑ U ∈ T.powerset, φ U) S = φ S := by
  induction S using Finset.induction_on generalizing φ with
  | empty => simp [vtxMobius]
  | insert a S ha ih =>
    rw [CountMobius_insert _ ha]
    have hc : vtxMobius (fun T => ∑ U ∈ (insert a T).powerset, φ U) S =
        vtxMobius (fun T => ∑ U ∈ T.powerset, φ U + ∑ U ∈ T.powerset, φ (insert a U)) S :=
      CountMobius_congr fun T hT => Finset.sum_powerset_insert (fun h => ha (hT h)) φ
    have ih' := ih (fun U => φ (insert a U))
    rw [hc, CountMobius_add, ih']
    ring

/-- [MO.2] Möbius inversion, second form: `f(T) = ∑_{U ⊆ T} (μf)(U)` (first step of the proof
of `lem:local-decomposition`). -/
theorem sum_powerset_vtxMobius (f : Finset V → ℂ) (T : Finset V) :
    ∑ U ∈ T.powerset, vtxMobius f U = f T := by
  induction T using Finset.induction_on generalizing f with
  | empty => simp [vtxMobius]
  | insert a T ha ih =>
    rw [Finset.sum_powerset_insert ha]
    have h2 : ∑ U ∈ T.powerset, vtxMobius f (insert a U) =
        ∑ U ∈ T.powerset, (vtxMobius (fun W => f (insert a W)) U - vtxMobius f U) :=
      Finset.sum_congr rfl fun U hU =>
        CountMobius_insert f (fun h => ha (Finset.mem_powerset.mp hU h))
    have ih' := ih (fun W => f (insert a W))
    rw [h2, Finset.sum_sub_distrib, ih f, ih']
    ring

/-- [MO.3] A `K`-local function has vanishing Möbius transform on sets of size `> K`. -/
theorem MobiusLocal.vtxMobius_eq_zero {K : ℕ} {f : Finset V → ℂ} (hf : MobiusLocal K f)
    {S : Finset V} (hS : K < S.card) : vtxMobius f S = 0 := by
  obtain ⟨φ, hφ0, hφ⟩ := hf
  rw [CountMobius_congr (g := fun T => ∑ U ∈ T.powerset, φ U) fun T _ => hφ T,
    vtxMobius_sum_powerset, hφ0 S hS]

/-- [MO.4] Constants are `K`-local. -/
theorem mobiusLocal_const (K : ℕ) (c : ℂ) : MobiusLocal K (fun _ : Finset V => c) := by
  refine ⟨fun U => if U = ∅ then c else 0, fun U hU => ?_, fun T => ?_⟩
  · have hU' : U ≠ ∅ := by
      rintro rfl
      simp at hU
    simp [hU']
  · simp

/-- [MO.5] -/
theorem MobiusLocal.add {K : ℕ} {f g : Finset V → ℂ} (hf : MobiusLocal K f)
    (hg : MobiusLocal K g) : MobiusLocal K (fun T => f T + g T) := by
  obtain ⟨φ, hφ0, hφ⟩ := hf
  obtain ⟨ψ, hψ0, hψ⟩ := hg
  refine ⟨fun U => φ U + ψ U, fun U hU => ?_, fun T => ?_⟩
  · dsimp only
    rw [hφ0 U hU, hψ0 U hU, add_zero]
  · dsimp only
    rw [hφ T, hψ T, Finset.sum_add_distrib]

/-- [MO.6] -/
theorem MobiusLocal.const_mul {K : ℕ} {f : Finset V → ℂ} (hf : MobiusLocal K f) (c : ℂ) :
    MobiusLocal K (fun T => c * f T) := by
  obtain ⟨φ, hφ0, hφ⟩ := hf
  refine ⟨fun U => c * φ U, fun U hU => ?_, fun T => ?_⟩
  · dsimp only
    rw [hφ0 U hU, mul_zero]
  · dsimp only
    rw [hφ T, Finset.mul_sum]

/-- Product of two subset sums, grouped by the union `W = U ∪ U'`. -/
private lemma CountMobius_mul_aux (φ ψ : Finset V → ℂ) (T : Finset V) :
    (∑ U ∈ T.powerset, φ U) * (∑ U ∈ T.powerset, ψ U) =
      ∑ W ∈ T.powerset, ∑ p ∈ (W.powerset ×ˢ W.powerset).filter (fun p => p.1 ∪ p.2 = W),
        φ p.1 * ψ p.2 := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product' (f := fun U U' => φ U * ψ U'),
    ← Finset.sum_fiberwise_of_maps_to (g := fun p : Finset V × Finset V => p.1 ∪ p.2)
      (t := T.powerset)]
  · refine Finset.sum_congr rfl fun W hW => ?_
    rw [Finset.mem_powerset] at hW
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
    constructor
    · rintro ⟨-, h3⟩
      exact ⟨⟨h3 ▸ Finset.subset_union_left, h3 ▸ Finset.subset_union_right⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1.trans hW, h2.trans hW⟩, h3⟩
  · intro p hp
    rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hp
    exact Finset.mem_powerset.mpr (Finset.union_subset hp.1 hp.2)

/-- [MO.7] Products: a `K`-local times an `L`-local function is `(K+L)`-local. -/
theorem MobiusLocal.mul {K L : ℕ} {f g : Finset V → ℂ} (hf : MobiusLocal K f)
    (hg : MobiusLocal L g) : MobiusLocal (K + L) (fun T => f T * g T) := by
  obtain ⟨φ, hφ0, hφ⟩ := hf
  obtain ⟨ψ, hψ0, hψ⟩ := hg
  refine ⟨fun W => ∑ p ∈ (W.powerset ×ˢ W.powerset).filter (fun p => p.1 ∪ p.2 = W),
    φ p.1 * ψ p.2, fun W hW => ?_, fun T => ?_⟩
  · refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_filter] at hp
    have hcard := Finset.card_union_le p.1 p.2
    rw [hp.2] at hcard
    rcases lt_or_ge K p.1.card with h | h
    · rw [hφ0 _ h, zero_mul]
    · rw [hψ0 _ (by omega), mul_zero]
  · dsimp only
    rw [hφ T, hψ T]
    exact CountMobius_mul_aux φ ψ T

/-- [MO.8] -/
theorem MobiusLocal.mono {K L : ℕ} {f : Finset V → ℂ} (hf : MobiusLocal K f) (hKL : K ≤ L) :
    MobiusLocal L f := by
  obtain ⟨φ, hφ0, hφ⟩ := hf
  exact ⟨φ, fun U hU => hφ0 U (lt_of_le_of_lt hKL hU), hφ⟩

/-- [MO.9] -/
theorem MobiusLocal.sum {ι : Type*} (s : Finset ι) {K : ℕ} {f : ι → Finset V → ℂ}
    (hf : ∀ i ∈ s, MobiusLocal K (f i)) : MobiusLocal K (fun T => ∑ i ∈ s, f i T) := by
  induction s using Finset.induction_on with
  | empty =>
    have e : (fun T => ∑ i ∈ (∅ : Finset ι), f i T) = fun _ => (0 : ℂ) := by
      funext T
      rw [Finset.sum_empty]
    rw [e]
    exact mobiusLocal_const K 0
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have e : (fun T => ∑ i ∈ insert a s, f i T) = fun T => f a T + ∑ i ∈ s, f i T := by
      funext T
      rw [Finset.sum_insert ha]
    rw [e]
    exact h1.add h2

/-- [MO.10] `μf(S)` only depends on `f` on the subsets of `S`. -/
theorem vtxMobius_congr {f g : Finset V → ℂ} {S : Finset V} (h : ∀ T ⊆ S, f T = g T) :
    vtxMobius f S = vtxMobius g S := CountMobius_congr h

/-- [MO.11] -/
theorem vtxMobius_add (f g : Finset V → ℂ) (S : Finset V) :
    vtxMobius (fun T => f T + g T) S = vtxMobius f S + vtxMobius g S := CountMobius_add f g S

/-- [MO.12] If `f` does not see the vertex `b ∈ S`, then `μf(S) = 0` (the disconnected case of
the proof of `lem:local-decomposition`). -/
theorem vtxMobius_eq_zero_of_insert {f : Finset V → ℂ} {S : Finset V} {b : V} (hb : b ∈ S)
    (h : ∀ T ⊆ S.erase b, f (insert b T) = f T) : vtxMobius f S = 0 := by
  unfold vtxMobius
  rw [← Finset.insert_erase hb, Finset.sum_powerset_insert (Finset.notMem_erase b S),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun T hT => ?_
  rw [Finset.mem_powerset] at hT
  have hbT : b ∉ T := fun hbT => (Finset.notMem_erase b S) (hT hbT)
  rw [h T hT, Finset.card_insert_of_notMem hbT,
    Finset.card_insert_of_notMem (Finset.notMem_erase b S)]
  have hle : T.card ≤ (S.erase b).card := Finset.card_le_card hT
  have e : (S.erase b).card + 1 - T.card = ((S.erase b).card + 1 - (T.card + 1)) + 1 := by
    omega
  rw [e, pow_succ]
  ring

end CountMobius

end

end ERZeroFreeness
