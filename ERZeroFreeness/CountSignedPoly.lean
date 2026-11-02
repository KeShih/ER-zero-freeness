/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.CountLogCoeff
import ERZeroFreeness.IsingRelation

/-! # Basic properties of the polynomial `P_{H,J}`

Properties of `signedPoly H q J = P_{H,J}` (`eq:algorithm-polynomial`) used in Section 8.

## Main results

* `signedPoly_coeff_zero`, `signedPoly_eval_zero`: `P_{H,J}(0) = 1`.
* `signedPoly_natDegree_le`: `deg P_{H,J} ≤ |E(H)|`.
* `signedPoly_eq_one`: the polynomial of an edgeless graph is `1`.
* `signedPoly_one_eq_zhat`: with all signs equal to `1`, `P_{H,J} = Ẑ_H`.
* `signedPoly_coeff`: the edge-subset expansion `P_{H,J}(t) = ∑_{F ⊆ E(H)} w(F) t^{|F|}`.
* `signedPoly_comap`: invariance under relabelling and under adding isolated vertices.
* `signedPoly_spanInduce_union`: multiplicativity over vertex sets not joined by an edge.
* `ellCoeff_rational`: each `ℓ_j(H)` is rational.

## Proof

`P_{H,J}(0) = 1`: every edge factor is `1` at `t = 0`, and `#(V → Fin q) = q^{|V|} ≠ 0`.
Degree: each product has at most `|E(H)|` linear factors.  Edge expansion: the coefficient of
`X^k` in `∏_{i ∈ s} (1 + a_i X)` is the `k`-th elementary symmetric sum of the `a_i`, as in the
proof of `zhat_coeff`.  `signedPoly_comap`: the edges of `H.comap f` correspond to those of `H`
via `Sym2.map f` (all edges of `H` lie in `range f`), `edgeA q σ (e.map f) = edgeA q (σ ∘ f) e`,
and `∑_{σ : V → [q]} F(σ ∘ c) = q^{|V|-|ι|} ∑_x F x` for injective `c`.
Union: the edge set of `spanInduce H (A ∪ B)` is the disjoint union of those of
`spanInduce H A` and `spanInduce H B`; the factor over `A` depends only on `σ|_A`, the one over
`B` only on `σ|_{Aᶜ}`, and `(∑_σ F σ)(∑_σ G σ) = q^{|V|} ∑_σ F σ G σ` for such `F, G` (pair
`(σ, τ)` with `(A.piecewise σ τ, A.piecewise τ σ)`).
Rationality: `signedPoly H q J` is the image of a `ℚ`-polynomial; then `logCoeff_map`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

section CountSignedPoly

namespace Count

variable {V : Type*} [Fintype V]

/-- `P_{H,J}(0) = 1` (constant coefficient). -/
theorem signedPoly_coeff_zero {q : ℕ} (hq : 1 ≤ q) (H : SimpleGraph V) (J : Sym2 V → ℤ) :
    (signedPoly H q J).coeff 0 = 1 := by
  have hq0 : ((q : ℂ) ^ Fintype.card V) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (by omega : q ≠ 0))
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [signedPoly, eval_finsetSum, eval_prod, hq0]

/-- `P_{H,J}(0) = 1`. -/
theorem signedPoly_eval_zero {q : ℕ} (hq : 1 ≤ q) (H : SimpleGraph V) (J : Sym2 V → ℤ) :
    (signedPoly H q J).eval 0 = 1 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  exact signedPoly_coeff_zero hq H J

/-- Each edge factor `1 + C a * X` has degree at most `1`. -/
private lemma CountSignedPoly_natDegree_one_add_C_mul_X_le (a : ℂ) :
    (1 + C a * X : ℂ[X]).natDegree ≤ 1 :=
  (natDegree_add_le _ _).trans
    (max_le (by rw [natDegree_one]; exact Nat.zero_le _)
      ((natDegree_C_mul_le _ _).trans natDegree_X_le))

/-- `deg P_{H,J} ≤ |E(H)|`. -/
theorem signedPoly_natDegree_le (H : SimpleGraph V) (q : ℕ) (J : Sym2 V → ℤ) :
    (signedPoly H q J).natDegree ≤ H.edgeFinset.card := by
  unfold signedPoly
  refine (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  refine (natDegree_prod_le _ _).trans ?_
  have h1 : ∀ e ∈ H.edgeFinset, (1 + C ((J e : ℂ) * edgeA q σ e) * X).natDegree ≤ 1 :=
    fun e _ => CountSignedPoly_natDegree_one_add_C_mul_X_le _
  calc _ ≤ ∑ _e ∈ H.edgeFinset, 1 := Finset.sum_le_sum h1
    _ = H.edgeFinset.card := by rw [Finset.card_eq_sum_ones]

/-- The polynomial of an edgeless graph is `1` (in particular `P_{G[∅],J} = 1`). -/
theorem signedPoly_eq_one {q : ℕ} (hq : 1 ≤ q) {H : SimpleGraph V} (hH : H.edgeFinset = ∅)
    (J : Sym2 V → ℤ) : signedPoly H q J = 1 := by
  have h := signedPoly_natDegree_le H q J
  rw [hH, Finset.card_empty] at h
  rw [eq_C_of_natDegree_le_zero h, signedPoly_coeff_zero hq H J, C_1]

/-- "With all signs equal to 1, `P_{H,J} = Ẑ_H`" (`eq:normalized-colors`); this restates
`signedPoly_one`. -/
theorem signedPoly_one_eq_zhat (H : SimpleGraph V) (q : ℕ) :
    signedPoly H q (fun _ => 1) = zhat H q := ERZeroFreeness.signedPoly_one H q

/-- The coefficient of `X^k` in `∏_{i ∈ s} (1 + a_i X)` is the `k`-th elementary symmetric
sum. -/
private lemma CountSignedPoly_coeff_prod_one_add {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (k : ℕ) :
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

/-- Edge-subset expansion `P_{H,J}(t) = ∑_{F ⊆ E(H)} w(F) t^{|F|}` (proof of
`lem:local-decomposition`). -/
theorem signedPoly_coeff (H : SimpleGraph V) (q : ℕ) (J : Sym2 V → ℤ) (i : ℕ) :
    (signedPoly H q J).coeff i = ∑ F ∈ H.edgeFinset.powersetCard i, signedEdgeWeight q J F := by
  rw [signedPoly, coeff_C_mul, finsetSum_coeff]
  simp_rw [CountSignedPoly_coeff_prod_one_add, signedEdgeWeight, ← Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Colourings restricted along an injective map `c : ι → V`, in a commutative semiring `R`:
`∑_{σ : V → [q]} F(σ ∘ c) = q^{|V| - |ι|} ∑_{x : ι → [q]} F x`. -/
private lemma CountSignedPoly_sum_comp_injective {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommSemiring R] (q : ℕ) {c : ι → V} (hc : Function.Injective c) (F : (ι → Fin q) → R) :
    ∑ σ : V → Fin q, F (σ ∘ c) =
      (q : R) ^ (Fintype.card V - Fintype.card ι) * ∑ x : ι → Fin q, F x := by
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

/-- Relabelling and isolated vertices: if all edges of `H` lie in the range of the
embedding `f`, then `H` and its pull-back `H.comap f` (with pulled-back signs) have the same
polynomial. -/
theorem signedPoly_comap {q : ℕ} (hq : 1 ≤ q) {W : Type*} [Fintype W] (f : W ↪ V)
    (H : SimpleGraph V) (J : Sym2 V → ℤ)
    (hH : ∀ u v, H.Adj u v → u ∈ Set.range f ∧ v ∈ Set.range f) :
    signedPoly (H.comap f) q (fun e => J (e.map f)) = signedPoly H q J := by
  -- the edges of `H.comap f` are the edges of `H`, pulled back along `Sym2.map f`
  have hmap : (H.comap f).edgeFinset.map ⟨Sym2.map f, Sym2.map.injective f.injective⟩ =
      H.edgeFinset := by
    ext e
    simp only [Finset.mem_map, SimpleGraph.mem_edgeFinset, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨e', he', rfl⟩
      induction e' using Sym2.ind with
      | _ a b => simpa using he'
    · intro he
      induction e using Sym2.ind with
      | _ u v =>
        obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hH u v (by simpa using he)
        exact ⟨s(a, b), by simpa using he, rfl⟩
  set F : (W → Fin q) → ℂ[X] := fun τ =>
    ∏ e ∈ (H.comap f).edgeFinset, (1 + C ((J (e.map f) : ℂ) * edgeA q τ e) * X) with hF
  have hprod : ∀ σ : V → Fin q,
      ∏ e ∈ H.edgeFinset, (1 + C ((J e : ℂ) * edgeA q σ e) * X) = F (σ ∘ f) := by
    intro σ
    rw [← hmap, Finset.prod_map, hF]
    refine Finset.prod_congr rfl fun e _ => ?_
    simp only [Function.Embedding.coeFn_mk, edgeA, Sym2.map_map]
  have hle : Fintype.card W ≤ Fintype.card V := Fintype.card_le_of_injective f f.injective
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hconst : ((q : ℂ) ^ Fintype.card V)⁻¹ * (q : ℂ) ^ (Fintype.card V - Fintype.card W) =
      ((q : ℂ) ^ Fintype.card W)⁻¹ := by
    obtain ⟨a, ha⟩ : ∃ a, Fintype.card V = a + Fintype.card W :=
      ⟨_, (Nat.sub_add_cancel hle).symm⟩
    rw [ha, Nat.add_sub_cancel, pow_add]
    field_simp
  unfold signedPoly
  simp_rw [hprod]
  rw [CountSignedPoly_sum_comp_injective q f.injective F, ← mul_assoc,
    show ((q : ℂ[X])) = C (q : ℂ) from (map_natCast C q).symm, ← map_pow, ← map_mul, hconst]
  rfl

/-- The edges of `spanInduce H T` are the edges of `H` inside `T`. -/
theorem edgeFinset_spanInduce (H : SimpleGraph V) (T : Finset V) :
    (spanInduce H T).edgeFinset = H.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ T := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_filter,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    simp [spanInduce]

/-- Independence lemma: if `F` depends only on `σ|_A` and `G` only on `σ|_{Aᶜ}`, then
`(∑_σ F σ)(∑_σ G σ) = q^{|V|} ∑_σ F σ G σ`.  The map
`(σ, τ) ↦ (A.piecewise σ τ, A.piecewise τ σ)` is an involution of `(V → [q])²`. -/
private lemma CountSignedPoly_sum_mul_sum_indep {R : Type*} [CommSemiring R] (q : ℕ)
    (A : Finset V) (F G : (V → Fin q) → R)
    (hF : ∀ σ σ' : V → Fin q, (∀ v ∈ A, σ v = σ' v) → F σ = F σ')
    (hG : ∀ σ σ' : V → Fin q, (∀ v ∉ A, σ v = σ' v) → G σ = G σ') :
    (∑ σ, F σ) * (∑ σ, G σ) = (q : R) ^ Fintype.card V * ∑ σ, F σ * G σ := by
  let pw : (V → Fin q) → (V → Fin q) → (V → Fin q) := fun σ τ v => if v ∈ A then σ v else τ v
  let Φ : (V → Fin q) × (V → Fin q) → (V → Fin q) × (V → Fin q) :=
    fun p => (pw p.1 p.2, pw p.2 p.1)
  have hΦ : Function.Involutive Φ := by
    intro p
    refine Prod.ext ?_ ?_
    · funext v
      simp only [Φ, pw]
      split_ifs <;> rfl
    · funext v
      simp only [Φ, pw]
      split_ifs <;> rfl
  have step1 : ∀ σ τ : V → Fin q, F σ * G τ = F (pw σ τ) * G (pw σ τ) := by
    intro σ τ
    congr 1
    · exact hF _ _ fun v hv => by simp [pw, hv]
    · exact hG _ _ fun v hv => by simp [pw, hv]
  have key : ∑ p : (V → Fin q) × (V → Fin q), F (pw p.1 p.2) * G (pw p.1 p.2) =
      ∑ p : (V → Fin q) × (V → Fin q), F p.1 * G p.1 :=
    Equiv.sum_comp (hΦ.toPerm Φ) (fun p => F p.1 * G p.1)
  rw [Fintype.sum_mul_sum]
  calc ∑ σ, ∑ τ, F σ * G τ = ∑ σ, ∑ τ, F (pw σ τ) * G (pw σ τ) :=
        Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => step1 σ τ
    _ = ∑ p : (V → Fin q) × (V → Fin q), F (pw p.1 p.2) * G (pw p.1 p.2) :=
        (Fintype.sum_prod_type' (fun σ τ => F (pw σ τ) * G (pw σ τ))).symm
    _ = ∑ p : (V → Fin q) × (V → Fin q), F p.1 * G p.1 := key
    _ = ∑ σ : V → Fin q, ∑ _τ : V → Fin q, F σ * G σ :=
        Fintype.sum_prod_type' (fun σ (_ : V → Fin q) => F σ * G σ)
    _ = (q : R) ^ Fintype.card V * ∑ σ, F σ * G σ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        simp

omit [Fintype V] in
/-- The edge factor depends only on the colours of the endpoints. -/
private lemma CountSignedPoly_edgeA_congr {q : ℕ} {σ σ' : V → Fin q} {e : Sym2 V}
    (h : ∀ v ∈ e, σ v = σ' v) : edgeA q σ e = edgeA q σ' e := by
  rw [edgeA, edgeA, Sym2.map_congr h]

/-- Multiplicativity over components: if no edge of `H` joins the disjoint sets `A`
and `B`, then `P_{H[A ∪ B]} = P_{H[A]} P_{H[B]}`. -/
theorem signedPoly_spanInduce_union {q : ℕ} (hq : 1 ≤ q) (H : SimpleGraph V) (J : Sym2 V → ℤ)
    {A B : Finset V} (hAB : Disjoint A B) (hno : ∀ a ∈ A, ∀ b ∈ B, ¬ H.Adj a b) :
    signedPoly (spanInduce H (A ∪ B)) q J =
      signedPoly (spanInduce H A) q J * signedPoly (spanInduce H B) q J := by
  -- the edge set of `H[A ∪ B]` is the disjoint union of those of `H[A]` and `H[B]`
  have hE : (spanInduce H (A ∪ B)).edgeFinset =
      (spanInduce H A).edgeFinset ∪ (spanInduce H B).edgeFinset := by
    rw [edgeFinset_spanInduce, edgeFinset_spanInduce, edgeFinset_spanInduce, ← Finset.filter_or]
    refine Finset.filter_congr fun e he => ?_
    induction e using Sym2.ind with
    | _ u v =>
      have huv : H.Adj u v := by simpa using he
      simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq, Finset.mem_union]
      constructor
      · rintro ⟨hu | hu, hv | hv⟩
        · exact Or.inl ⟨hu, hv⟩
        · exact absurd huv (hno u hu v hv)
        · exact absurd huv.symm (hno v hv u hu)
        · exact Or.inr ⟨hu, hv⟩
      · rintro (⟨hu, hv⟩ | ⟨hu, hv⟩)
        · exact ⟨Or.inl hu, Or.inl hv⟩
        · exact ⟨Or.inr hu, Or.inr hv⟩
  have hdisj : Disjoint (spanInduce H A).edgeFinset (spanInduce H B).edgeFinset := by
    rw [Finset.disjoint_left]
    intro e heA heB
    rw [edgeFinset_spanInduce, Finset.mem_filter] at heA heB
    induction e using Sym2.ind with
    | _ u v =>
      exact Finset.disjoint_left.mp hAB (heA.2 u (Sym2.mem_mk_left u v))
        (heB.2 u (Sym2.mem_mk_left u v))
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hconst : C (((q : ℂ) ^ Fintype.card V)⁻¹) * (q : ℂ[X]) ^ Fintype.card V = 1 := by
    rw [show ((q : ℂ[X])) = C (q : ℂ) from (map_natCast C q).symm, ← map_pow, ← map_mul,
      inv_mul_cancel₀ (pow_ne_zero _ hq0), map_one]
  have hind : (∑ σ : V → Fin q, ∏ e ∈ (spanInduce H A).edgeFinset,
        (1 + C ((J e : ℂ) * edgeA q σ e) * X)) *
      (∑ σ : V → Fin q, ∏ e ∈ (spanInduce H B).edgeFinset,
        (1 + C ((J e : ℂ) * edgeA q σ e) * X)) =
      (q : ℂ[X]) ^ Fintype.card V * ∑ σ : V → Fin q,
        (∏ e ∈ (spanInduce H A).edgeFinset, (1 + C ((J e : ℂ) * edgeA q σ e) * X)) *
        ∏ e ∈ (spanInduce H B).edgeFinset, (1 + C ((J e : ℂ) * edgeA q σ e) * X) := by
    refine CountSignedPoly_sum_mul_sum_indep q A
      (fun σ => ∏ e ∈ (spanInduce H A).edgeFinset, (1 + C ((J e : ℂ) * edgeA q σ e) * X))
      (fun σ => ∏ e ∈ (spanInduce H B).edgeFinset, (1 + C ((J e : ℂ) * edgeA q σ e) * X))
      ?_ ?_
    · intro σ σ' h
      refine Finset.prod_congr rfl fun e he => ?_
      rw [edgeFinset_spanInduce, Finset.mem_filter] at he
      rw [CountSignedPoly_edgeA_congr fun v hv => h v (he.2 v hv)]
    · intro σ σ' h
      refine Finset.prod_congr rfl fun e he => ?_
      rw [edgeFinset_spanInduce, Finset.mem_filter] at he
      rw [CountSignedPoly_edgeA_congr fun v hv => h v (Finset.disjoint_right.mp hAB (he.2 v hv))]
  unfold signedPoly
  rw [hE]
  simp_rw [Finset.prod_union hdisj]
  rw [mul_mul_mul_comm, hind, mul_assoc, ← mul_assoc (C _) ((q : ℂ[X]) ^ _), hconst, one_mul]

end Count

/-- The rational version of the edge factor `A_{σ e}`. -/
private def CountSignedPoly_edgeAQ {V : Type*} (q : ℕ) (σ : V → Fin q) (e : Sym2 V) : ℚ :=
  if (e.map σ).IsDiag then (q : ℚ) - 1 else -1

/-- The rational polynomial whose image in `ℂ[X]` is `P_{H,J}`. -/
private def CountSignedPoly_polyQ {V : Type*} [Fintype V] (H : SimpleGraph V) (q : ℕ)
    (J : Sym2 V → ℤ) : ℚ[X] :=
  C (((q : ℚ) ^ Fintype.card V)⁻¹) *
    ∑ σ : V → Fin q, ∏ e ∈ H.edgeFinset, (1 + C ((J e : ℚ) * CountSignedPoly_edgeAQ q σ e) * X)

private lemma CountSignedPoly_polyQ_map {V : Type*} [Fintype V] (H : SimpleGraph V) (q : ℕ)
    (J : Sym2 V → ℤ) :
    (CountSignedPoly_polyQ H q J).map (algebraMap ℚ ℂ) = signedPoly H q J := by
  simp [CountSignedPoly_polyQ, signedPoly, CountSignedPoly_edgeAQ, edgeA, Polynomial.map_sum,
    Polynomial.map_prod, apply_ite]

/-- "Each `ℓ_j(H)` is rational" (after `eq:log-coefficients`). -/
theorem ellCoeff_rational {V : Type*} [Fintype V] (H : SimpleGraph V) (q : ℕ) (J : Sym2 V → ℤ)
    (j : ℕ) : ∃ x : ℚ, ellCoeff H q J j = x := by
  refine ⟨logCoeff (CountSignedPoly_polyQ H q J) j, ?_⟩
  rw [ellCoeff, ← CountSignedPoly_polyQ_map, logCoeff_map]
  exact eq_ratCast _ _

end CountSignedPoly

end

end ERZeroFreeness
