/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.SignedDefs

/-! # `CountDefs`: the definitions of the counting workstream (blueprint §2)

Definitions only.  `logCoeff` is defined by the recursion of the proof of Lemma 8.3,
`j a_j = ∑_{r=1}^{j} r ℓ_r a_{j-r}` with `a_0 = 1`, solved for `ℓ_j`.  When `p(0) = 1` it is
the coefficient sequence of the formal logarithm of `p`: `logCoeff_eq_coeff_logOf` [LC.10]
(Mathlib's `PowerSeries.logOf`); its analytic meaning is `exists_eval_eq_exp_logCoeff` [IN.3].
Never unfold it with `simp [logCoeff]` (loops on `logCoeff.eq_2`); use one `rw [logCoeff]`.
`H[T]` is Mathlib's `H.induce (T : Set V)`, a graph on the subtype, with signs
`J ∘ Sym2.map Subtype.val` ("an induced subgraph keeps the signs of its edges"); `spanInduce H T`
is the same graph with the vertices outside `T` kept as isolated vertices (same polynomial,
`signedPoly_induce_eq`), which is the form used in the proofs.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- [D.1] **`eq:log-coefficients`.** The logarithmic coefficients `ℓ_j(p)` of a polynomial `p`
with `p(0) = 1`: `ℓ_0 = 0` and `ℓ_{j+1} = a_{j+1} - (1/(j+1)) ∑_{r=1}^{j} r ℓ_r a_{j+1-r}`,
`a_i = p.coeff i`, i.e. the recursion `j a_j = ∑_{r=1}^{j} r ℓ_r a_{j-r}` (`a_0 = 1`) of the
proof of `lem:coefficient-oracle`.  For `p(0) = 1` these are the coefficients of `log p`. -/
def logCoeff {K : Type*} [Field K] (p : K[X]) : ℕ → K
  | 0 => 0
  | j + 1 => p.coeff (j + 1) -
      (∑ r : Fin j, (((r : ℕ) : K) + 1) * logCoeff p ((r : ℕ) + 1) * p.coeff (j - r)) /
        ((j : K) + 1)

/-- [D.2] `ℓ_j(H)`: the logarithmic coefficients of `P_{H,J} = signedPoly H q J`
(`eq:log-coefficients`; they depend on `q` and `J`). -/
def ellCoeff {V : Type*} [Fintype V] (H : SimpleGraph V) (q : ℕ) (J : Sym2 V → ℤ) (j : ℕ) : ℂ :=
  logCoeff (signedPoly H q J) j

/-- [D.3] **`eq:local-mobius`.** The vertex Möbius weight
`ω_j(H) = ∑_{T ⊆ V(H)} (-1)^{|V(H)|-|T|} ℓ_j(H[T])`, where `H[T]` is the induced subgraph on
`T` with the signs of its edges. -/
def omegaCoeff {V : Type*} [Fintype V] (H : SimpleGraph V) (q : ℕ) (J : Sym2 V → ℤ)
    (j : ℕ) : ℂ :=
  ∑ T : Finset V, (-1) ^ (Fintype.card V - T.card) *
    ellCoeff (H.induce (T : Set V)) q (fun e => J (e.map Subtype.val)) j

/-- [D.4] The spanning form of `H[T]`: the graph on `V` whose edges are the edges of `H` with
both endpoints in `T` (vertices outside `T` are isolated). -/
def spanInduce {V : Type*} (H : SimpleGraph V) (T : Finset V) : SimpleGraph V where
  Adj u v := H.Adj u v ∧ u ∈ T ∧ v ∈ T
  symm.symm _ _ h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless.irrefl v h := H.loopless.irrefl v h.1

/-- [D.5] The weight `w(F) = E_σ ∏_{ab ∈ F} J_{ab} A_{σ_a σ_b}` of an edge set (proof of
`lem:local-decomposition`), with `σ` uniform on `[q]^V`. -/
def signedEdgeWeight {V : Type*} [Fintype V] (q : ℕ) (J : Sym2 V → ℤ)
    (F : Finset (Sym2 V)) : ℂ :=
  ((q : ℂ) ^ Fintype.card V)⁻¹ * ∑ σ : V → Fin q, ∏ e ∈ F, (J e : ℂ) * edgeA q σ e

/-- [D.6] The subset Möbius transform `(μf)(S) = ∑_{T ⊆ S} (-1)^{|S|-|T|} f(T)`; with
`f(T) = ℓ_j(G[T])` this is `ω_j(G[S])` (`omegaCoeff_induce_eq_vtxMobius`). -/
def vtxMobius {V : Type*} (f : Finset V → ℂ) (S : Finset V) : ℂ :=
  ∑ T ∈ S.powerset, (-1) ^ (S.card - T.card) * f T

/-- [D.7] `f` is `K`-local: `f(T) = ∑_{U ⊆ T} φ(U)` for some `φ` vanishing on sets of size
`> K` (equivalently, `μf` vanishes on sets of size `> K`). -/
def MobiusLocal {V : Type*} (K : ℕ) (f : Finset V → ℂ) : Prop :=
  ∃ φ : Finset V → ℂ, (∀ U : Finset V, K < U.card → φ U = 0) ∧
    ∀ T : Finset V, f T = ∑ U ∈ T.powerset, φ U

/-- [D.8] `N_s(G)`: the number of connected vertex subsets `S ⊆ V(G)` of size `s` (`G[S]`
connected; Mathlib's `Connected` includes nonemptiness, so `N_0(G) = 0`). -/
def connSetCount {V : Type*} [Fintype V] (G : SimpleGraph V) (s : ℕ) : ℕ :=
  (Finset.univ.filter fun S : Finset V => S.card = s ∧ (G.induce (S : Set V)).Connected).card

/-- [D.9] **`eq:connected-set-bound`** for every `s ≥ 1`: `N_s(G) ≤ n² B^s`. -/
def ConnSetBound {n : ℕ} (B : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ s : ℕ, 1 ≤ s → (connSetCount G s : ℝ) ≤ (n : ℝ) ^ 2 * B ^ s

/-- [D.10] The coefficient-level Viana–Bray approximation
`Z̃_k(β) = 2^n cosh(β)^{|E(G)|} exp(∑_{j=1}^{k} ℓ_j(G) tanh(β)^j)` (proof of
`prop:counting`(ii), before the numerical evaluation of `exp`, `cosh`, `tanh`). -/
def vbApprox {V : Type*} [Fintype V] (G : SimpleGraph V) (J : Sym2 V → ℤ) (k : ℕ) (β : ℝ) :
    ℂ :=
  2 ^ Fintype.card V * (Real.cosh β : ℂ) ^ G.edgeFinset.card *
    Complex.exp (∑ j ∈ Finset.Icc 1 k, ellCoeff G 2 J j * (Real.tanh β : ℂ) ^ j)

end

end ERZeroFreeness
