/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# Core definitions

Definitions for Theorem 1.1 (`thm:zero-free`) of
*Zero-Freeness and Deterministic Counting on Erdős–Rényi Random Graphs* (Ke Shi).

This file defines the objects in the statement of Theorem 1.1 and in the statements shared
between the modules of its proof:

* the Potts partition function `pottsZ` (`eq:partition`), the threshold `d2`, the
  neighbourhood `Kρ` of `[0,1]`;
* the Erdős–Rényi law `G(n,p)` through the explicit weights `erWeight`, with `erProb`
  and `erExp`;
* the normalized partition polynomial `zhat` (`eq:normalized-colors`), its edge matrix
  `edgeA`, the maps `bFac`, `tOf` (`eq:transformation`), and the tubes `tube`, `openTube`
  around `I_s = [-s,0]`;
* cycles (`CycSeq`, `Cyc`, `AnyCyc`) and the cycle counts `cycleCount`, `cycleCounts`
  (`lem:cycle-counts`), the "dense subgraph" event `HasDenseSubgraph` and the edge-set
  weight `edgeWeight` (`lem:jets`);
* the constant `cq` of `lem:entropy-comparison`, the relative entropy `empKL` of an empirical
  distribution, the balanced window `balanced` and the balanced partition function `zhatB`
  (`sec:balance`), and the overlap matrix `overlap` (`eq:overlap-def`), used in the moment
  bounds of Section 5;
* the finite cycle product `cyclePoly` (`Q_{r+2}`), the Poisson means `cycleMean`, the
  product Poisson law `poisProd`, and the compensated cycle model `cycleModel` on the
  domain `cycleDomain` (`lem:cycle-general`, finite version).

Everything is classical.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

section Potts

variable {V : Type*} [Fintype V]

/-- `m_G(σ)`: the number of edges of `G` whose two endpoints receive the same colour. -/
def monoCount (G : SimpleGraph V) {q : ℕ} (σ : V → Fin q) : ℕ :=
  (G.edgeFinset.filter fun e => (e.map σ).IsDiag).card

/-- **`eq:partition`.** The `q`-state Potts partition function
`Z_G(q,z) = ∑_{σ : V → [q]} z^{m_G(σ)}` (with `0^0 = 1`). -/
def pottsZ (G : SimpleGraph V) (q : ℕ) (z : ℂ) : ℂ :=
  ∑ σ : V → Fin q, z ^ monoCount G σ

/-- The second-moment threshold `d₂(q) = 2(q-1)³ log(q-1) / (q(q-2))`. -/
def d2 (q : ℕ) : ℝ :=
  2 * ((q : ℝ) - 1) ^ 3 * Real.log ((q : ℝ) - 1) / ((q : ℝ) * ((q : ℝ) - 2))

/-- `K_ρ = {z ∈ ℂ : dist(z,[0,1]) ≤ ρ}`. -/
def Kρ (ρ : ℝ) : Set ℂ :=
  {z | ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧ ‖z - x‖ ≤ ρ}

/-- The edge entry `A_{σ_u σ_v}` of `A = q·Id − J` on the edge `e = uv` under the colouring
`σ`: it is `q - 1` if `σ_u = σ_v` and `-1` otherwise. -/
def edgeA (q : ℕ) (σ : V → Fin q) (e : Sym2 V) : ℂ :=
  if (e.map σ).IsDiag then (q : ℂ) - 1 else -1

/-- **`eq:normalized-colors`.** The normalized partition polynomial
`Ẑ_G(t) = E_σ ∏_{uv ∈ E(G)} (1 + t A_{σ_u σ_v})`, with `σ` uniform on `[q]^V`. -/
def zhat (G : SimpleGraph V) (q : ℕ) : ℂ[X] :=
  C (((q : ℂ) ^ Fintype.card V)⁻¹) *
    ∑ σ : V → Fin q, ∏ e ∈ G.edgeFinset, (1 + C (edgeA q σ e) * X)

/-- The average edge weight `b(z) = (z + q - 1)/q`. -/
def bFac (q : ℕ) (z : ℂ) : ℂ := (z + q - 1) / q

/-- The transformed parameter `t(z) = (z - 1)/(z + q - 1)`. -/
def tOf (q : ℕ) (z : ℂ) : ℂ := (z - 1) / (z + q - 1)

end Potts

section Tubes

/-- The closed `r`-neighbourhood `L_r(I_s)` of `I_s = [-s, 0]` in `ℂ`. -/
def tube (s r : ℝ) : Set ℂ :=
  {t | ∃ x : ℝ, x ∈ Set.Icc (-s) 0 ∧ ‖t - x‖ ≤ r}

/-- The open `r`-neighbourhood `U_r(I_s)` of `I_s = [-s, 0]` in `ℂ`. -/
def openTube (s r : ℝ) : Set ℂ :=
  {t | ∃ x : ℝ, x ∈ Set.Icc (-s) 0 ∧ ‖t - x‖ < r}

end Tubes

section ErdosRenyi

/-- The probability of the graph `G` under the Erdős–Rényi law `G(n,p)`: each of the
`n.choose 2` possible edges is present independently with probability `p`.
(For `0 ≤ p ≤ 1` these weights are nonnegative and sum to one; see `ErdosRenyi.lean`.) -/
def erWeight (n : ℕ) (p : ℝ) (G : SimpleGraph (Fin n)) : ℝ :=
  p ^ G.edgeFinset.card * (1 - p) ^ (n.choose 2 - G.edgeFinset.card)

/-- `Pr_{G ∼ G(n,p)}[G ∈ A]`. -/
def erProb (n : ℕ) (p : ℝ) (A : Set (SimpleGraph (Fin n))) : ℝ :=
  ∑ G : SimpleGraph (Fin n), if G ∈ A then erWeight n p G else 0

/-- `E_{G ∼ G(n,p)}[f(G)]`. -/
def erExp (n : ℕ) (p : ℝ) (f : SimpleGraph (Fin n) → ℝ) : ℝ :=
  ∑ G : SimpleGraph (Fin n), erWeight n p G * f G

end ErdosRenyi

section Cycles

variable {V : Type*}

/-- Injective cyclic sequences `c : ℤ/(j+3) → V`. Such a sequence represents the
`(j+3)`-cycle `c 0, c 1, …, c (j+2), c 0`. -/
def CycSeq (V : Type*) (j : ℕ) : Type _ :=
  {c : ZMod (j + 3) → V // Function.Injective c}

/-- The edge set `{c_i c_{i+1}}` of a cyclic sequence (indices mod `j+3`). -/
def CycSeq.edges {j : ℕ} (c : CycSeq V j) : Finset (Sym2 V) :=
  Finset.univ.image fun i : ZMod (j + 3) => s(c.1 i, c.1 (i + 1))

/-- Two cyclic sequences are related when they differ by a rotation or a reflection,
i.e. by an element of the dihedral group acting on the indices. -/
def CycSeq.Rel {j : ℕ} (c c' : CycSeq V j) : Prop :=
  ∃ a : ZMod (j + 3), (∀ i, c'.1 i = c.1 (a + i)) ∨ (∀ i, c'.1 i = c.1 (a - i))

theorem CycSeq.rel_equivalence (j : ℕ) : Equivalence (@CycSeq.Rel V j) where
  refl c := ⟨0, Or.inl fun i => by simp⟩
  symm := by
    rintro c c' ⟨a, h | h⟩
    · exact ⟨-a, Or.inl fun i => by rw [h]; congr 1; ring⟩
    · exact ⟨a, Or.inr fun i => by rw [h]; congr 1; ring⟩
  trans := by
    rintro c c' c'' ⟨a, h | h⟩ ⟨b, h' | h'⟩
    · exact ⟨a + b, Or.inl fun i => by rw [h', h]; congr 1; ring⟩
    · exact ⟨a + b, Or.inr fun i => by rw [h', h]; congr 1; ring⟩
    · exact ⟨a - b, Or.inr fun i => by rw [h', h]; congr 1; ring⟩
    · exact ⟨a - b, Or.inl fun i => by rw [h', h]; congr 1; ring⟩

/-- The dihedral setoid on cyclic sequences. -/
instance CycSeq.setoid (V : Type*) (j : ℕ) : Setoid (CycSeq V j) :=
  ⟨CycSeq.Rel, CycSeq.rel_equivalence j⟩

theorem CycSeq.edges_eq_of_rel {j : ℕ} {c c' : CycSeq V j} (h : CycSeq.Rel c c') :
    c.edges = c'.edges := by
  obtain ⟨a, h | h⟩ := h
  · ext e
    simp only [CycSeq.edges, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i - a, by rw [h, h]; congr 2 <;> ring_nf⟩
    · rintro ⟨i, rfl⟩
      exact ⟨a + i, by rw [h, h]; congr 2; ring⟩
  · ext e
    simp only [CycSeq.edges, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨a - i - 1, ?_⟩
      rw [h, h, Sym2.eq_swap]
      congr 2 <;> ring
    · rintro ⟨i, rfl⟩
      refine ⟨a - i - 1, ?_⟩
      rw [h, h, Sym2.eq_swap]
      congr 2 <;> ring

/-- `(j+3)`-cycles of `V`: injective cyclic sequences up to rotation and reflection. -/
def Cyc (V : Type*) (j : ℕ) : Type _ := Quotient (CycSeq.setoid V j)

/-- The edge set of a cycle. -/
def Cyc.edges {j : ℕ} : Cyc V j → Finset (Sym2 V) :=
  Quotient.lift CycSeq.edges fun _ _ h => CycSeq.edges_eq_of_rel h

instance CycSeq.fintype [Fintype V] (j : ℕ) : Fintype (CycSeq V j) := by
  unfold CycSeq; infer_instance

instance Cyc.fintype [Fintype V] (j : ℕ) : Fintype (Cyc V j) := by
  unfold Cyc; infer_instance

/-- A cycle of any length `≥ 3`: the length of `⟨j, γ⟩` is `j + 3`. -/
abbrev AnyCyc (V : Type*) : Type _ := Σ j : ℕ, Cyc V j

/-- The edge set of a cycle of any length. -/
def AnyCyc.edges (γ : AnyCyc V) : Finset (Sym2 V) := γ.2.edges

/-- The vertices touched by a set of edges. -/
def edgeVerts [Fintype V] (S : Finset (Sym2 V)) : Finset V :=
  Finset.univ.filter fun v => ∃ e ∈ S, v ∈ e

/-- The number of edges of `S` containing `v` (the degree of `v` in the edge set `S`). -/
def edgeDeg (S : Finset (Sym2 V)) (v : V) : ℕ :=
  (S.filter fun e => v ∈ e).card

/-- The vertex set of a cycle of any length. -/
def AnyCyc.verts [Fintype V] (γ : AnyCyc V) : Finset V := edgeVerts γ.edges

variable [Fintype V]

/-- `C_{j+3}(G)`: the number of (unoriented, simple) `(j+3)`-cycles of `G`. -/
def cycleCount (G : SimpleGraph V) (j : ℕ) : ℕ :=
  (Finset.univ.filter fun γ : Cyc V j => γ.edges ⊆ G.edgeFinset).card

/-- The vector `(C_3(G), …, C_{r+2}(G))`. -/
def cycleCounts (r : ℕ) (G : SimpleGraph V) : Fin r → ℕ :=
  fun i => cycleCount G i

/-- `G` contains a set of at most `b` edges that touches fewer vertices than it has edges. -/
def HasDenseSubgraph (G : SimpleGraph V) (b : ℕ) : Prop :=
  ∃ S ⊆ G.edgeFinset, S.card ≤ b ∧ (edgeVerts S).card < S.card

end Cycles

section Weights

variable {V : Type*} [Fintype V]

/-- The weight `w(S) = E_σ ∏_{e ∈ S} A_{σ e}` of an edge set (proof of `lem:jets`). -/
def edgeWeight (q : ℕ) (S : Finset (Sym2 V)) : ℂ :=
  ((q : ℂ) ^ Fintype.card V)⁻¹ * ∑ σ : V → Fin q, ∏ e ∈ S, edgeA q σ e

theorem zhat_eval (G : SimpleGraph V) (q : ℕ) (t : ℂ) :
    (zhat G q).eval t =
      ((q : ℂ) ^ Fintype.card V)⁻¹ * ∑ σ : V → Fin q, ∏ e ∈ G.edgeFinset, (1 + t * edgeA q σ e) := by
  simp only [zhat, eval_mul, eval_C, eval_finset_sum, eval_prod, eval_add, eval_one, eval_X]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => Finset.prod_congr rfl fun e _ => ?_
  ring

end Weights

section Moments

/-- `c_q = (q-1) log(q-1) / (q(q-2))` (`lem:entropy-comparison`). -/
def cq (q : ℕ) : ℝ := ((q : ℝ) - 1) * Real.log ((q : ℝ) - 1) / ((q : ℝ) * ((q : ℝ) - 2))

/-- The number of `v` with `f v = c`. -/
def fiberCard {ι κ : Type*} [Fintype ι] (f : ι → κ) (c : κ) : ℕ :=
  (Finset.univ.filter fun v => f v = c).card

/-- The relative entropy `D(emp(f) ‖ unif(κ)) = ∑_c (N_c/n) log(|κ| N_c / n)` of the
empirical distribution of `f : ι → κ` (with `n = |ι|`, `N_c = |f⁻¹(c)|`, `0 log 0 = 0`). -/
def empKL {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ) : ℝ :=
  ∑ c : κ, ((fiberCard f c : ℝ) / Fintype.card ι) *
    Real.log ((Fintype.card κ : ℝ) * (fiberCard f c : ℝ) / Fintype.card ι)

/-- The colour-class fraction `α_i(σ) = |σ⁻¹(i)|/n`. -/
def colorFrac {n q : ℕ} (σ : Fin n → Fin q) (i : Fin q) : ℝ := (fiberCard σ i : ℝ) / n

/-- The balanced window `𝓑_n = {σ : |α_i(σ) - 1/q| ≤ δ for all i}` (`sec:balance`). -/
def balanced (q n : ℕ) (δ : ℝ) : Finset (Fin n → Fin q) :=
  Finset.univ.filter fun σ => ∀ i, |colorFrac σ i - 1 / (q : ℝ)| ≤ δ

/-- The balanced partition function `Ẑ^B_G(t) = E_σ[1_{σ ∈ 𝓑_n} ∏_{uv∈E} (1 + t A_{σ_u σ_v})]`. -/
def zhatB {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) (δ : ℝ) (t : ℂ) : ℂ :=
  ((q : ℂ) ^ n)⁻¹ * ∑ σ ∈ balanced q n δ, ∏ e ∈ G.edgeFinset, (1 + t * edgeA q σ e)

/-- The overlap matrix `R_ij = |{v : σ_v = i, τ_v = j}| / n` (`eq:overlap-def`). -/
def overlap {n q : ℕ} (σ τ : Fin n → Fin q) (i j : Fin q) : ℝ :=
  (fiberCard (fun v => (σ v, τ v)) (i, j) : ℝ) / n

end Moments

section CycleModel

/-- The finite Poisson cycle product `Q_{r+2}(t;x) = ∏_{i<r} (1 + (q-1) t^{i+3})^{x_i}`. -/
def cyclePoly (q r : ℕ) (x : Fin r → ℕ) : ℂ[X] :=
  ∏ i : Fin r, (1 + C ((q : ℂ) - 1) * X ^ (i.1 + 3)) ^ x i

/-- The Poisson mean `λ_{i+3} = d^{i+3} / (2(i+3))` of the number of `(i+3)`-cycles. -/
def cycleMean (d : ℝ) (i : ℕ) : ℝ := d ^ (i + 3) / (2 * ((i : ℝ) + 3))

/-- The Poisson probability mass function `e^{-λ} λ^k / k!`. -/
def poisPMF (lam : ℝ) (k : ℕ) : ℝ := Real.exp (-lam) * lam ^ k / k.factorial

/-- The law of independent Poisson variables with means `lam i`, as a mass function on
`ℕ^r`. -/
def poisProd {r : ℕ} (lam : Fin r → ℝ) (x : Fin r → ℕ) : ℝ :=
  ∏ i, poisPMF (lam i) (x i)

/-- `Pr[(P_i)_i ∈ B]` for independent `P_i ∼ Pois(lam i)`. -/
def poisProb {r : ℕ} (lam : Fin r → ℝ) (B : Set (Fin r → ℕ)) : ℝ :=
  ∑' x, B.indicator (poisProd lam) x

/-- `E[f(P)]` for `P ∼ Pois(lam)`. -/
def poisExp (lam : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑' k, poisPMF lam k * f k

/-- The domain `𝒟 = {|t| < 1, d|t|² < 1, (q-1)|t|³ < 1, Re(1 - dt) > 0}` of the
compensated cycle model. -/
def cycleDomain (q : ℕ) (d : ℝ) : Set ℂ :=
  {t | ‖t‖ < 1 ∧ d * ‖t‖ ^ 2 < 1 ∧ ((q : ℝ) - 1) * ‖t‖ ^ 3 < 1 ∧ 0 < (1 - (d : ℂ) * t).re}

/-- The compensated finite cycle product (`lem:cycle-general`)
`W_{r+2}(t;x) = Q_{r+2}(t;x) · exp(-(q-1)/2 · [log(1-dt) + ∑_{ℓ=1}^{r+2} (dt)^ℓ/ℓ])`. -/
def cycleModel (q : ℕ) (d : ℝ) (r : ℕ) (x : Fin r → ℕ) (t : ℂ) : ℂ :=
  (cyclePoly q r x).eval t *
    Complex.exp (-(((q : ℂ) - 1) / 2) *
      (Complex.log (1 - (d : ℂ) * t) +
        ∑ l ∈ Finset.range (r + 2), ((d : ℂ) * t) ^ (l + 1) / ((l : ℂ) + 1)))

end CycleModel

end

end ERZeroFreeness
