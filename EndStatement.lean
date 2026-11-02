/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# What is proved

The zero-freeness theorems of *Zero-Freeness and Deterministic Counting on Erdős–Rényi Random
Graphs* (Ke Shi), and the coefficient-level content of the counting part of its Theorem 1.5 (ii),
stated as propositions.  This file imports Mathlib alone and contains no proofs: it
defines every object that the statements mention and states each claim as a `Prop`.
`Challenge/EndStatement.lean` asserts the propositions with `sorry`, and
`Solution/EndStatement.lean` proves them from the library; the tool Comparator checks that the two
agree and that the proofs use only Lean's three standard axioms.

| Claim | Paper |
|---|---|
| `Theorem_1_1` | Theorem 1.1: Potts zero-freeness near `[0,1]` for `d < d₂(q)` |
| `Corollary_1_3` | Corollary 1.3, zero-freeness part: colorability scale `q ≥ (1/2+η) d/log d` |
| `Corollary_1_4` | Corollary 1.4 for `q ≥ 3`, without the algorithm: zero-freeness or no proper coloring |
| `Appendix_B` | Appendix B, zero-freeness part: `d < d₂(q) ((q-1+x₀)/((q-1)(1-x₀)))²` |
| `Theorem_1_5_i` | Theorem 1.5 (i): Ising antiferromagnet, zero-freeness |
| `Theorem_1_5_ii` | Theorem 1.5 (ii): Viana–Bray spin glass, zero-freeness |
| `Theorem_1_5_ii_counting` | Theorem 1.5 (ii), counting, at the level of coefficients |
| `Lemma_8_1` | Lemma 8.1: `ℓ_j` is a sum over connected induced subgraphs on at most `2j` vertices |
| `Theorem_C_1`, `dCond_pos` | Theorem C.1, zero-freeness up to condensation, and `d_cond > 0` |

**How the claims are to be read.**
* `G(n,p)` is the explicit finite law `erWeight` on the simple graphs on `Fin n`: each of the
  `n choose 2` pairs is an edge independently with probability `p`, and `erProb n p A` is the
  probability of a set `A` of graphs.  In the signed model `sgProb` the graph is `G(n,p)` and every
  element of `Sym2 (Fin n)` (the pairs, and the `n` diagonal elements, which are never edges)
  carries an independent uniform sign; only the signs of edges of `G` enter the statements, so
  this is the paper's model with uniform signs on the edges.  "With probability tending to one" is
  `Tendsto (fun n => erProb n (d / n) A_n) atTop (𝓝 1)`.  For the finitely many `n` with
  `1 ≤ n < d` the number `d / n` exceeds `1` (and `d / 0 = 0` in Lean), so the weights are not a
  law of `G(n,d/n)` there; a limit does not see these `n`.
* In every claim the radius `ρ` (and the constants `D`, `q_d`, `C`) are chosen before `n`.
* `Z_G(q,z) = ∑_{σ : V → [q]} z^{m_G(σ)}` with Lean's `0 ^ 0 = 1`, so `Z_G(q,0)` is the number of
  proper `q`-colorings of `G`.
* `d_cond(q,x)` is the infimum of `{r > 0 : Ψ_{r,x}(ν) > 0 for some ν ∈ 𝒫_u}`, where `Ψ` is the
  normalized Bethe functional `eq:bethe-condensation`, written out with explicit Poisson weights
  and product measures.  In Lean `sInf ∅ = 0`; `dCond_pos` shows `d_cond(q,x) > 0` for
  `x ∈ [0,1)`, so the set is nonempty there, `d_cond` is its true infimum, and the hypothesis of
  Theorem C.1 can be met.  The paper's comparison `d₂(q) ≤ d_cond(q,0)` (which rests on
  [CKPZ, Theorem 1.2]) is not formalized, so this file does not show that Theorem C.1 at
  `x_* = 0` contains Theorem 1.1.
* The counting results of the paper (Theorem 1.2, the algorithms of Corollaries 1.3 and 1.4 and
  of Appendix B, and the counting parts of Theorems 1.5 and C.1) are algorithms with running-time
  bounds; none of them is formalized, and Proposition 8.4 (i), on which all of them except
  Theorem 1.5 (ii) rest, has no counterpart here.  For Theorem 1.5 (ii), `Theorem_1_5_ii_counting`
  and `Lemma_8_1` state the mathematical content on which the algorithm rests: with high
  probability every size `s` has at most `n² B^s` connected vertex sets; each `ℓ_j` is a sum over
  the connected induced subgraphs on at most `2j` vertices (Lemma 8.1); and for every
  `k ≥ C log(n/ε)` the truncated logarithm built from `ℓ_1, …, ℓ_k` approximates `Z^VB` within a
  factor `1 ± ε`.  The exact computation of the `ℓ_j` (Lemma 8.3) and the numerical evaluation are
  not formalized.
-/

open Filter Topology MeasureTheory Polynomial

namespace EndStatement

open scoped Classical

noncomputable section

/-! ## The Potts partition function and the Erdős–Rényi graph -/

section Potts

variable {V : Type*} [Fintype V]

/-- `m_G(σ)`: the number of edges of `G` whose two endpoints receive the same color. -/
def monoCount (G : SimpleGraph V) {q : ℕ} (σ : V → Fin q) : ℕ :=
  (G.edgeFinset.filter fun e => (e.map σ).IsDiag).card

/-- **`eq:partition`.** The `q`-state Potts partition function
`Z_G(q,z) = ∑_{σ : V → [q]} z^{m_G(σ)}` (with `0^0 = 1`). -/
def pottsZ (G : SimpleGraph V) (q : ℕ) (z : ℂ) : ℂ :=
  ∑ σ : V → Fin q, z ^ monoCount G σ

end Potts

/-- The second-moment threshold `d₂(q) = 2(q-1)³ log(q-1) / (q(q-2))`, used for `q ≥ 3` (at `q = 2`
Lean's `x / 0 = 0` gives `d2 2 = 0`). -/
def d2 (q : ℕ) : ℝ :=
  2 * ((q : ℝ) - 1) ^ 3 * Real.log ((q : ℝ) - 1) / ((q : ℝ) * ((q : ℝ) - 2))

/-- `K_ρ = {z ∈ ℂ : dist(z,[0,1]) ≤ ρ}`. -/
def Kρ (ρ : ℝ) : Set ℂ :=
  {z | ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧ ‖z - x‖ ≤ ρ}

/-- The probability of the graph `G` under `G(n,p)`: each of the `n choose 2` possible edges is
present independently with probability `p`. -/
def erWeight (n : ℕ) (p : ℝ) (G : SimpleGraph (Fin n)) : ℝ :=
  p ^ G.edgeFinset.card * (1 - p) ^ (n.choose 2 - G.edgeFinset.card)

/-- `Pr_{G ∼ G(n,p)}[G ∈ A]`. -/
def erProb (n : ℕ) (p : ℝ) (A : Set (SimpleGraph (Fin n))) : ℝ :=
  ∑ G : SimpleGraph (Fin n), if G ∈ A then erWeight n p G else 0

/-! ## Signed graphs: the two-state polynomial and the Viana–Bray model -/

section Signed

variable {V : Type*} [Fintype V]

/-- The edge entry `A_{σ_u σ_v}` of `A = q·Id − J` on the edge `e = uv` under the coloring `σ`:
`q - 1` if `σ_u = σ_v` and `-1` otherwise.  For `q = 2`, identifying `Fin 2` with `{1,-1}`, it is
`σ_u σ_v`. -/
def edgeA (q : ℕ) (σ : V → Fin q) (e : Sym2 V) : ℂ :=
  if (e.map σ).IsDiag then (q : ℂ) - 1 else -1

/-- **`eq:algorithm-polynomial`.** `P_{H,J}(t) = E_σ ∏_{e ∈ E(H)} (1 + t J_e A_{σ e})`, `σ`
uniform on `[q]^V`, for a graph with edge signs `J`.  For `q = 2` this is the polynomial
`𝓘_{H,J}(t) = 2^{-n} ∑_{σ ∈ {±1}^V} ∏_{uv ∈ E(H)} (1 + t J_{uv} σ_u σ_v)` of
`eq:ising-normalization`. -/
def signedPoly (H : SimpleGraph V) (q : ℕ) (J : Sym2 V → ℤ) : ℂ[X] :=
  C (((q : ℂ) ^ Fintype.card V)⁻¹) *
    ∑ σ : V → Fin q, ∏ e ∈ H.edgeFinset, (1 + C ((J e : ℂ) * edgeA q σ e) * X)

/-- **`eq:viana-bray`.** The zero-field Viana–Bray partition function
`Z^VB_{G,J}(β) = ∑_{σ ∈ {±1}^V} exp(β ∑_{uv ∈ E(G)} J_{uv} σ_u σ_v)`. -/
def vbZ (G : SimpleGraph V) (J : Sym2 V → ℤ) (β : ℂ) : ℂ :=
  ∑ σ : V → Fin 2, Complex.exp (β * ∑ e ∈ G.edgeFinset, (J e : ℂ) * edgeA 2 σ e)

/-- `ℓ_j(H)`: the `j`-th coefficient of the formal logarithm of `P_{H,J}` (`eq:log-coefficients`),
`log P_{H,J}(t) = ∑_{j ≥ 1} ℓ_j t^j` as formal power series.  Mathlib's `PowerSeries.logOf f` is
`log(1 + X)` composed with `f - 1`; since `P_{H,J}(0) = 1` for `q ≥ 1`, `f - 1` has zero constant
term and `logOf f = ∑_{i ≥ 1} (-1)^{i+1} (f - 1)^i / i` coefficientwise, and `ℓ_0 = 0`. -/
def ellCoeff (H : SimpleGraph V) (q : ℕ) (J : Sym2 V → ℤ) (j : ℕ) : ℂ :=
  PowerSeries.coeff j (PowerSeries.logOf (signedPoly H q J : PowerSeries ℂ))

/-- The truncated-logarithm approximation of `Z^VB_{G,J}(β)` from the first `k` coefficients (exact
arithmetic, before any numerical evaluation):
`Z̃_k(β) = 2^n cosh(β)^{|E(G)|} exp(∑_{j=1}^{k} ℓ_j(G) tanh(β)^j)`. -/
def vbApprox (G : SimpleGraph V) (J : Sym2 V → ℤ) (k : ℕ) (β : ℝ) : ℂ :=
  2 ^ Fintype.card V * (Real.cosh β : ℂ) ^ G.edgeFinset.card *
    Complex.exp (∑ j ∈ Finset.Icc 1 k, ellCoeff G 2 J j * (Real.tanh β : ℂ) ^ j)

/-- **`eq:local-mobius`.** The vertex Möbius weight
`ω_j(H) = ∑_{T ⊆ V(H)} (-1)^{|V(H)|-|T|} ℓ_j(H[T])`, where `H[T]` is the induced subgraph on `T`
with the signs of its edges. -/
def omegaCoeff (H : SimpleGraph V) (q : ℕ) (J : Sym2 V → ℤ) (j : ℕ) : ℂ :=
  ∑ T : Finset V, (-1) ^ (Fintype.card V - T.card) *
    ellCoeff (H.induce (T : Set V)) q (fun e => J (e.map Subtype.val)) j

/-- `N_s(G)`: the number of vertex sets `S` of size `s` that induce a connected subgraph
(Mathlib's `Connected` includes nonemptiness, so `N_0(G) = 0`). -/
def connSetCount (G : SimpleGraph V) (s : ℕ) : ℕ :=
  (Finset.univ.filter fun S : Finset V => S.card = s ∧ (G.induce (S : Set V)).Connected).card

end Signed

/-- **`eq:connected-set-bound`.** `N_s(G) ≤ n² B^s` for every `s ≥ 1`. -/
def ConnSetBound {n : ℕ} (B : ℝ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ s : ℕ, 1 ≤ s → (connSetCount G s : ℝ) ≤ (n : ℝ) ^ 2 * B ^ s

/-- A uniform sign: `true ↦ 1`, `false ↦ -1`. -/
def boolSign (b : Bool) : ℤ := if b then 1 else -1

/-- Weight of `(G, J)` in the signed Erdős–Rényi model: `G ∼ G(n,p)` and an independent uniform sign
on every element of `Sym2 (Fin n)`. -/
def sgWeight (n : ℕ) (p : ℝ) (G : SimpleGraph (Fin n)) (_J : Sym2 (Fin n) → Bool) : ℝ :=
  erWeight n p G / 2 ^ Fintype.card (Sym2 (Fin n))

/-- `Pr_{(G,J)}[(G,J) ∈ A]` in the signed Erdős–Rényi model. -/
def sgProb (n : ℕ) (p : ℝ) (A : Set (SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool))) : ℝ :=
  ∑ G : SimpleGraph (Fin n), ∑ J : Sym2 (Fin n) → Bool,
    if (G, J) ∈ A then sgWeight n p G J else 0

/-! ## The condensation threshold `d_cond(q,x)` (`eq:bethe-condensation`) -/

/-- `A_{ab} = q·[a = b] - 1`: the matrix `A = q·Id - J` of `edgeA`, indexed by colors
(`edgeA q σ s(u,v)` is `rsA q (σ u) (σ v)` cast to `ℂ`). -/
def rsA (q : ℕ) (a b : Fin q) : ℤ := if a = b then (q : ℤ) - 1 else -1

/-- `M_t(a,b) = 1 + t·A_{ab}`, the normalized edge matrix `M = J + tA`. -/
def rsM {R : Type*} [Ring R] (q : ℕ) (t : R) (a b : Fin q) : R := 1 + t * (rsA q a b : R)

/-- `t(x) = (x - 1)/(x + q - 1)`. -/
def tRe (q : ℕ) (x : ℝ) : ℝ := (x - 1) / (x + q - 1)

/-- The probability simplex `{μ ∈ [0,1]^q : ∑_a μ_a = 1}`. -/
abbrev rsSimplex (q : ℕ) : Type := ↥(stdSimplex ℝ (Fin q))

/-- `(M_t μ)_a = ∑_b M_t(a,b) μ_b`. -/
def betheMvec (q : ℕ) (t : ℝ) (μ : Fin q → ℝ) (a : Fin q) : ℝ := ∑ b, rsM q t a b * μ b

/-- `V_k = q⁻¹ ∑_a ∏_{i<k} (M_t μ_i)_a` (`V_0 = 1`). -/
def betheV (q : ℕ) (t : ℝ) {k : ℕ} (μ : Fin k → Fin q → ℝ) : ℝ :=
  (q : ℝ)⁻¹ * ∑ a, ∏ i, betheMvec q t (μ i) a

/-- `E = μ₁ᵀ M_t μ₂`. -/
def betheE (q : ℕ) (t : ℝ) (μ₁ μ₂ : Fin q → ℝ) : ℝ := ∑ a, μ₁ a * betheMvec q t μ₂ a

/-- `𝒫_u`: the Borel probability measures on the simplex with mean `u = (1/q, …, 1/q)`. -/
def rsPu (q : ℕ) : Set (ProbabilityMeasure (rsSimplex q)) :=
  {ν | ∀ a : Fin q, ∫ μ, (μ : Fin q → ℝ) a ∂(ν : Measure (rsSimplex q)) = (q : ℝ)⁻¹}

/-- The Poisson mass function `P(Pois(λ) = k) = e^{-λ} λ^k / k!`. -/
def poisPMF (lam : ℝ) (k : ℕ) : ℝ := Real.exp (-lam) * lam ^ k / k.factorial

/-- The normalized Potts Bethe functional
`Ψ_{r,x}(ν) = E[V_D log V_D] - (r/2) E[E_x log E_x]`, where `μ_1, μ_2, … ∼ ν` are i.i.d.,
`D ∼ Pois(r)` is independent of them, and `M_x = M_{t(x)}`.  Lean's `Real.log 0 = 0` gives
`0 log 0 = 0`.  For `q ≥ 3` and `x ∈ [0,1)` the entries of `M_x` lie in `[0, 3/2]`, so
`0 ≤ V_k ≤ (3/2)^k` and `0 ≤ E_x ≤ 3/2`: every integrand is bounded and measurable and the series
in `k` converges absolutely, so the default values of `∑'` and `∫` never occur (other `x` are not
used). -/
def bethePsi (q : ℕ) (r x : ℝ) (ν : ProbabilityMeasure (rsSimplex q)) : ℝ :=
  (∑' k : ℕ, poisPMF r k *
      ∫ μ : Fin k → rsSimplex q,
        betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)) *
          Real.log (betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)))
        ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q)))) -
    r / 2 * ∫ μ : Fin 2 → rsSimplex q,
        betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ) *
          Real.log (betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ))
        ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q)))

/-- The condensation threshold `d_cond(q,x) = inf {r > 0 : sup_{ν ∈ 𝒫_u} Ψ_{r,x}(ν) > 0}`, with
"`sup_ν Ψ > 0`" written "`Ψ(ν) > 0` for some `ν`".  Lean's `sInf ∅ = 0`; for `q ≥ 3` and
`x ∈ [0,1)` the set is nonempty (`dCond_pos`) and bounded below by `0`, so this is its true
infimum. -/
def dCond (q : ℕ) (x : ℝ) : ℝ :=
  sInf {r : ℝ | 0 < r ∧ ∃ ν ∈ rsPu q, 0 < bethePsi q r x ν}

/-! ## The claims -/

/-- **Theorem 1.1 (`thm:zero-free`).** Fix an integer `q ≥ 3` and `0 < d < d₂(q)`.  There is
`ρ > 0`, independent of `n`, such that `Pr[Z_{G_n}(q,z) ≠ 0 for every z ∈ K_ρ] → 1`,
`G_n ∼ G(n,d/n)`. -/
def Theorem_1_1 : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ d : ℝ, 0 < d → d < d2 q →
    ∃ ρ > 0, Tendsto (fun n : ℕ => erProb n (d / n)
      {G | ∀ z ∈ Kρ ρ, pottsZ G q z ≠ 0}) atTop (𝓝 1)

/-- **Corollary 1.3 (`cor:range`), zero-freeness part.** For every `η > 0` and all sufficiently
large `d`, the conclusion of Theorem 1.1 holds for every integer `q ≥ (1/2 + η) d / log d`. -/
def Corollary_1_3 : Prop :=
  ∀ η : ℝ, 0 < η → ∃ D : ℝ, ∀ d : ℝ, D ≤ d → ∀ q : ℕ, (1 / 2 + η) * d / Real.log d ≤ q →
    ∃ ρ > 0, Tendsto (fun n : ℕ => erProb n (d / n)
      {G | ∀ z ∈ Kρ ρ, pottsZ G q z ≠ 0}) atTop (𝓝 1)

/-- **Corollary 1.4 (`cor:all-but-one`), for `q ≥ 3`, without the algorithm.** For every `d > 0`
there is an integer `q_d ≥ 1` such that every integer `q ≥ 3` other than `q_d` satisfies the
conclusion of Theorem 1.1 (on which the counting algorithm at `z = 0` rests), or
`Z_{G_n}(q,0) = 0` with probability tending to one, i.e. `G_n` has no proper `q`-coloring.  (The
paper treats `q = 1, 2` by exact algorithms, which are not stated here.) -/
def Corollary_1_4 : Prop :=
  ∀ d : ℝ, 0 < d → ∃ qd : ℕ, 1 ≤ qd ∧ ∀ q : ℕ, 3 ≤ q → q ≠ qd →
    (∃ ρ > 0, Tendsto (fun n : ℕ => erProb n (d / n)
      {G | ∀ z ∈ Kρ ρ, pottsZ G q z ≠ 0}) atTop (𝓝 1)) ∨
    Tendsto (fun n : ℕ => erProb n (d / n) {G | pottsZ G q 0 = 0}) atTop (𝓝 1)

/-- **Appendix B (`eq:positive-temperature-range`), zero-freeness part** (the FPTAS on `[x₀,1]` is
not formalized).  Fix an integer `q ≥ 3`, `x₀ ∈ (0,1)` and
`0 < d < d₂(q) ((q-1+x₀)/((q-1)(1-x₀)))²`.  There is `ρ > 0` such that, with probability tending to
one, `Z_{G_n}(q,z) ≠ 0` whenever `dist(z,[x₀,1]) ≤ ρ`. -/
def Appendix_B : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ x0 : ℝ, 0 < x0 → x0 < 1 → ∀ d : ℝ, 0 < d →
    d < d2 q * (((q : ℝ) - 1 + x0) / (((q : ℝ) - 1) * (1 - x0))) ^ 2 →
    ∃ ρ > 0, Tendsto (fun n : ℕ => erProb n (d / n)
      {G | ∀ z : ℂ, (∃ x : ℝ, x ∈ Set.Icc x0 1 ∧ ‖z - x‖ ≤ ρ) → pottsZ G q z ≠ 0}) atTop (𝓝 1)

/-- **Theorem 1.5 (i) (`thm:ising-applications`), zero-field Ising antiferromagnet,
zero-freeness.** Fix
`d > 0` and `x_* ∈ (0,1)` with `d ((1-x_*)/(1+x_*))² < 1`.  There is `ρ > 0` such that, with
probability tending to one, `Z_{G_n}(2,z) ≠ 0` whenever `dist(z,[x_*,1]) ≤ ρ`. -/
def Theorem_1_5_i : Prop :=
  ∀ d : ℝ, 0 < d → ∀ xs : ℝ, 0 < xs → xs < 1 → d * ((1 - xs) / (1 + xs)) ^ 2 < 1 →
    ∃ ρ > 0, Tendsto (fun n : ℕ => erProb n (d / n)
      {G | ∀ z : ℂ, (∃ x : ℝ, x ∈ Set.Icc xs 1 ∧ ‖z - x‖ ≤ ρ) → pottsZ G 2 z ≠ 0}) atTop (𝓝 1)

/-- **Theorem 1.5 (ii) (`thm:ising-applications`), Viana–Bray spin glass, zero-freeness.** Fix
`d > 0` and `β_* > 0` with `d tanh² β_* < 1`; the edges of `G_n ∼ G(n,d/n)` carry independent
uniform signs `J`.  There is `ρ > 0` such that, with probability tending to one,
`𝓘_{G_n,J}(t) ≠ 0` whenever `|t| ≤ tanh β_*`, and `Z^VB_{G_n,J}(β) ≠ 0` whenever
`dist(β,[-β_*,β_*]) ≤ ρ`. -/
def Theorem_1_5_ii : Prop :=
  ∀ d : ℝ, 0 < d → ∀ βs : ℝ, 0 < βs → d * Real.tanh βs ^ 2 < 1 →
    ∃ ρ > 0, Tendsto (fun n : ℕ => sgProb n (d / n)
      {GJ | (∀ t : ℂ, ‖t‖ ≤ Real.tanh βs →
          (signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))).eval t ≠ 0) ∧
        ∀ β : ℂ, (∃ x : ℝ, x ∈ Set.Icc (-βs) βs ∧ ‖β - x‖ ≤ ρ) →
          vbZ GJ.1 (fun e => boolSign (GJ.2 e)) β ≠ 0}) atTop (𝓝 1)

/-- **Theorem 1.5 (ii), counting, at the level of coefficients** (the content of the proof of
`prop:counting` (ii) in Section 8).  Fix `d > 0`, `β_* > 0` with `d tanh² β_* < 1`, and
`B > 2e(d+1)`.  There is `C` such that, with probability tending to one over `(G_n, J)`:
* `N_s(G_n) ≤ n² B^s` for every `s ≥ 1` (`eq:connected-set-bound`); and
* for every `β ∈ [-β_*, β_*]`, every `ε ∈ (0,1)` and every `k ≥ C log(n/ε)`, the truncated
  logarithm `Z̃_k(β)` built from `ℓ_1, …, ℓ_k` is real and lies within a factor `1 ± ε` of
  `Z^VB_{G_n,J}(β)`.
By `Lemma_8_1` each `ℓ_j` is a sum over the connected induced subgraphs on at most `2j`
vertices, of which there are at most `∑_{s ≤ 2k} n² B^s` on this event.  Here `C` is the constant
of the truncation order `k = O(log(n/ε))`, not the running-time exponent of the paper. -/
def Theorem_1_5_ii_counting : Prop :=
  ∀ d : ℝ, 0 < d → ∀ βs : ℝ, 0 < βs → d * Real.tanh βs ^ 2 < 1 →
    ∀ B : ℝ, 2 * Real.exp 1 * (d + 1) < B →
    ∃ C : ℝ, Tendsto (fun n : ℕ => sgProb n (d / n)
      {GJ | ConnSetBound B GJ.1 ∧
        ∀ β ∈ Set.Icc (-βs) βs, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ k : ℕ,
          C * Real.log (n / ε) ≤ k →
            ∃ x y : ℝ, vbApprox GJ.1 (fun e => boolSign (GJ.2 e)) k β = x ∧
              vbZ GJ.1 (fun e => boolSign (GJ.2 e)) β = y ∧
              (1 - ε) * y ≤ x ∧ x ≤ (1 + ε) * y}) atTop (𝓝 1)

/-- **Lemma 8.1 (`lem:local-decomposition`).** For every finite graph `G` with integer edge weights
`J` (the paper: signs `±1`), every `q ≥ 1` and every `j ≥ 1`:
`ℓ_j(G) = ∑ ω_j(G[S])`, the sum over the vertex sets `S` with `1 ≤ |S| ≤ 2j` that induce a
connected subgraph (`eq:local-log-decomposition`). -/
def Lemma_8_1 : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ), 1 ≤ q → ∀ (G : SimpleGraph V) (J : Sym2 V → ℤ) (j : ℕ),
    1 ≤ j →
    ellCoeff G q J j =
      ∑ S ∈ Finset.univ.filter (fun S : Finset V =>
          1 ≤ S.card ∧ S.card ≤ 2 * j ∧ (G.induce (S : Set V)).Connected),
        omegaCoeff (G.induce (S : Set V)) q (fun e => J (e.map Subtype.val)) j

/-- **Theorem C.1 (`thm:rs-extension`), zero-freeness.** Fix an integer `q ≥ 3`, `x_* ∈ [0,1)` and
`0 < d < d_cond(q,x_*)`.  There is `ρ > 0` such that, with probability tending to one,
`Z_{G_n}(q,z) ≠ 0` whenever `dist(z,[x_*,1]) ≤ ρ`. -/
def Theorem_C_1 : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ xs : ℝ, 0 ≤ xs → xs < 1 → ∀ d : ℝ, 0 < d → d < dCond q xs →
    ∃ ρ > 0, Tendsto (fun n : ℕ => erProb n (d / n)
      {G | ∀ z : ℂ, (∃ x : ℝ, x ∈ Set.Icc xs 1 ∧ ‖z - x‖ ≤ ρ) → pottsZ G q z ≠ 0}) atTop (𝓝 1)

/-- Theorem C.1 is not vacuous: `d_cond(q,x) > 0` for every integer `q ≥ 3` and `x ∈ [0,1)`. -/
def dCond_pos : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ x : ℝ, 0 ≤ x → x < 1 → 0 < dCond q x

end

end EndStatement
