/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs

/-!
# Signed graphs: shared definitions for Section 7 (Viana–Bray) and Section 8 (coefficients)

* `signedPoly H q J` — `P_{H,J}(t) = E_σ ∏_{ab ∈ E(H)} (1 + t J_{ab} A_{σ_a σ_b})`
  (`eq:algorithm-polynomial`), `σ` uniform on `[q]^V`.  With `J ≡ 1` it is `zhat H q`; for `q = 2`
  it is the two-state polynomial `𝓘_{H,J}` of `eq:ising-normalization` (identify `Fin 2` with
  `{1,-1}`: `A_{ab} = 2·[a = b] - 1 = σ_a σ_b`).
* `vbZ G J β` — the zero-field Viana–Bray partition function `eq:viana-bray`,
  `∑_{σ ∈ {±1}^V} exp(β ∑_{uv ∈ E} J_{uv} σ_u σ_v)`, written with `Fin 2` colours.
* `sgWeight`, `sgProb`, `sgExp` — the signed Erdős–Rényi model: `G ∼ G(n,p)` together with
  independent uniform signs `J_e ∈ {1,-1}` on all `e ∈ Sym2 (Fin n)` (signs off `E(G)` are
  irrelevant, so this is the paper's model with uniform signs on the edges of `G`).
-/

open Polynomial

namespace ERZeroFreeness

open scoped Classical

noncomputable section

section Signed

variable {V : Type*} [Fintype V]

/-- **`eq:algorithm-polynomial`.** `P_{H,J}(t) = E_σ ∏_{e ∈ E(H)} (1 + t J_e A_{σ e})` for a graph
with edge signs `J : Sym2 V → ℤ` (values off `E(H)` are irrelevant). -/
def signedPoly (H : SimpleGraph V) (q : ℕ) (J : Sym2 V → ℤ) : ℂ[X] :=
  C (((q : ℂ) ^ Fintype.card V)⁻¹) *
    ∑ σ : V → Fin q, ∏ e ∈ H.edgeFinset, (1 + C ((J e : ℂ) * edgeA q σ e) * X)

/-- **`eq:viana-bray`.** `Z^{VB}_{G,J}(β) = ∑_σ exp(β ∑_{uv ∈ E(G)} J_{uv} σ_u σ_v)`, with
`σ_u σ_v = edgeA 2 σ uv` for `Fin 2`-valued spins. -/
def vbZ (G : SimpleGraph V) (J : Sym2 V → ℤ) (β : ℂ) : ℂ :=
  ∑ σ : V → Fin 2, Complex.exp (β * ∑ e ∈ G.edgeFinset, (J e : ℂ) * edgeA 2 σ e)

end Signed

section SignedModel

/-- A uniform sign: `true ↦ 1`, `false ↦ -1`. -/
def boolSign (b : Bool) : ℤ := if b then 1 else -1

/-- Weight of `(G, J)` in the signed Erdős–Rényi model: `G ∼ G(n,p)` and independent uniform signs
on all pairs. -/
def sgWeight (n : ℕ) (p : ℝ) (G : SimpleGraph (Fin n)) (_J : Sym2 (Fin n) → Bool) : ℝ :=
  erWeight n p G / 2 ^ Fintype.card (Sym2 (Fin n))

/-- `Pr_{(G,J)}[(G,J) ∈ A]` in the signed Erdős–Rényi model. -/
def sgProb (n : ℕ) (p : ℝ) (A : Set (SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool))) : ℝ :=
  ∑ G : SimpleGraph (Fin n), ∑ J : Sym2 (Fin n) → Bool,
    if (G, J) ∈ A then sgWeight n p G J else 0

/-- `E_{(G,J)}[f(G,J)]` in the signed Erdős–Rényi model. -/
def sgExp (n : ℕ) (p : ℝ) (f : SimpleGraph (Fin n) → (Sym2 (Fin n) → Bool) → ℝ) : ℝ :=
  ∑ G : SimpleGraph (Fin n), ∑ J : Sym2 (Fin n) → Bool, sgWeight n p G J * f G J

end SignedModel

end

end ERZeroFreeness
