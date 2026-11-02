/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.SignedDefs

/-! Definitions only (no theorems, no proofs): every definition used in a frozen statement of
another module lives here, so that `scripts/check-frozen.py` (which tracks `theorem`s) together
with "provers never edit this module" freezes their meaning. -/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- [Def IR-a] The spin `σ_v ∈ {1, -1}` of a colour `a ∈ Fin 2` (`0 ↦ 1`, `1 ↦ -1`). -/
def isingSpin (a : Fin 2) : ℝ := if a = 0 then 1 else -1

/-- [Def IR-b] The magnetization `S_σ = ∑_v σ_v` of a configuration `σ ∈ {±1}^n`
(colours in `Fin 2`). -/
def isingMag {n : ℕ} (σ : Fin n → Fin 2) : ℝ := ∑ v, isingSpin (σ v)

/-- [Def VM-a] The sign `J(C) = ∏_{e ∈ E(C)} J_e ∈ {±1}` of a cycle. -/
def cycSign {V : Type*} (J : Sym2 V → Bool) {j : ℕ} (γ : Cyc V j) : ℤ :=
  ∏ e ∈ γ.edges, boolSign (J e)

/-- [Def VM-b] `C^±_{j+3}(G,J)`: the number of `(j+3)`-cycles `γ` of `G` with
`J(γ) = boolSign b` (`b = true` for `+`, `b = false` for `-`). -/
def sgCycleCount {V : Type*} [Fintype V] (G : SimpleGraph V) (J : Sym2 V → Bool) (j : ℕ)
    (b : Bool) : ℕ :=
  (Finset.univ.filter fun γ : Cyc V j => γ.edges ⊆ G.edgeFinset ∧ cycSign J γ = boolSign b).card

/-- [Def VM-c] The signed short-cycle vector
`(C^+_3, …, C^+_{r+2}, C^-_3, …, C^-_{r+2}) ∈ ℕ^{r+r}`. -/
def sgCycleCounts {V : Type*} [Fintype V] (r : ℕ) (G : SimpleGraph V) (J : Sym2 V → Bool) :
    Fin (r + r) → ℕ :=
  Fin.append (fun i : Fin r => sgCycleCount G J i true) (fun i : Fin r => sgCycleCount G J i false)

/-- [Def VM-d] The Poisson means `d^ℓ/(4ℓ) = λ_ℓ/2` of `P^±_ℓ`, `ℓ = i + 3`, in the same
layout. -/
def sgCycleMeans (d : ℝ) (r : ℕ) : Fin (r + r) → ℝ :=
  Fin.append (fun i : Fin r => cycleMean d i / 2) (fun i : Fin r => cycleMean d i / 2)

/-- [Def VM-e] The signed finite cycle product
`Q^{sg}_{r+2}(t; x) = ∏_{ℓ=3}^{r+2} (1 + t^ℓ)^{x^+_ℓ} (1 - t^ℓ)^{x^-_ℓ}`. -/
def sgCyclePoly (r : ℕ) (x : Fin (r + r) → ℕ) : ℂ[X] :=
  ∏ i : Fin r, ((1 + X ^ (i.1 + 3)) ^ x (Fin.castAdd r i) *
    (1 - X ^ (i.1 + 3)) ^ x (Fin.natAdd r i))

/-! ═══════════════════════════════════ Part (i) ═══════════════════════════════════ -/

end

end ERZeroFreeness
