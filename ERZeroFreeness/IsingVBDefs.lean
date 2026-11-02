/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.SignedDefs

/-!
# Definitions for Theorem 1.5 (Ising antiferromagnet and Viana–Bray spin glass)

Definitions used in the statements of the `Ising*` and `VB*` modules (`thm:ising-applications`,
Section 7); the module contains no theorems.

* `isingSpin`, `isingMag`: the spin `σ_v ∈ {1, -1}` of a `Fin 2`-colouring and the
  magnetization `S_σ = ∑_v σ_v`.
* `cycSign`, `sgCycleCount`, `sgCycleCounts`: the sign `J(C)` of a cycle, the numbers `C^±_ℓ` of
  `ℓ`-cycles with `J(C) = ±1`, and the signed short-cycle vector.
* `sgCycleMeans`, `sgCyclePoly`: the Poisson means `d^ℓ/(4ℓ)` of `P^±_ℓ` and the signed finite
  cycle product `Q^{sg}_{r+2}`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- The spin `σ_v ∈ {1, -1}` of a colour `a ∈ Fin 2` (`0 ↦ 1`, `1 ↦ -1`). -/
def isingSpin (a : Fin 2) : ℝ := if a = 0 then 1 else -1

/-- The magnetization `S_σ = ∑_v σ_v` of a configuration `σ ∈ {±1}^n` (colours in `Fin 2`). -/
def isingMag {n : ℕ} (σ : Fin n → Fin 2) : ℝ := ∑ v, isingSpin (σ v)

/-- The sign `J(C) = ∏_{e ∈ E(C)} J_e ∈ {±1}` of a cycle. -/
def cycSign {V : Type*} (J : Sym2 V → Bool) {j : ℕ} (γ : Cyc V j) : ℤ :=
  ∏ e ∈ γ.edges, boolSign (J e)

/-- `C^±_{j+3}(G,J)`: the number of `(j+3)`-cycles `γ` of `G` with `J(γ) = boolSign b`
(`b = true` for `+`, `b = false` for `-`). -/
def sgCycleCount {V : Type*} [Fintype V] (G : SimpleGraph V) (J : Sym2 V → Bool) (j : ℕ)
    (b : Bool) : ℕ :=
  (Finset.univ.filter fun γ : Cyc V j => γ.edges ⊆ G.edgeFinset ∧ cycSign J γ = boolSign b).card

/-- The signed short-cycle vector `(C^+_3, …, C^+_{r+2}, C^-_3, …, C^-_{r+2}) ∈ ℕ^{r+r}`. -/
def sgCycleCounts {V : Type*} [Fintype V] (r : ℕ) (G : SimpleGraph V) (J : Sym2 V → Bool) :
    Fin (r + r) → ℕ :=
  Fin.append (fun i : Fin r => sgCycleCount G J i true) (fun i : Fin r => sgCycleCount G J i false)

/-- The Poisson means `d^ℓ/(4ℓ) = λ_ℓ/2` of `P^±_ℓ`, `ℓ = i + 3`, in the layout of
`sgCycleCounts`. -/
def sgCycleMeans (d : ℝ) (r : ℕ) : Fin (r + r) → ℝ :=
  Fin.append (fun i : Fin r => cycleMean d i / 2) (fun i : Fin r => cycleMean d i / 2)

/-- The signed finite cycle product
`Q^{sg}_{r+2}(t; x) = ∏_{ℓ=3}^{r+2} (1 + t^ℓ)^{x^+_ℓ} (1 - t^ℓ)^{x^-_ℓ}`. -/
def sgCyclePoly (r : ℕ) (x : Fin (r + r) → ℕ) : ℂ[X] :=
  ∏ i : Fin r, ((1 + X ^ (i.1 + 3)) ^ x (Fin.castAdd r i) *
    (1 - X ^ (i.1 + 3)) ^ x (Fin.natAdd r i))

end

end ERZeroFreeness
