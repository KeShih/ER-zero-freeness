/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.SignedDefs
import ERZeroFreeness.Normalize

/-!
# The two-state polynomial and the Ising antiferromagnet (`eq:ising-af-relation`)

`signedPoly G 2 J` is the two-state polynomial `𝓘_{G,J}(t)` of `eq:ising-normalization`, the
case `q = 2` of `P_{H,J}` (`eq:algorithm-polynomial`).

* `signedPoly_eval`: `P_{H,J}(t) = q^{-|V|} ∑_σ ∏_{e ∈ E(H)} (1 + t J_e A_{σe})`.
* `signedPoly_one`: with all signs equal to `1`, `P_{H,1} = Ẑ_H` for every `q`; in particular
  `𝓘_{G,1} = Ẑ_G`.
* `ising_af_relation`: `eq:ising-af-relation`,
  `Z_G(2,z) = 2^n ((1+z)/2)^{|E(G)|} 𝓘_{G,1}((z-1)/(z+1))` for `z ≠ -1`, the `q = 2` case of
  `eq:transformation` (`pottsZ_eq_zhat`).
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- Evaluation of `P_{H,J}` (`eq:algorithm-polynomial`; for `q = 2`, `eq:ising-normalization`). -/
theorem signedPoly_eval {V : Type*} [Fintype V] (H : SimpleGraph V) (q : ℕ) (J : Sym2 V → ℤ)
    (t : ℂ) :
    (signedPoly H q J).eval t =
      ((q : ℂ) ^ Fintype.card V)⁻¹ *
        ∑ σ : V → Fin q, ∏ e ∈ H.edgeFinset, (1 + t * ((J e : ℂ) * edgeA q σ e)) := by
  simp only [signedPoly, eval_mul, eval_C, eval_finsetSum, eval_prod, eval_add, eval_one, eval_X]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => Finset.prod_congr rfl fun e _ => ?_
  ring

/-- `P_{H,1} = Ẑ_H` for every `q`; for `q = 2`, `𝓘_{G,1} = Ẑ_G`. -/
theorem signedPoly_one {V : Type*} [Fintype V] (H : SimpleGraph V) (q : ℕ) :
    signedPoly H q (fun _ => 1) = zhat H q := by
  simp [signedPoly, zhat]

/-- **`eq:ising-af-relation`**, for `z ≠ -1` (where `(z-1)/(z+1)` is defined). -/
theorem ising_af_relation {V : Type*} [Fintype V] (G : SimpleGraph V) {z : ℂ}
    (hz : z + 1 ≠ 0) :
    pottsZ G 2 z = 2 ^ Fintype.card V * ((1 + z) / 2) ^ G.edgeFinset.card *
      (signedPoly G 2 (fun _ => 1)).eval ((z - 1) / (z + 1)) := by
  have hz' : z + ((2 : ℕ) : ℂ) - 1 ≠ 0 := by
    have : z + ((2 : ℕ) : ℂ) - 1 = z + 1 := by push_cast; ring
    rw [this]; exact hz
  rw [pottsZ_eq_zhat (by norm_num) G hz', signedPoly_one]
  simp only [bFac, tOf]
  push_cast
  congr 3 <;> ring

end

end ERZeroFreeness
