/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.SignedDefs
import ERZeroFreeness.Normalize

/-! # `IsingRelation`: part of Theorem 1.5 (`thm:ising-applications`), zero-freeness

Proof plans for the statements of this module: `docs/ising-vb/blueprint.md`, section
"Module `IsingRelation`" (and Appendix A for proofs already checked).  Frozen statements carry their
blueprint item numbers in the comments. -/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

-- [IL1] evaluation of `P_{H,J}` (`eq:algorithm-polynomial`, `eq:ising-normalization`).
theorem signedPoly_eval {V : Type*} [Fintype V] (H : SimpleGraph V) (q : ℕ) (J : Sym2 V → ℤ)
    (t : ℂ) :
    (signedPoly H q J).eval t =
      ((q : ℂ) ^ Fintype.card V)⁻¹ *
        ∑ σ : V → Fin q, ∏ e ∈ H.edgeFinset, (1 + t * ((J e : ℂ) * edgeA q σ e)) := by
  simp only [signedPoly, eval_mul, eval_C, eval_finsetSum, eval_prod, eval_add, eval_one, eval_X]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => Finset.prod_congr rfl fun e _ => ?_
  ring

-- [IL2] `𝓘_{G,1} = Ẑ_G` for `q = 2` (and `P_{H,1} = Ẑ_H` for every `q`).
-- Owned here; `Count.signedPoly_one_eq_zhat` is its alias (blueprint §8).
theorem signedPoly_one {V : Type*} [Fintype V] (H : SimpleGraph V) (q : ℕ) :
    signedPoly H q (fun _ => 1) = zhat H q := by
  simp [signedPoly, zhat]

-- [IL3] **`eq:ising-af-relation`** (`z ≠ -1`; at `z = -1` the right side is undefined).
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
