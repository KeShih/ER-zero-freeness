/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import EndStatement

/-! What is claimed: the propositions of `EndStatement.lean`, each with `sorry` in place of its
proof.  This file imports `EndStatement.lean` alone, and that file imports Mathlib alone, so whoever
has read `EndStatement.lean` knows what the statements mean.  Nothing imports this file. -/

namespace ERZeroFreeness

/-- Theorem 1.1: Potts zero-freeness near `[0,1]` for `0 < d < d₂(q)`. -/
theorem endStatement_theorem_1_1 : EndStatement.Theorem_1_1 := by
  sorry

/-- Corollary 1.3, zero-freeness part: the colourability scale `q ≥ (1/2 + η) d / log d`. -/
theorem endStatement_corollary_1_3 : EndStatement.Corollary_1_3 := by
  sorry

/-- Corollary 1.4 without the algorithm: for all `q ≥ 3` but at most one, zero-freeness near
`[0,1]` or no proper `q`-colouring, with high probability. -/
theorem endStatement_corollary_1_4 : EndStatement.Corollary_1_4 := by
  sorry

/-- Appendix B: Potts zero-freeness near `[x₀,1]` in the positive-temperature range. -/
theorem endStatement_appendix_B : EndStatement.Appendix_B := by
  sorry

/-- Theorem 1.5 (i): zero-freeness of the zero-field Ising antiferromagnet. -/
theorem endStatement_theorem_1_5_i : EndStatement.Theorem_1_5_i := by
  sorry

/-- Theorem 1.5 (ii): zero-freeness of the Viana–Bray spin glass. -/
theorem endStatement_theorem_1_5_ii : EndStatement.Theorem_1_5_ii := by
  sorry

/-- Theorem 1.5 (ii), counting, at the level of coefficients. -/
theorem endStatement_theorem_1_5_ii_counting : EndStatement.Theorem_1_5_ii_counting := by
  sorry

/-- Theorem C.1: Potts zero-freeness up to the condensation threshold. -/
theorem endStatement_theorem_C_1 : EndStatement.Theorem_C_1 := by
  sorry

/-- `d_cond(q,x) > 0` for `x ∈ [0,1)`: Theorem C.1 is not vacuous. -/
theorem endStatement_dCond_pos : EndStatement.dCond_pos := by
  sorry

end ERZeroFreeness
