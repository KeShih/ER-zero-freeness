/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import EndStatement
import ERZeroFreeness.Main
import ERZeroFreeness.AppendixC
import ERZeroFreeness.PTMain
import ERZeroFreeness.RSBethePos
import ERZeroFreeness.VBMain
import ERZeroFreeness.CountVBMain
import ERZeroFreeness.CountColor
import ERZeroFreeness.CountLogCoeff
import ERZeroFreeness.CountSignedPoly

/-!
# The claims of `EndStatement.lean`, proved

Each definition of `EndStatement.lean` is a verbatim copy of the library's definition of the same
name, so the two are equal by unfolding, and each claim is the corresponding library theorem.
The one exception is `ℓ_j`: `EndStatement.ellCoeff` is the coefficient of Mathlib's formal
logarithm `PowerSeries.logOf`, while the library computes `ℓ_j` by the recursion
`j a_j = ∑_{r=1}^{j} r ℓ_r a_{j-r}` (`logCoeff`); `logCoeff_eq_coeff_logOf` identifies the two.
-/

open Filter Topology

namespace ERZeroFreeness

theorem endStatement_ellCoeff_eq {V : Type*} [Fintype V] (H : SimpleGraph V) {q : ℕ}
    (hq : 1 ≤ q) (J : Sym2 V → ℤ) (j : ℕ) : EndStatement.ellCoeff H q J j = ellCoeff H q J j :=
  (logCoeff_eq_coeff_logOf (Count.signedPoly_coeff_zero hq H J) j).symm

theorem endStatement_vbApprox_eq {V : Type*} [Fintype V] (G : SimpleGraph V) (J : Sym2 V → ℤ)
    (k : ℕ) (β : ℝ) : EndStatement.vbApprox G J k β = vbApprox G J k β := by
  unfold EndStatement.vbApprox vbApprox
  simp only [endStatement_ellCoeff_eq G (by norm_num : 1 ≤ 2)]

/-- Theorem 1.1 is `potts_zero_free`. -/
theorem endStatement_theorem_1_1 : EndStatement.Theorem_1_1 :=
  fun _ hq _ hd hd2 => potts_zero_free hq hd hd2

/-- Corollary 1.3 is `cor_range`. -/
theorem endStatement_corollary_1_3 : EndStatement.Corollary_1_3 :=
  fun _ hη => cor_range hη

/-- Corollary 1.4 is `cor_all_but_one`. -/
theorem endStatement_corollary_1_4 : EndStatement.Corollary_1_4 :=
  fun _ hd => cor_all_but_one hd

/-- Appendix B is `potts_zero_free_positive_temperature`. -/
theorem endStatement_appendix_B : EndStatement.Appendix_B :=
  fun _ hq _ hx0 hx1 _ hd hdx => potts_zero_free_positive_temperature hq hx0 hx1 hd hdx

/-- Theorem 1.5 (i) is `ising_af_zero_free`. -/
theorem endStatement_theorem_1_5_i : EndStatement.Theorem_1_5_i :=
  fun _ hd _ hx0 hx1 hdx => ising_af_zero_free hd hx0 hx1 hdx

/-- Theorem 1.5 (ii) is `viana_bray_zero_free`. -/
theorem endStatement_theorem_1_5_ii : EndStatement.Theorem_1_5_ii :=
  fun _ hd _ hβ hdβ => viana_bray_zero_free hd hβ hdβ

/-- Theorem 1.5 (ii), counting at the level of coefficients, is `viana_bray_counting`. -/
theorem endStatement_theorem_1_5_ii_counting : EndStatement.Theorem_1_5_ii_counting := by
  intro d hd βs hβs hdβ B hB
  obtain ⟨C, hC⟩ := viana_bray_counting hd hβs hdβ hB
  refine ⟨C, ?_⟩
  simp only [endStatement_vbApprox_eq]
  exact hC

/-- Theorem C.1 is `potts_zero_free_up_to_condensation`. -/
theorem endStatement_theorem_C_1 : EndStatement.Theorem_C_1 :=
  fun _ hq _ hx0 hx1 _ hd hdc => potts_zero_free_up_to_condensation hq hx0 hx1 hd hdc

/-- `d_cond > 0` is `rs_dCond_pos`. -/
theorem endStatement_dCond_pos : EndStatement.dCond_pos :=
  fun _ hq _ hx0 hx1 => rs_dCond_pos hq hx0 hx1

end ERZeroFreeness
