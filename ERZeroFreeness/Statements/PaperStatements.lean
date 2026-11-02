/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import PaperStatements
import ERZeroFreeness.Normalize
import ERZeroFreeness.Transfer
import ERZeroFreeness.Main
import ERZeroFreeness.IsingRelation
import ERZeroFreeness.VBRelation
import ERZeroFreeness.CountLogCoeff
import ERZeroFreeness.CountSignedPoly
import ERZeroFreeness.CountLocal
import ERZeroFreeness.CountConnSets
import ERZeroFreeness.CountInterp
import ERZeroFreeness.CountVB
import ERZeroFreeness.CountColor
import ERZeroFreeness.NonColor
import ERZeroFreeness.PTMain
import ERZeroFreeness.RSBetheMono
import ERZeroFreeness.RSBetheKS
import ERZeroFreeness.AppendixC
import ERZeroFreeness.CKMain

/-!
# The statements of `PaperStatements.lean`, proved

Each definition of `PaperStatements.lean` is a verbatim copy of the library's definition of the
same name, and those of `EndStatement.lean` are too, so the two are equal by unfolding, and each
statement is the corresponding library theorem.  The one exception is `ℓ_j`: `EndStatement.ellCoeff`
and the coefficients in `PaperStatements.Section_8_interpolation` are those of Mathlib's formal
logarithm `PowerSeries.logOf`, while the library computes `ℓ_j` by the recursion
`j a_j = ∑_{r=1}^{j} r ℓ_r a_{j-r}` (`logCoeff`); `logCoeff_eq_coeff_logOf` identifies the two.
-/

open Filter Topology

namespace ERZeroFreeness

theorem paperStatements_ellCoeff_eq {V : Type*} [Fintype V] (H : SimpleGraph V) {q : ℕ}
    (hq : 1 ≤ q) (J : Sym2 V → ℤ) (j : ℕ) : EndStatement.ellCoeff H q J j = ellCoeff H q J j :=
  (logCoeff_eq_coeff_logOf (Count.signedPoly_coeff_zero hq H J) j).symm

theorem paperStatements_vbApprox_eq {V : Type*} [Fintype V] (G : SimpleGraph V)
    (J : Sym2 V → ℤ) (k : ℕ) (β : ℝ) : EndStatement.vbApprox G J k β = vbApprox G J k β := by
  unfold EndStatement.vbApprox vbApprox
  simp only [paperStatements_ellCoeff_eq G (by norm_num : 1 ≤ 2)]

/-! ## Sections 1 and 2 -/

/-- (1.4) is `ising_af_relation`. -/
theorem paperStatements_eq_1_4 : PaperStatements.Eq_1_4 :=
  fun _ _ G _ hz => ising_af_relation G hz

/-- (1.5) is `vbZ_eq`. -/
theorem paperStatements_eq_1_5 : PaperStatements.Eq_1_5 :=
  fun _ _ G J hJ _ hβ => vbZ_eq G J hJ hβ

/-- (2.2) is `pottsZ_eq_zhat`. -/
theorem paperStatements_eq_2_2 : PaperStatements.Eq_2_2 :=
  fun _ _ _ hq G _ hz => pottsZ_eq_zhat hq G hz

/-! ## Section 6 -/

/-- Proposition 6.1, `t`-plane conclusion, is `zero_free_of_first_moment`. -/
theorem paperStatements_proposition_6_1_tplane : PaperStatements.Proposition_6_1_tplane :=
  fun _ hq _ hd _ hs0 hs1 hsq hds _ _ hr hmom =>
    zero_free_of_first_moment hq hd hs0 hs1 hsq hds hr hmom

/-- Proposition 6.1, `z`-plane conclusion, is `prop_zero_free_moment`. -/
theorem paperStatements_proposition_6_1 : PaperStatements.Proposition_6_1 :=
  fun _ hq _ hd _ hs0 hs1 hsq hds _ _ hr hmom =>
    prop_zero_free_moment hq hd hs0 hs1 hsq hds hr hmom

/-- The return to the `z`-plane in the proof of Proposition 6.1 is `zplane_of_tplane`. -/
theorem paperStatements_proposition_6_1_return_to_z :
    PaperStatements.Proposition_6_1_return_to_z :=
  fun _ hq _ _ hs hsq hρ => zplane_of_tplane hq hs hsq hρ

/-- (5.11) is `first_moment_bound`. -/
theorem paperStatements_eq_5_11 : PaperStatements.Eq_5_11 :=
  fun _ hq _ hd hd2 => first_moment_bound hq hd hd2

/-! ## Section 8 -/

/-- Lemma 8.2 is `connected_sets`. -/
theorem paperStatements_lemma_8_2 : PaperStatements.Lemma_8_2 :=
  fun _ hd _ hB => connected_sets hd hB

/-- The interpolation estimate is `interpolation_estimate`. -/
theorem paperStatements_section_8_interpolation : PaperStatements.Section_8_interpolation := by
  intro p hp M hzf t ht ε hε k hk
  have h0 : p.coeff 0 = 1 := by rw [Polynomial.coeff_zero_eq_eval_zero]; exact hp
  simp only [← logCoeff_eq_coeff_logOf h0]
  exact interpolation_estimate hp hzf ht hε hk

/-- Proposition 8.4 (ii), at the level of coefficients, is `vb_counting_real`. -/
theorem paperStatements_proposition_8_4_ii : PaperStatements.Proposition_8_4_ii := by
  intro d hd βs r hβs hr hzf B hB
  obtain ⟨C, hC⟩ := vb_counting_real hd hβs hr hzf hB
  refine ⟨C, ?_⟩
  simp only [paperStatements_vbApprox_eq]
  exact hC

/-! ## Appendices A and B -/

/-- `d₂(q) ∼ 2q log q` is `tendsto_d2_div_two_mul_log`. -/
theorem paperStatements_appendix_A_d2_asymptotic : PaperStatements.Appendix_A_d2_asymptotic :=
  tendsto_d2_div_two_mul_log

/-- `d₂` is strictly increasing: `d2_strictMonoOn`. -/
theorem paperStatements_appendix_A_d2_strictMono : PaperStatements.Appendix_A_d2_strictMono :=
  d2_formula_strictMonoOn

/-- `d_nc` is strictly increasing: `dnc_strictMonoOn`. -/
theorem paperStatements_appendix_A_dnc_strictMono : PaperStatements.Appendix_A_dnc_strictMono :=
  dnc_strictMonoOn

/-- `d₂(q+1) > 2q log q > d_nc(q)` is `dnc_lt_d2_succ`. -/
theorem paperStatements_appendix_A_dnc_lt_d2_succ : PaperStatements.Appendix_A_dnc_lt_d2_succ :=
  fun _ hq => dnc_lt_d2_succ hq

/-- The intervals `[d₂(q), d_nc(q))` are pairwise disjoint: `d2_dnc_subsingleton`. -/
theorem paperStatements_appendix_A_disjoint : PaperStatements.Appendix_A_disjoint :=
  d2_dnc_subsingleton

/-- Non-colorability for `d ≥ d_nc(q)` is `noncolorable_whp`. -/
theorem paperStatements_corollary_1_4_noncolorable :
    PaperStatements.Corollary_1_4_noncolorable :=
  fun _ hq _ hd => noncolorable_whp hq hd

/-- Appendix B, `t`-plane form, is `pt_zero_free_tplane`. -/
theorem paperStatements_appendix_B_tplane : PaperStatements.Appendix_B_tplane :=
  fun _ hq _ hx0 hx1 _ hd hdx => pt_zero_free_tplane hq hx0 hx1 hd hdx

/-! ## Appendix C -/

/-- Proposition C.2 is `rs_first_moment_zplane_unconditional`. -/
theorem paperStatements_proposition_C_2 : PaperStatements.Proposition_C_2 :=
  fun _ hq _ hxs0 hxs1 _ hd hdc => rs_first_moment_zplane_unconditional hq hxs0 hxs1 hd hdc

/-- Proposition C.2, `t`-plane form, is `rs_first_moment_tube_unconditional`. -/
theorem paperStatements_proposition_C_2_tube : PaperStatements.Proposition_C_2_tube :=
  fun _ hq _ hxs0 hxs1 _ hd hdc => rs_first_moment_tube_unconditional hq hxs0 hxs1 hd hdc

/-- Lemma C.3, monotonicity, is `rs_dCond_mono`. -/
theorem paperStatements_lemma_C_3_monotone : PaperStatements.Lemma_C_3_monotone :=
  fun _ hq _ _ hy0 hyx hx1 => rs_dCond_mono hq hy0 hyx hx1

/-- Lemma C.3, Kesten–Stigum bound, is `rs_dCond_le_inv_sq`. -/
theorem paperStatements_lemma_C_3_ks_bound : PaperStatements.Lemma_C_3_ks_bound :=
  fun _ hq _ hx0 hx1 => rs_dCond_le_inv_sq hq hx0 hx1

/-- Lemma C.3, (C.5), is `rs_free_energy_unconditional`. -/
theorem paperStatements_lemma_C_3_free_energy : PaperStatements.Lemma_C_3_free_energy := by
  intro q hq x hx0 hx1 s hs0 hs
  refine ⟨fun n => ?_, rs_free_energy_unconditional hq hx0 hx1 hs0 hs⟩
  have hlam : ∀ i, 0 ≤ rsMean n s i := fun i => by
    unfold rsMean
    positivity
  have hF := fun N : RSGraph n => rs_rsF_bounds hq hx0 hx1.le N
  have hFpos : ∀ N : RSGraph n, 0 < rsF q (tRe q x) N := fun N =>
    lt_of_lt_of_le (pow_pos hx0 _) (hF N).1
  -- the series of the library's definitions; the trusted copies are equal to them by unfolding
  have hsum : Summable fun N : RSGraph n =>
      poisPi (rsMean n s) N * (rsF q (tRe q x) N * Real.log (rsF q (tRe q x) N)) := by
    refine rs_summable_poisPi_of_abs_le hlam (A := 2) (c := 9 / 4) (by norm_num) fun N => ?_
    have h1 := RSFreeEnergyAux.abs_mulLog_le (hFpos N).le
    have h2 : rsF q (tRe q x) N ^ 2 ≤ ((3 / 2 : ℝ) ^ rsEdges N) ^ 2 :=
      pow_le_pow_left₀ (hFpos N).le (hF N).2 2
    have h3 : ((3 / 2 : ℝ) ^ rsEdges N) ^ 2 = (9 / 4) ^ (∑ i, N i) := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
      rfl
    have h4 : (1 : ℝ) ≤ (9 / 4) ^ (∑ i, N i) := one_le_pow₀ (by norm_num)
    linarith
  exact hsum

/-- [CKPZ, Proposition 3.6] for the Potts antiferromagnet is `ckpz_prop36`. -/
theorem paperStatements_CKPZ_proposition_3_6 : PaperStatements.CKPZ_Proposition_3_6 :=
  fun _ hq => ckpz_prop36 hq

end ERZeroFreeness
