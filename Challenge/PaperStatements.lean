/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import PaperStatements

/-! What is claimed: the propositions of `PaperStatements.lean`, each with `sorry` in place of its
proof.  This file imports `PaperStatements.lean` alone, and that file imports Mathlib and
`EndStatement.lean` alone, so whoever has read `EndStatement.lean` and `PaperStatements.lean` knows
what the statements mean.  Nothing imports this file. -/

namespace ERZeroFreeness

/-! ## Sections 1 and 2 -/

/-- (1.4): `Z_G(2,z) = 2^n ((1+z)/2)^{|E|} 𝓘_{G,1}((z-1)/(z+1))`. -/
theorem paperStatements_eq_1_4 : PaperStatements.Eq_1_4 := by
  sorry

/-- (1.5): `Z^VB_{G,J}(β) = 2^n (cosh β)^{|E|} 𝓘_{G,J}(tanh β)`. -/
theorem paperStatements_eq_1_5 : PaperStatements.Eq_1_5 := by
  sorry

/-- (2.2): `Z_G(q,z) = q^{|V|} b(z)^{|E|} Ẑ_G(t(z))`. -/
theorem paperStatements_eq_2_2 : PaperStatements.Eq_2_2 := by
  sorry

/-! ## Section 6 -/

/-- Proposition 6.1, `t`-plane conclusion (6.2): a first-moment bound on a tube gives
zero-freeness of `Ẑ_{G_n}` on a thinner tube, with high probability. -/
theorem paperStatements_proposition_6_1_tplane : PaperStatements.Proposition_6_1_tplane := by
  sorry

/-- Proposition 6.1, `z`-plane conclusion: zero-freeness of `Z_{G_n}(q,·)` near `[x_s,1]`. -/
theorem paperStatements_proposition_6_1 : PaperStatements.Proposition_6_1 := by
  sorry

/-- Proposition 6.1, proof: a zero-free tube for `Ẑ_G` gives a zero-free neighborhood of
`[x_s,1]` for `Z_G(q,·)`, uniformly in the graph. -/
theorem paperStatements_proposition_6_1_return_to_z :
    PaperStatements.Proposition_6_1_return_to_z := by
  sorry

/-- (5.11): the uniform first-moment bound on a tube around `[-1/(q-1), 0]` for `d < d₂(q)`. -/
theorem paperStatements_eq_5_11 : PaperStatements.Eq_5_11 := by
  sorry

/-! ## Section 8 -/

/-- Lemma 8.2: `N_s(G_n) ≤ n² B^s` for all `s ≥ 1`, with probability `1 - O(1/n)`. -/
theorem paperStatements_lemma_8_2 : PaperStatements.Lemma_8_2 := by
  sorry

/-- The interpolation estimate before Proposition 8.4. -/
theorem paperStatements_section_8_interpolation : PaperStatements.Section_8_interpolation := by
  sorry

/-- Proposition 8.4 (ii), at the level of coefficients. -/
theorem paperStatements_proposition_8_4_ii : PaperStatements.Proposition_8_4_ii := by
  sorry

/-! ## Appendices A and B -/

/-- Appendix A: `d₂(q) ∼ 2q log q`. -/
theorem paperStatements_appendix_A_d2_asymptotic : PaperStatements.Appendix_A_d2_asymptotic := by
  sorry

/-- Appendix A: `d₂` is strictly increasing on `[3,∞)`. -/
theorem paperStatements_appendix_A_d2_strictMono : PaperStatements.Appendix_A_d2_strictMono := by
  sorry

/-- Appendix A: `d_nc(q) = (2q-1) log q` is strictly increasing on the integers `q ≥ 1`. -/
theorem paperStatements_appendix_A_dnc_strictMono :
    PaperStatements.Appendix_A_dnc_strictMono := by
  sorry

/-- Appendix A: `d₂(q+1) > 2q log q > d_nc(q)` for `q ≥ 2`. -/
theorem paperStatements_appendix_A_dnc_lt_d2_succ :
    PaperStatements.Appendix_A_dnc_lt_d2_succ := by
  sorry

/-- Appendix A: the intervals `[d₂(q), d_nc(q))`, `q ≥ 3`, are pairwise disjoint. -/
theorem paperStatements_appendix_A_disjoint : PaperStatements.Appendix_A_disjoint := by
  sorry

/-- The non-colorability input of Corollary 1.4: no proper `q`-coloring for `d ≥ d_nc(q)`,
with high probability. -/
theorem paperStatements_corollary_1_4_noncolorable :
    PaperStatements.Corollary_1_4_noncolorable := by
  sorry

/-- Appendix B, `t`-plane form: zero-freeness of `Ẑ_{G_n}` on a tube around `t([x₀,1])`. -/
theorem paperStatements_appendix_B_tplane : PaperStatements.Appendix_B_tplane := by
  sorry

/-! ## Appendix C -/

/-- Proposition C.2: the complex first moment below condensation, `z`-plane form (C.2). -/
theorem paperStatements_proposition_C_2 : PaperStatements.Proposition_C_2 := by
  sorry

/-- Proposition C.2, `t`-plane form. -/
theorem paperStatements_proposition_C_2_tube : PaperStatements.Proposition_C_2_tube := by
  sorry

/-- Lemma C.3: `x ↦ d_cond(q,x)` is nondecreasing on `[0,1)`. -/
theorem paperStatements_lemma_C_3_monotone : PaperStatements.Lemma_C_3_monotone := by
  sorry

/-- Lemma C.3: `d_cond(q,x) ≤ t(x)^{-2}`. -/
theorem paperStatements_lemma_C_3_ks_bound : PaperStatements.Lemma_C_3_ks_bound := by
  sorry

/-- Lemma C.3, (C.5): the series converge and `E_{𝖯_s}[F_G(x) log F_G(x)] = o(n)` below
condensation. -/
theorem paperStatements_lemma_C_3_free_energy : PaperStatements.Lemma_C_3_free_energy := by
  sorry

/-- [CKPZ, Proposition 3.6] for the Potts antiferromagnet, for every `q ≥ 2`. -/
theorem paperStatements_CKPZ_proposition_3_6 : PaperStatements.CKPZ_Proposition_3_6 := by
  sorry

end ERZeroFreeness
