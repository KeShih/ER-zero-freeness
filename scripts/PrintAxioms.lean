/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Statements.EndStatement
import ERZeroFreeness.Statements.PaperStatements

/-! Prints the axioms of every claim of `EndStatement.lean` and `PaperStatements.lean`.  Run with
`lake env lean scripts/PrintAxioms.lean`; each line should end with
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms ERZeroFreeness.endStatement_theorem_1_1
#print axioms ERZeroFreeness.endStatement_corollary_1_3
#print axioms ERZeroFreeness.endStatement_corollary_1_4
#print axioms ERZeroFreeness.endStatement_appendix_B
#print axioms ERZeroFreeness.endStatement_theorem_1_5_i
#print axioms ERZeroFreeness.endStatement_theorem_1_5_ii
#print axioms ERZeroFreeness.endStatement_theorem_1_5_ii_counting
#print axioms ERZeroFreeness.endStatement_lemma_8_1
#print axioms ERZeroFreeness.endStatement_theorem_C_1
#print axioms ERZeroFreeness.endStatement_dCond_pos

#print axioms ERZeroFreeness.paperStatements_eq_1_4
#print axioms ERZeroFreeness.paperStatements_eq_1_5
#print axioms ERZeroFreeness.paperStatements_eq_2_2
#print axioms ERZeroFreeness.paperStatements_proposition_6_1_tplane
#print axioms ERZeroFreeness.paperStatements_proposition_6_1
#print axioms ERZeroFreeness.paperStatements_proposition_6_1_return_to_z
#print axioms ERZeroFreeness.paperStatements_eq_5_11
#print axioms ERZeroFreeness.paperStatements_lemma_8_2
#print axioms ERZeroFreeness.paperStatements_section_8_interpolation
#print axioms ERZeroFreeness.paperStatements_proposition_8_4_ii
#print axioms ERZeroFreeness.paperStatements_appendix_A_d2_asymptotic
#print axioms ERZeroFreeness.paperStatements_appendix_A_d2_strictMono
#print axioms ERZeroFreeness.paperStatements_appendix_A_dnc_strictMono
#print axioms ERZeroFreeness.paperStatements_appendix_A_dnc_lt_d2_succ
#print axioms ERZeroFreeness.paperStatements_appendix_A_disjoint
#print axioms ERZeroFreeness.paperStatements_corollary_1_4_noncolorable
#print axioms ERZeroFreeness.paperStatements_appendix_B_tplane
#print axioms ERZeroFreeness.paperStatements_proposition_C_2
#print axioms ERZeroFreeness.paperStatements_proposition_C_2_tube
#print axioms ERZeroFreeness.paperStatements_lemma_C_3_monotone
#print axioms ERZeroFreeness.paperStatements_lemma_C_3_ks_bound
#print axioms ERZeroFreeness.paperStatements_lemma_C_3_free_energy
#print axioms ERZeroFreeness.paperStatements_CKPZ_proposition_3_6
