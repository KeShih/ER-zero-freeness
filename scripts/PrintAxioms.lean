/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Statements.EndStatement

/-! Prints the axioms of every claim of `EndStatement.lean`.  Run with
`lake env lean scripts/PrintAxioms.lean`; each line should end with
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms ERZeroFreeness.endStatement_theorem_1_1
#print axioms ERZeroFreeness.endStatement_corollary_1_3
#print axioms ERZeroFreeness.endStatement_corollary_1_4
#print axioms ERZeroFreeness.endStatement_appendix_B
#print axioms ERZeroFreeness.endStatement_theorem_1_5_i
#print axioms ERZeroFreeness.endStatement_theorem_1_5_ii
#print axioms ERZeroFreeness.endStatement_theorem_1_5_ii_counting
#print axioms ERZeroFreeness.endStatement_theorem_C_1
#print axioms ERZeroFreeness.endStatement_dCond_pos
