/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.CountDefs
import ERZeroFreeness.ErdosRenyi
import ERZeroFreeness.VBModel

/-! # `CountSgModel`: the signed Erdős–Rényi model (blueprint §9)

Plan.  SG.1–SG.4 are owned by IV (`VBModel`): prove them as aliases with full names,
`ERZeroFreeness.sgProb_nonneg hp0 hp1 A` [VM6], `ERZeroFreeness.sgProb_mono hp0 hp1 h` [VM7],
`ERZeroFreeness.sgProb_le_one hp0 hp1 A` [VM10], `ERZeroFreeness.sgProb_fst n p A` [VM5].
Fallback without the IV import: `sgWeight = erWeight / 2^N` with `N = #Sym2 (Fin n)` and
`#(Sym2 (Fin n) → Bool) = 2^N`, so summing over `J` gives back `erWeight` (`sum_erWeight`,
`erWeight_nonneg`).  `sgProb_inter_ge`: `P(A ∩ B) = 1 - P(Aᶜ ∪ Bᶜ) ≥ P(A) + P(B) - 1` from IV's
`sgProb_union_le` [VM8] and `sgProb_compl` [VM9] (fallback: termwise
`[A] + [B] - [A ∩ B] = [A ∪ B] ≤ 1`).  The `Tendsto` lemmas: squeeze for `n ≥ d` (where
`d/n ∈ [0,1]`, `div_natCast_mem_Icc`).
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

section CountSgModel

namespace Count

/-- [SG.1] -/
theorem sgProb_nonneg {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool))) : 0 ≤ sgProb n p A :=
  ERZeroFreeness.sgProb_nonneg hp0 hp1 A

/-- [SG.2] -/
theorem sgProb_mono {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {A B : Set (SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool))} (h : A ⊆ B) :
    sgProb n p A ≤ sgProb n p B :=
  ERZeroFreeness.sgProb_mono hp0 hp1 h

/-- [SG.3] -/
theorem sgProb_le_one {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool))) : sgProb n p A ≤ 1 :=
  ERZeroFreeness.sgProb_le_one hp0 hp1 A

/-- [SG.4] Events of the graph alone have their `G(n,p)` probability. -/
theorem sgProb_graphEvent (n : ℕ) (p : ℝ) (A : Set (SimpleGraph (Fin n))) :
    sgProb n p {GJ | GJ.1 ∈ A} = erProb n p A :=
  ERZeroFreeness.sgProb_fst n p A

/-- [SG.5] -/
theorem sgProb_inter_ge {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A B : Set (SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool))) :
    sgProb n p A + sgProb n p B - 1 ≤ sgProb n p (A ∩ B) := by
  have h1 := ERZeroFreeness.sgProb_compl (n := n) (p := p) (A ∩ B)
  have h2 := ERZeroFreeness.sgProb_union_le hp0 hp1 Aᶜ Bᶜ
  have h3 := ERZeroFreeness.sgProb_compl (n := n) (p := p) A
  have h4 := ERZeroFreeness.sgProb_compl (n := n) (p := p) B
  rw [Set.compl_inter] at h1
  linarith

/-- For `n ≥ ⌈d⌉`, the edge probability `d / n` lies in `[0, 1]`. -/
private lemma CountSgModel_eventually_mem_Icc {d : ℝ} (hd : 0 ≤ d) :
    ∀ᶠ n : ℕ in atTop, 0 ≤ d / (n : ℝ) ∧ d / (n : ℝ) ≤ 1 := by
  filter_upwards [eventually_ge_atTop ⌈d⌉₊] with n hn
  exact div_natCast_mem_Icc hd ((Nat.le_ceil d).trans (by exact_mod_cast hn))

/-- [SG.6] The intersection of two events of probability tending to one. -/
theorem tendsto_sgProb_inter {d : ℝ} (hd : 0 < d)
    {A B : (n : ℕ) → Set (SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool))}
    (hA : Tendsto (fun n : ℕ => sgProb n (d / n) (A n)) atTop (𝓝 1))
    (hB : Tendsto (fun n : ℕ => sgProb n (d / n) (B n)) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => sgProb n (d / n) (A n ∩ B n)) atTop (𝓝 1) := by
  have hlow : Tendsto (fun n : ℕ => sgProb n (d / n) (A n) + sgProb n (d / n) (B n) - 1)
      atTop (𝓝 1) := by
    have h := (hA.add hB).sub_const 1
    rwa [show (1 : ℝ) + 1 - 1 = 1 by norm_num] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [CountSgModel_eventually_mem_Icc hd.le] with n hn
    exact sgProb_inter_ge hn.1 hn.2 (A n) (B n)
  · filter_upwards [CountSgModel_eventually_mem_Icc hd.le] with n hn
    exact sgProb_le_one hn.1 hn.2 (A n ∩ B n)

/-- [SG.7] An event containing an event of probability tending to one. -/
theorem tendsto_sgProb_of_subset {d : ℝ} (hd : 0 < d)
    {A B : (n : ℕ) → Set (SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool))} (hAB : ∀ n, A n ⊆ B n)
    (hA : Tendsto (fun n : ℕ => sgProb n (d / n) (A n)) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => sgProb n (d / n) (B n)) atTop (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hA tendsto_const_nhds ?_ ?_
  · filter_upwards [CountSgModel_eventually_mem_Icc hd.le] with n hn
    exact sgProb_mono hn.1 hn.2 (hAB n)
  · filter_upwards [CountSgModel_eventually_mem_Icc hd.le] with n hn
    exact sgProb_le_one hn.1 hn.2 (B n)

end Count

end CountSgModel

end

end ERZeroFreeness
