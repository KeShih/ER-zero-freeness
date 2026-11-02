/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.CKDefs
import ERZeroFreeness.CKAnalysis
import ERZeroFreeness.CKInfo
import ERZeroFreeness.RSPoisPi
import ERZeroFreeness.RSModel
import ERZeroFreeness.RSBetheBasic
import ERZeroFreeness.RSPoisSplit
import ERZeroFreeness.Poisson

/-!
# Proof of [CKPZ, Prop. 3.6]: Bernoulli sets (Lemma 1.3) and pinning (Lemma 6.1)

Part of the self-contained proof of `CKPZProp36 q`, the Potts case of the planted free-energy
bound of Coja-Oghlan, Krzakala, Perkins and Zdeborová [CKPZ, Prop. 3.6], which Lemma C.3
(`lem:rs-ckpz`) cites.  Appendix C is formalized in two layers: the `RS*` modules prove
Theorem C.1 from `CKPZProp36 q` as an explicit hypothesis, and the `CK*` modules prove
`CKPZProp36 q`.  Lemma numbers refer to `docs/ckpz-proof.md`.

A random set `U ∼ Bern(π)^V` on `V = Fin n` enters through its weight
`ckBern π U = ∏_{v ∈ U} π ∏_{v ∉ U} (1 - π)`, so expectations are finite sums over subsets.

* Basic facts: `ck_bern_sum`, `ck_bern_nonneg`, `ck_bern_zero` and `ck_bern_card` (`E|U| = nπ`).
* Lemma 1.3: union (`ck_bern_union`), insertion (`ck_bern_insert`) and the lower bound
  `E[1_{v ∈ W} / |W ∖ {u}|] ≥ p/(1 + np)` (`ck_bern_inv_card`).
* `ck_poisPi_support`: for i.i.d. `Pois(λ)` counts `D`, the set `{v : D_v ≥ 1}` is
  `Bern(1 - e^{-λ})^V`.
* Lemma 6.1, pinning by entropy telescoping: `ck_pinning_J` (part (a)) and `ck_pinning_pairs`
  (part (b)).
-/

open Filter Topology MeasureTheory

namespace ERZeroFreeness

open scoped Classical

noncomputable section


/-! ### Bernoulli random sets (Lemma 1.3) -/

/-- `∑_U ∏_v (U ∋ v ? f v : g v) = ∏_v (f v + g v)`. -/
private lemma CKBernA_sum_prod_ite {n : ℕ} (f g : Fin n → ℝ) :
    ∑ U : Finset (Fin n), ∏ v, (if v ∈ U then f v else g v) = ∏ v, (f v + g v) := by
  rw [Fintype.prod_add]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [Finset.prod_ite]
  congr 1
  · congr 1; ext x; simp
  · congr 1; ext x; simp

/-- Prop-indexed version of `CKBernA_sum_prod_ite`. -/
private lemma CKBernA_sum_prod_prop {n : ℕ} (h : Fin n → Prop → ℝ) :
    ∑ U : Finset (Fin n), ∏ v, h v (v ∈ U) = ∏ v, (h v True + h v False) := by
  rw [← CKBernA_sum_prod_ite]
  refine Finset.sum_congr rfl fun U _ => Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : v ∈ U <;> simp [hv]

/-- Two-set version: `∑_A ∑_W ∏_v h_v(v ∈ A, v ∈ W) = ∏_v ∑_{x,y} h_v(x, y)`. -/
private lemma CKBernA_sum_sum_prod_prop {n : ℕ} (h : Fin n → Prop → Prop → ℝ) :
    ∑ A : Finset (Fin n), ∑ W : Finset (Fin n), ∏ v, h v (v ∈ A) (v ∈ W) =
      ∏ v, (h v True True + h v True False + (h v False True + h v False False)) := by
  have h1 : ∀ A : Finset (Fin n), ∑ W : Finset (Fin n), ∏ v, h v (v ∈ A) (v ∈ W) =
      ∏ v, (h v (v ∈ A) True + h v (v ∈ A) False) := fun A =>
    CKBernA_sum_prod_prop (fun v y => h v (v ∈ A) y)
  simp_rw [h1]
  exact CKBernA_sum_prod_prop (fun v x => h v x True + h v x False)

/-- `E_π ∏_v (v ∈ U ? φ v : ψ v) = ∏_v (π φ v + (1 - π) ψ v)`. -/
private lemma CKBernA_sum_mul_prod {n : ℕ} (π : ℝ) (φ ψ : Fin n → ℝ) :
    ∑ U : Finset (Fin n), ckBern π U * ∏ v, (if v ∈ U then φ v else ψ v) =
      ∏ v, (π * φ v + (1 - π) * ψ v) := by
  rw [← CKBernA_sum_prod_ite]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [ckBern, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : v ∈ U <;> simp [hv]

/-- `P_π(S ⊆ U) = π^{|S|}`. -/
private lemma CKBernA_subset {n : ℕ} (π : ℝ) (S : Finset (Fin n)) :
    ∑ U : Finset (Fin n), ckBern π U * (if S ⊆ U then 1 else 0) = π ^ S.card := by
  have hind : ∀ U : Finset (Fin n), (if S ⊆ U then (1 : ℝ) else 0) =
      ∏ v, (if v ∈ U then (1 : ℝ) else (if v ∈ S then 0 else 1)) := by
    intro U
    by_cases hSU : S ⊆ U
    · rw [if_pos hSU]
      refine (Finset.prod_eq_one fun v _ => ?_).symm
      by_cases hv : v ∈ U
      · rw [if_pos hv]
      · rw [if_neg hv, if_neg fun hvS => hv (hSU hvS)]
    · rw [if_neg hSU]
      obtain ⟨v, hvS, hvU⟩ := Finset.not_subset.mp hSU
      refine (Finset.prod_eq_zero (Finset.mem_univ v) ?_).symm
      rw [if_neg hvU, if_pos hvS]
  simp_rw [hind]
  rw [CKBernA_sum_mul_prod]
  have : ∀ v : Fin n, π * 1 + (1 - π) * (if v ∈ S then (0 : ℝ) else 1) =
      if v ∈ S then π else 1 := by
    intro v; by_cases hv : v ∈ S <;> simp [hv]
  simp_rw [this]
  rw [Fintype.prod_ite_mem, Finset.prod_const]

/-- `P_π(v ∈ U) = π`. -/
private lemma CKBernA_mem {n : ℕ} (π : ℝ) (v : Fin n) :
    ∑ U : Finset (Fin n), ckBern π U * (if v ∈ U then 1 else 0) = π := by
  have h := CKBernA_subset π {v}
  simp only [Finset.singleton_subset_iff, Finset.card_singleton, pow_one] at h
  exact h

/-- `|U| = ∑_v 1_{v ∈ U}` in `ℝ`. -/
private lemma CKBernA_card_eq_sum {n : ℕ} (U : Finset (Fin n)) :
    (U.card : ℝ) = ∑ v, (if v ∈ U then (1 : ℝ) else 0) := by
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The weights `B_π(U)` sum to `1`, for every real `π`. -/
theorem ck_bern_sum {n : ℕ} (π : ℝ) : ∑ U : Finset (Fin n), ckBern π U = 1 := by
  have h := CKBernA_sum_mul_prod (n := n) π (fun _ => 1) (fun _ => 1)
  simp only [ite_self, Finset.prod_const_one, mul_one, add_sub_cancel] at h
  exact h

/-- `B_π(U) ≥ 0` for `π ∈ [0, 1]`. -/
theorem ck_bern_nonneg {n : ℕ} {π : ℝ} (h0 : 0 ≤ π) (h1 : π ≤ 1) (U : Finset (Fin n)) :
    0 ≤ ckBern π U :=
  Finset.prod_nonneg fun v _ => by
    by_cases hv : v ∈ U
    · rw [if_pos hv]; exact h0
    · rw [if_neg hv]; linarith

/-- For `π = 0` the random set is empty: `B_0(U) = 1_{U = ∅}`. -/
theorem ck_bern_zero {n : ℕ} (U : Finset (Fin n)) : ckBern 0 U = if U = ∅ then 1 else 0 := by
  by_cases hU : U = ∅
  · subst hU
    rw [if_pos rfl, ckBern]
    exact Finset.prod_eq_one fun v _ => by simp
  · rw [if_neg hU, ckBern]
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hU
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by rw [if_pos hv])

/-- `E|U| = nπ` for `U ∼ Bern(π)^V`, `|V| = n`. -/
theorem ck_bern_card {n : ℕ} (π : ℝ) :
    ∑ U : Finset (Fin n), ckBern π U * U.card = n * π := by
  simp_rw [CKBernA_card_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [CKBernA_mem]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `P(A ∪ W = U) = B_c(U)` with `c = 1 - (1 - a)(1 - b)`, for independent `A ∼ Bern(a)` and
`W ∼ Bern(b)`. -/
private lemma CKBernA_union_weight {n : ℕ} (a b : ℝ) (U : Finset (Fin n)) :
    ∑ A : Finset (Fin n), ∑ W : Finset (Fin n),
      ckBern a A * ckBern b W * (if A ∪ W = U then 1 else 0) =
      ckBern (1 - (1 - a) * (1 - b)) U := by
  have hind : ∀ A W : Finset (Fin n), (if A ∪ W = U then (1 : ℝ) else 0) =
      ∏ v, (if (v ∈ A ∨ v ∈ W ↔ v ∈ U) then (1 : ℝ) else 0) := by
    intro A W
    by_cases hAW : A ∪ W = U
    · rw [if_pos hAW]
      refine (Finset.prod_eq_one fun v _ => ?_).symm
      rw [if_pos (by rw [← hAW, Finset.mem_union])]
    · rw [if_neg hAW]
      have : ∃ v, ¬ (v ∈ A ∨ v ∈ W ↔ v ∈ U) := by
        by_contra hne
        push Not at hne
        exact hAW (Finset.ext fun v => by rw [Finset.mem_union]; exact hne v)
      obtain ⟨v, hv⟩ := this
      exact (Finset.prod_eq_zero (Finset.mem_univ v) (by rw [if_neg hv])).symm
  set h : Fin n → Prop → Prop → ℝ := fun v x y => (if x then a else 1 - a) *
    (if y then b else 1 - b) * (if (x ∨ y ↔ v ∈ U) then (1 : ℝ) else 0) with hh
  have hpt : ∀ A W : Finset (Fin n),
      ckBern a A * ckBern b W * (if A ∪ W = U then 1 else 0) = ∏ v, h v (v ∈ A) (v ∈ W) := by
    intro A W
    rw [hind, ckBern, ckBern, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [hh]
    by_cases hA : v ∈ A <;> by_cases hW : v ∈ W <;> simp [hA, hW]
  calc ∑ A : Finset (Fin n), ∑ W : Finset (Fin n),
        ckBern a A * ckBern b W * (if A ∪ W = U then 1 else 0)
      = ∑ A : Finset (Fin n), ∑ W : Finset (Fin n), ∏ v, h v (v ∈ A) (v ∈ W) :=
        Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun W _ => hpt A W
    _ = ∏ v, (h v True True + h v True False + (h v False True + h v False False)) :=
        CKBernA_sum_sum_prod_prop h
    _ = ckBern (1 - (1 - a) * (1 - b)) U := by
        rw [ckBern]
        refine Finset.prod_congr rfl fun v _ => ?_
        rw [hh]
        by_cases hU : v ∈ U
        · simp only [hU, if_true, if_false, true_or, or_true, or_self, iff_true, iff_self,
            mul_one, mul_zero, add_zero]
          ring
        · simp only [hU, if_true, if_false, true_or, or_true, or_self, iff_false, iff_self,
            not_true_eq_false, mul_one, mul_zero, zero_add]
          ring

/-- Lemma 1.3(a): for independent `A ∼ Bern(a)^V` and `W ∼ Bern(b)^V`,
`A ∪ W ∼ Bern(1 - (1 - a)(1 - b))^V`.  This is a polynomial identity, valid for all real `a`,
`b`. -/
theorem ck_bern_union {n : ℕ} (a b : ℝ) (f : Finset (Fin n) → ℝ) :
    ∑ A : Finset (Fin n), ∑ W : Finset (Fin n), ckBern a A * ckBern b W * f (A ∪ W) =
      ∑ U : Finset (Fin n), ckBern (1 - (1 - a) * (1 - b)) U * f U := by
  have hf : ∀ A W : Finset (Fin n), ckBern a A * ckBern b W * f (A ∪ W) =
      ∑ U : Finset (Fin n), ckBern a A * ckBern b W * (if A ∪ W = U then 1 else 0) * f U := by
    intro A W
    rw [Finset.sum_eq_single (A ∪ W)]
    · rw [if_pos rfl, mul_one]
    · intro U _ hU
      rw [if_neg (Ne.symm hU), mul_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  calc ∑ A : Finset (Fin n), ∑ W : Finset (Fin n), ckBern a A * ckBern b W * f (A ∪ W)
      = ∑ A : Finset (Fin n), ∑ W : Finset (Fin n), ∑ U : Finset (Fin n),
          ckBern a A * ckBern b W * (if A ∪ W = U then 1 else 0) * f U :=
        Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun W _ => hf A W
    _ = ∑ A : Finset (Fin n), ∑ U : Finset (Fin n), ∑ W : Finset (Fin n),
          ckBern a A * ckBern b W * (if A ∪ W = U then 1 else 0) * f U :=
        Finset.sum_congr rfl fun A _ => Finset.sum_comm
    _ = ∑ U : Finset (Fin n), ∑ A : Finset (Fin n), ∑ W : Finset (Fin n),
          ckBern a A * ckBern b W * (if A ∪ W = U then 1 else 0) * f U :=
        Finset.sum_comm
    _ = ∑ U : Finset (Fin n), ckBern (1 - (1 - a) * (1 - b)) U * f U := by
        refine Finset.sum_congr rfl fun U _ => ?_
        rw [← CKBernA_union_weight a b U, Finset.sum_mul]
        refine Finset.sum_congr rfl fun A _ => ?_
        rw [Finset.sum_mul]

/-- The toggle involution `W ↦ W △ {w}`. -/
private def CKBernA_toggle {n : ℕ} (w : Fin n) : Finset (Fin n) ≃ Finset (Fin n) where
  toFun W := symmDiff W {w}
  invFun W := symmDiff W {w}
  left_inv _ := symmDiff_symmDiff_cancel_right _ _
  right_inv _ := symmDiff_symmDiff_cancel_right _ _

private lemma CKBernA_toggle_of_mem {n : ℕ} {w : Fin n} {W : Finset (Fin n)} (hw : w ∈ W) :
    CKBernA_toggle w W = W.erase w := by
  ext x
  simp only [CKBernA_toggle, Equiv.coe_fn_mk, Finset.mem_symmDiff, Finset.mem_singleton,
    Finset.mem_erase]
  constructor
  · rintro (⟨hx, hxw⟩ | ⟨rfl, hx⟩)
    · exact ⟨hxw, hx⟩
    · exact absurd hw hx
  · rintro ⟨hxw, hx⟩
    exact Or.inl ⟨hx, hxw⟩

private lemma CKBernA_toggle_of_not_mem {n : ℕ} {w : Fin n} {W : Finset (Fin n)} (hw : w ∉ W) :
    CKBernA_toggle w W = insert w W := by
  ext x
  simp only [CKBernA_toggle, Equiv.coe_fn_mk, Finset.mem_symmDiff, Finset.mem_singleton,
    Finset.mem_insert]
  constructor
  · rintro (⟨hx, _⟩ | ⟨rfl, _⟩)
    · exact Or.inr hx
    · exact Or.inl rfl
  · rintro (rfl | hx)
    · exact Or.inr ⟨rfl, hw⟩
    · refine Or.inl ⟨hx, fun hxw => hw (hxw ▸ hx)⟩

/-- `B_p(W ∪ {w}) (1 - p) = p B_p(W)` for `w ∉ W`. -/
private lemma CKBernA_insert_weight {n : ℕ} (p : ℝ) {w : Fin n} {W : Finset (Fin n)}
    (hw : w ∉ W) : ckBern p (insert w W) * (1 - p) = p * ckBern p W := by
  rw [ckBern, ckBern, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), if_pos (Finset.mem_insert_self w W),
    if_neg hw]
  have : ∏ x ∈ Finset.univ.erase w, (if x ∈ insert w W then p else 1 - p) =
      ∏ x ∈ Finset.univ.erase w, (if x ∈ W then p else 1 - p) := by
    refine Finset.prod_congr rfl fun x hx => ?_
    have hxw : x ≠ w := Finset.ne_of_mem_erase hx
    simp [Finset.mem_insert, hxw]
  rw [this]
  ring

/-- Lemma 1.3(b), insertion: for `p ≠ 1` and `W ∼ Bern(p)^V`,
`E ∑_{w ∈ W} g(w, W ∖ {w}) = p/(1 - p) ∑_w E[1_{w ∉ W} g(w, W)]`. -/
theorem ck_bern_insert {n : ℕ} {p : ℝ} (hp : p ≠ 1) (g : Fin n → Finset (Fin n) → ℝ) :
    ∑ W : Finset (Fin n), ckBern p W * ∑ w ∈ W, g w (W.erase w) =
      p / (1 - p) * ∑ w, ∑ W : Finset (Fin n), ckBern p W * (if w ∈ W then 0 else g w W) := by
  have h1p : (1 - p) ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  have hL : ∀ W : Finset (Fin n), ckBern p W * ∑ w ∈ W, g w (W.erase w) =
      ∑ w, (if w ∈ W then ckBern p W * g w (W.erase w) else 0) := by
    intro W
    rw [Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]
  simp_rw [hL]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← (CKBernA_toggle w).sum_comp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun W _ => ?_
  by_cases hw : w ∈ W
  · rw [CKBernA_toggle_of_mem hw, if_neg (Finset.notMem_erase w W), if_pos hw, mul_zero,
      mul_zero]
  · rw [CKBernA_toggle_of_not_mem hw, if_pos (Finset.mem_insert_self w W), if_neg hw,
      Finset.erase_insert hw]
    have h := CKBernA_insert_weight p hw
    field_simp
    linear_combination g w W * h

/-- `E_p[1_{v ∈ W} |W|] ≤ p + n p²`. -/
private lemma CKBernA_mem_card_le {n : ℕ} (p : ℝ) (v : Fin n) :
    ∑ W : Finset (Fin n), ckBern p W * (if v ∈ W then (W.card : ℝ) else 0) ≤ p + n * p ^ 2 := by
  have h1 : ∀ W : Finset (Fin n), (if v ∈ W then (W.card : ℝ) else 0) =
      ∑ x, (if ({v, x} : Finset (Fin n)) ⊆ W then (1 : ℝ) else 0) := by
    intro W
    by_cases hv : v ∈ W
    · rw [if_pos hv, CKBernA_card_eq_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp [Finset.insert_subset_iff, hv]
    · rw [if_neg hv]
      refine (Finset.sum_eq_zero fun x _ => ?_).symm
      simp [Finset.insert_subset_iff, hv]
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [CKBernA_subset]
  calc ∑ x, p ^ ({v, x} : Finset (Fin n)).card ≤ ∑ x, ((if v = x then p else 0) + p ^ 2) := by
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases hx : v = x
        · subst hx
          rw [Finset.pair_eq_singleton, Finset.card_singleton, pow_one, if_pos rfl]
          nlinarith [sq_nonneg p]
        · rw [Finset.card_pair hx, if_neg hx, zero_add]
    _ = p + n * p ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ v),
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Tangent line of `x ↦ 1/x` at `c`: `2/c - m/c² ≤ 1/x` for `1 ≤ x ≤ m`. -/
private lemma CKBernA_inv_tangent {c x m : ℝ} (hc : 0 < c) (hx : 1 ≤ x) (hxm : x ≤ m) :
    2 / c - m / c ^ 2 ≤ x⁻¹ := by
  have hx0 : 0 < x := by linarith
  have e : 2 / c - x / c ^ 2 = x⁻¹ - (c - x) ^ 2 / (x * c ^ 2) := by
    field_simp
    ring
  have h1 : m / c ^ 2 ≥ x / c ^ 2 := div_le_div_of_nonneg_right hxm (by positivity)
  have h2 : 0 ≤ (c - x) ^ 2 / (x * c ^ 2) := by positivity
  linarith

/-- Lemma 1.3(c): for `n ≥ 2`, `p ∈ (0, 1)`, `u ≠ v` and `W ∼ Bern(p)^V`,
`E[1_{v ∈ W} / |W ∖ {u}|] ≥ p/(1 + np)`.  In place of Jensen's inequality, the proof uses the
tangent line `1/x ≥ 2/c - x/c²` at `c = 1 + np` and `E[1_{v ∈ W} |W|] ≤ p + np²`. -/
theorem ck_bern_inv_card {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {u v : Fin n} (huv : u ≠ v) :
    p / (1 + n * p) ≤
      ∑ W : Finset (Fin n), ckBern p W * (if v ∈ W then (((W.erase u).card : ℝ))⁻¹ else 0) := by
  set c : ℝ := 1 + n * p with hc_def
  have hc : 0 < c := by positivity
  have hpt : ∀ W : Finset (Fin n), 2 / c * (if v ∈ W then 1 else 0) -
      1 / c ^ 2 * (if v ∈ W then (W.card : ℝ) else 0) ≤
      (if v ∈ W then (((W.erase u).card : ℝ))⁻¹ else 0) := by
    intro W
    by_cases hv : v ∈ W
    · simp only [if_pos hv, mul_one]
      have h1 : (1 : ℝ) ≤ (W.erase u).card := by
        have : 0 < (W.erase u).card :=
          Finset.card_pos.mpr ⟨v, Finset.mem_erase.mpr ⟨huv.symm, hv⟩⟩
        exact_mod_cast this
      have h2 : ((W.erase u).card : ℝ) ≤ W.card := by exact_mod_cast Finset.card_erase_le
      have := CKBernA_inv_tangent hc h1 h2
      calc 2 / c - 1 / c ^ 2 * W.card = 2 / c - W.card / c ^ 2 := by ring
        _ ≤ _ := this
    · simp [hv]
  have hB : ∀ W : Finset (Fin n), 0 ≤ ckBern p W := ck_bern_nonneg hp0.le hp1.le
  have hpc : p + n * p ^ 2 = p * c := by rw [hc_def]; ring
  calc p / c = 2 / c * p - 1 / c ^ 2 * (p + n * p ^ 2) := by
        rw [hpc]
        field_simp
        ring
    _ ≤ 2 / c * p - 1 / c ^ 2 * ∑ W, ckBern p W * (if v ∈ W then (W.card : ℝ) else 0) := by
        have := CKBernA_mem_card_le (n := n) p v
        have hc2 : 0 ≤ 1 / c ^ 2 := by positivity
        nlinarith
    _ = ∑ W, ckBern p W * (2 / c * (if v ∈ W then 1 else 0) -
          1 / c ^ 2 * (if v ∈ W then (W.card : ℝ) else 0)) := by
        have e1 := CKBernA_mem p v
        rw [Finset.sum_congr rfl fun W _ => show ckBern p W * (2 / c * (if v ∈ W then 1 else 0) -
            1 / c ^ 2 * (if v ∈ W then (W.card : ℝ) else 0)) =
            2 / c * (ckBern p W * (if v ∈ W then 1 else 0)) -
            1 / c ^ 2 * (ckBern p W * (if v ∈ W then (W.card : ℝ) else 0)) by ring]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e1]
    _ ≤ ∑ W, ckBern p W * (if v ∈ W then (((W.erase u).card : ℝ))⁻¹ else 0) :=
        Finset.sum_le_sum fun W _ => mul_le_mul_of_nonneg_left (hpt W) (hB W)

/-- `1_{S = W} = ∏_v 1_{v ∈ S ↔ v ∈ W}`. -/
private lemma CKBernA_ind_eq_prod {n : ℕ} (S W : Finset (Fin n)) :
    (if S = W then (1 : ℝ) else 0) = ∏ v, (if (v ∈ S ↔ v ∈ W) then (1 : ℝ) else 0) := by
  by_cases hSW : S = W
  · rw [if_pos hSW]
    exact (Finset.prod_eq_one fun v _ => by rw [if_pos (by rw [hSW])]).symm
  · rw [if_neg hSW]
    have : ∃ v, ¬ (v ∈ S ↔ v ∈ W) := by
      by_contra hne
      push Not at hne
      exact hSW (Finset.ext hne)
    obtain ⟨v, hv⟩ := this
    exact (Finset.prod_eq_zero (Finset.mem_univ v) (by rw [if_neg hv])).symm

/-- `E_{Pois(λ)} 1_{k ≠ 0 ↔ P} = (P ? 1 - e^{-λ} : e^{-λ})`. -/
private lemma CKBernA_hasSum_pois_ind {lam : ℝ} (hlam : 0 ≤ lam) (P : Prop) [Decidable P] :
    HasSum (fun k : ℕ => poisPMF lam k * (if (k ≠ 0 ↔ P) then 1 else 0))
      (if P then 1 - Real.exp (-lam) else Real.exp (-lam)) := by
  have h0 : HasSum (fun k : ℕ => poisPMF lam k * (if k = 0 then 1 else 0)) (Real.exp (-lam)) := by
    refine (hasSum_ite_eq 0 (Real.exp (-lam))).congr_fun fun k => ?_
    by_cases hk : k = 0
    · subst hk; simp [poisPMF]
    · simp [hk]
  by_cases hP : P
  · rw [if_pos hP]
    refine ((hasSum_poisPMF hlam).sub h0).congr_fun fun k => ?_
    by_cases hk : k = 0 <;> simp [hk, hP]
  · rw [if_neg hP]
    refine h0.congr_fun fun k => ?_
    by_cases hk : k = 0 <;> simp [hk, hP]

/-- For i.i.d. `Pois(λ)` counts `D` on `V = Fin n`, the set `{v : D_v ≥ 1}` is
`Bern(1 - e^{-λ})^V`: `E f({v : D_v ≠ 0}) = E_{W ∼ Bern(1 - e^{-λ})^V} f(W)`. -/
theorem ck_poisPi_support {n : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) (f : Finset (Fin n) → ℝ) :
    ∑' D : Fin n → ℕ, poisPi (fun _ => lam) D * f (Finset.univ.filter fun v => D v ≠ 0) =
      ∑ W : Finset (Fin n), ckBern (1 - Real.exp (-lam)) W * f W := by
  have hW : ∀ W : Finset (Fin n), HasSum (fun D : Fin n → ℕ => poisPi (fun _ => lam) D *
      (if (Finset.univ.filter fun v => D v ≠ 0) = W then 1 else 0))
      (ckBern (1 - Real.exp (-lam)) W) := by
    intro W
    have H := rs_hasSum_poisPi_mul_prod (lam := fun _ : Fin n => lam) (fun _ => hlam)
      (fun v k => if (k ≠ 0 ↔ v ∈ W) then (1 : ℝ) else 0)
      (fun v k => by positivity)
      (fun v => if v ∈ W then 1 - Real.exp (-lam) else Real.exp (-lam))
      (fun v => CKBernA_hasSum_pois_ind hlam (v ∈ W))
    have hB : ∏ v : Fin n, (if v ∈ W then 1 - Real.exp (-lam) else Real.exp (-lam)) =
        ckBern (1 - Real.exp (-lam)) W := by
      rw [ckBern]
      refine Finset.prod_congr rfl fun v _ => ?_
      by_cases hv : v ∈ W <;> simp [hv]
    rw [hB] at H
    refine H.congr_fun fun D => ?_
    rw [CKBernA_ind_eq_prod]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hsum : HasSum (fun D : Fin n → ℕ => ∑ W : Finset (Fin n), poisPi (fun _ => lam) D *
      (if (Finset.univ.filter fun v => D v ≠ 0) = W then 1 else 0) * f W)
      (∑ W : Finset (Fin n), ckBern (1 - Real.exp (-lam)) W * f W) :=
    hasSum_sum fun W _ => (hW W).mul_right (f W)
  refine (hsum.congr_fun fun D => ?_).tsum_eq
  rw [Finset.sum_eq_single (Finset.univ.filter fun v => D v ≠ 0)]
  · rw [if_pos rfl, mul_one]
  · intro U _ hU
    rw [if_neg (Ne.symm hU), mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### Lemma 6.1: entropy telescoping -/

/-- `𝓗_μ(S) = ∑_w H(τ_w | τ_S)`. -/
private def CKBernA_HH {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ w, (ckH μ ({w} ∪ S) - ckH μ S)

/-- Step 1: `∑_w I(τ_w; τ_W | τ_S) = 𝓗(S) - 𝓗(W ∪ S)`. -/
private lemma CKBernA_HH_step {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) (W S : Finset (Fin n)) :
    ∑ w, ckMI μ {w} W S = CKBernA_HH μ S - CKBernA_HH μ (W ∪ S) := by
  rw [CKBernA_HH, CKBernA_HH, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [ckMI, Finset.union_assoc]
  ring

private lemma CKBernA_HH_nonneg {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (S : Finset (Fin n)) : 0 ≤ CKBernA_HH μ S :=
  Finset.sum_nonneg fun _ _ => sub_nonneg.mpr (ck_H_mono hμ Finset.subset_union_right)

private lemma CKBernA_HH_empty_le {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) :
    CKBernA_HH μ ∅ ≤ n * Real.log q := by
  rw [CKBernA_HH]
  calc ∑ w : Fin n, (ckH μ ({w} ∪ ∅) - ckH μ ∅) ≤ ∑ _w : Fin n, Real.log q := by
        refine Finset.sum_le_sum fun w _ => ?_
        rw [Finset.union_empty, ck_H_empty hμ, sub_zero]
        have := ck_H_le hμ {w}
        rwa [Finset.card_singleton, Nat.cast_one, one_mul] at this
    _ = n * Real.log q := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `E_k = E_{A ∼ Bern(π_k)} 𝓗(A)` with `π_k = 1 - (1 - p)^k`. -/
private def CKBernA_E {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) (p : ℝ) (k : ℕ) : ℝ :=
  ∑ A : Finset (Fin n), ckBern (1 - (1 - p) ^ k) A * CKBernA_HH μ A

/-- Step 2 (one layer): `E_{A_k} E_W ∑_w I(τ_w; τ_W | τ_{A_k}) = E_k - E_{k+1}`. -/
private lemma CKBernA_layer {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) (p : ℝ) (k : ℕ) :
    ∑ A : Finset (Fin n), ckBern (1 - (1 - p) ^ k) A *
      ∑ W : Finset (Fin n), ckBern p W * ∑ w, ckMI μ {w} W A =
      CKBernA_E μ p k - CKBernA_E μ p (k + 1) := by
  have h1 : ∀ A : Finset (Fin n), ckBern (1 - (1 - p) ^ k) A *
      ∑ W : Finset (Fin n), ckBern p W * ∑ w, ckMI μ {w} W A =
      ckBern (1 - (1 - p) ^ k) A * CKBernA_HH μ A -
        ∑ W : Finset (Fin n), ckBern (1 - (1 - p) ^ k) A * ckBern p W * CKBernA_HH μ (A ∪ W) := by
    intro A
    simp_rw [CKBernA_HH_step]
    have hs := ck_bern_sum (n := n) p
    calc ckBern (1 - (1 - p) ^ k) A *
          ∑ W : Finset (Fin n), ckBern p W * (CKBernA_HH μ A - CKBernA_HH μ (W ∪ A))
        = ckBern (1 - (1 - p) ^ k) A * CKBernA_HH μ A * ∑ W : Finset (Fin n), ckBern p W -
          ∑ W : Finset (Fin n), ckBern (1 - (1 - p) ^ k) A * ckBern p W *
            CKBernA_HH μ (A ∪ W) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun W _ => ?_
          rw [Finset.union_comm W A]
          ring
      _ = _ := by rw [hs, mul_one]
  rw [Finset.sum_congr rfl fun A _ => h1 A, Finset.sum_sub_distrib, ck_bern_union]
  have hπ : 1 - (1 - (1 - (1 - p) ^ k)) * (1 - p) = 1 - (1 - p) ^ (k + 1) := by ring
  rw [hπ]
  rfl

/-- Step 2 (summed): `∑_{k<T} E_{A_k} E_W ∑_w I(τ_w; τ_W | τ_{A_k}) ≤ n log q`. -/
private lemma CKBernA_telescope {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (T : ℕ) :
    ∑ k ∈ Finset.range T, ∑ A : Finset (Fin n), ckBern (1 - (1 - p) ^ k) A *
      ∑ W : Finset (Fin n), ckBern p W * ∑ w, ckMI μ {w} W A ≤ n * Real.log q := by
  simp_rw [CKBernA_layer]
  rw [Finset.sum_range_sub']
  have h0 : CKBernA_E μ p 0 = CKBernA_HH μ ∅ := by
    rw [CKBernA_E, pow_zero, sub_self]
    simp_rw [ck_bern_zero]
    rw [Finset.sum_eq_single ∅]
    · rw [if_pos rfl, one_mul]
    · intro U _ hU
      rw [if_neg hU, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hT : 0 ≤ CKBernA_E μ p T := by
    refine Finset.sum_nonneg fun A _ => mul_nonneg (ck_bern_nonneg ?_ ?_ A) (CKBernA_HH_nonneg hμ A)
    · have : (1 - p) ^ T ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      linarith
    · have : 0 ≤ (1 - p) ^ T := pow_nonneg (by linarith) T
      linarith
  have := CKBernA_HH_empty_le hμ
  linarith

/-- Lemma 6.1(a) for one `A`: `E_W 𝒥(W | A) ≤ p/(1-p) E_W ∑_w I(τ_w; τ_W | τ_A)`. -/
private lemma CKBernA_J_le {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p < 1) (A : Finset (Fin n)) :
    ∑ W : Finset (Fin n), ckBern p W * ckJ μ W A ≤
      p / (1 - p) * ∑ W : Finset (Fin n), ckBern p W * ∑ w, ckMI μ {w} W A := by
  have hins := ck_bern_insert hp1.ne (fun w W' => ckMI μ {w} W' A)
  simp only [ckJ]
  rw [hins]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hp0 (by linarith))
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun W _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left ?_ (ck_bern_nonneg hp0 hp1.le W)
  split_ifs
  · exact ck_MI_nonneg hμ _ _ _
  · exact le_rfl

/-- Lemma 6.1(a): with `π_k = 1 - (1 - p)^k` and independent `A_k ∼ Bern(π_k)^V`,
`W ∼ Bern(p)^V`, `T⁻¹ ∑_{k<T} E 𝒥_μ(W | A_k) ≤ p/(1 - p) · n log q / T`. -/
theorem ck_pinning_J {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) {T : ℕ} (hT : 1 ≤ T) :
    (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, ∑ A : Finset (Fin n), ckBern (1 - (1 - p) ^ k) A *
      ∑ W : Finset (Fin n), ckBern p W * ckJ μ W A ≤ p / (1 - p) * (n * Real.log q) / T := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hπ : ∀ k : ℕ, 0 ≤ 1 - (1 - p) ^ k ∧ 1 - (1 - p) ^ k ≤ 1 := by
    intro k
    have h1 : (1 - p) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have h2 : 0 ≤ (1 - p) ^ k := pow_nonneg (by linarith) k
    constructor <;> linarith
  have hpp : 0 ≤ p / (1 - p) := div_nonneg hp0.le (by linarith)
  have key : ∑ k ∈ Finset.range T, ∑ A : Finset (Fin n), ckBern (1 - (1 - p) ^ k) A *
      ∑ W : Finset (Fin n), ckBern p W * ckJ μ W A ≤ p / (1 - p) * (n * Real.log q) := by
    calc ∑ k ∈ Finset.range T, ∑ A : Finset (Fin n), ckBern (1 - (1 - p) ^ k) A *
          ∑ W : Finset (Fin n), ckBern p W * ckJ μ W A
        ≤ ∑ k ∈ Finset.range T, ∑ A : Finset (Fin n), ckBern (1 - (1 - p) ^ k) A *
          (p / (1 - p) * ∑ W : Finset (Fin n), ckBern p W * ∑ w, ckMI μ {w} W A) := by
          refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun A _ => ?_
          exact mul_le_mul_of_nonneg_left (CKBernA_J_le hμ hp0.le hp1 A)
            (ck_bern_nonneg (hπ k).1 (hπ k).2 A)
      _ = p / (1 - p) * ∑ k ∈ Finset.range T, ∑ A : Finset (Fin n),
          ckBern (1 - (1 - p) ^ k) A *
            ∑ W : Finset (Fin n), ckBern p W * ∑ w, ckMI μ {w} W A := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun A _ => ?_
          ring
      _ ≤ p / (1 - p) * (n * Real.log q) :=
          mul_le_mul_of_nonneg_left (CKBernA_telescope hμ hp0.le hp1.le T) hpp
  calc (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, ∑ A : Finset (Fin n), ckBern (1 - (1 - p) ^ k) A *
        ∑ W : Finset (Fin n), ckBern p W * ckJ μ W A
      ≤ (T : ℝ)⁻¹ * (p / (1 - p) * (n * Real.log q)) :=
        mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hT'.le)
    _ = p / (1 - p) * (n * Real.log q) / T := by ring

/-- `∑_{v ∈ W∖u} I(τ_u; τ_v | τ_S)/|W∖u| ≤ I(τ_u; τ_W | τ_S)`. -/
private lemma CKBernA_avg_le {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (S : Finset (Fin n)) (u : Fin n) (W : Finset (Fin n)) :
    ∑ v ∈ Finset.univ.erase u, (if v ∈ W then (((W.erase u).card : ℝ))⁻¹ else 0) *
      ckMI μ {u} {v} S ≤ ckMI μ {u} W S := by
  have hI := ck_MI_nonneg hμ {u} W S
  calc ∑ v ∈ Finset.univ.erase u, (if v ∈ W then (((W.erase u).card : ℝ))⁻¹ else 0) *
        ckMI μ {u} {v} S
      ≤ ∑ v ∈ Finset.univ.erase u, (if v ∈ W then (((W.erase u).card : ℝ))⁻¹ else 0) *
        ckMI μ {u} W S := by
        refine Finset.sum_le_sum fun v _ => ?_
        by_cases hv : v ∈ W
        · rw [if_pos hv]
          exact mul_le_mul_of_nonneg_left
            (ck_MI_mono hμ {u} (Finset.singleton_subset_iff.mpr hv) S)
            (inv_nonneg.mpr (Nat.cast_nonneg _))
        · rw [if_neg hv, zero_mul, zero_mul]
    _ = ((W.erase u).card : ℝ) * ((W.erase u).card : ℝ)⁻¹ * ckMI μ {u} W S := by
        rw [← Finset.sum_mul, Finset.sum_ite_mem]
        have : Finset.univ.erase u ∩ W = W.erase u := by
          ext x
          simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true]
        rw [this, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ckMI μ {u} W S := by
        rcases Nat.eq_zero_or_pos (W.erase u).card with h0 | hpos
        · rw [h0, Nat.cast_zero, zero_mul, zero_mul]
          exact hI
        · have : ((W.erase u).card : ℝ) ≠ 0 := by positivity
          rw [mul_inv_cancel₀ this, one_mul]

/-- Lemma 6.1(b) for fixed `S` and `u`:
`p/(1 + np) ∑_{v ≠ u} I(τ_u; τ_v | τ_S) ≤ E_W I(τ_u; τ_W | τ_S)`. -/
private lemma CKBernA_pair_le {n q : ℕ} (hn : 2 ≤ n) {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (S : Finset (Fin n)) (u : Fin n) :
    p / (1 + n * p) * ∑ v ∈ Finset.univ.erase u, ckMI μ {u} {v} S ≤
      ∑ W : Finset (Fin n), ckBern p W * ckMI μ {u} W S := by
  rw [Finset.mul_sum]
  calc ∑ v ∈ Finset.univ.erase u, p / (1 + n * p) * ckMI μ {u} {v} S
      ≤ ∑ v ∈ Finset.univ.erase u, (∑ W : Finset (Fin n),
          ckBern p W * (if v ∈ W then (((W.erase u).card : ℝ))⁻¹ else 0)) *
          ckMI μ {u} {v} S := by
        refine Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_right ?_ (ck_MI_nonneg hμ _ _ _)
        exact ck_bern_inv_card hn hp0 hp1 (Finset.ne_of_mem_erase hv).symm
    _ = ∑ W : Finset (Fin n), ckBern p W * ∑ v ∈ Finset.univ.erase u,
          (if v ∈ W then (((W.erase u).card : ℝ))⁻¹ else 0) * ckMI μ {u} {v} S := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun W _ => Finset.sum_congr rfl fun v _ => by ring
    _ ≤ ∑ W : Finset (Fin n), ckBern p W * ckMI μ {u} W S := by
        refine Finset.sum_le_sum fun W _ =>
          mul_le_mul_of_nonneg_left ?_ (ck_bern_nonneg hp0.le hp1.le W)
        exact CKBernA_avg_le hμ S u W

/-- Lemma 6.1(b): for `n ≥ 2`, with `A_k` as in `ck_pinning_J`,
`T⁻¹ ∑_{k<T} E ∑_{u ≠ v} I_μ(τ_u; τ_v | τ_{A_k}) ≤ (1 + np)/p · n log q / T`. -/
theorem ck_pinning_pairs {n q : ℕ} (hn : 2 ≤ n) {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {T : ℕ} (hT : 1 ≤ T) :
    (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, ∑ A : Finset (Fin n), ckBern (1 - (1 - p) ^ k) A *
      ∑ u, ∑ v ∈ Finset.univ.erase u, ckMI μ {u} {v} A ≤
        (1 + n * p) / p * (n * Real.log q) / T := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hπ : ∀ k : ℕ, 0 ≤ 1 - (1 - p) ^ k ∧ 1 - (1 - p) ^ k ≤ 1 := by
    intro k
    have h1 : (1 - p) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have h2 : 0 ≤ (1 - p) ^ k := pow_nonneg (by linarith) k
    constructor <;> linarith
  set X := ∑ k ∈ Finset.range T, ∑ A : Finset (Fin n), ckBern (1 - (1 - p) ^ k) A *
      ∑ u, ∑ v ∈ Finset.univ.erase u, ckMI μ {u} {v} A with hX_def
  have hX : p / (1 + n * p) * X ≤ n * Real.log q := by
    calc p / (1 + n * p) * X
        = ∑ k ∈ Finset.range T, ∑ A : Finset (Fin n), ckBern (1 - (1 - p) ^ k) A *
            ∑ u, p / (1 + n * p) * ∑ v ∈ Finset.univ.erase u, ckMI μ {u} {v} A := by
          rw [hX_def, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun A _ => ?_
          rw [← Finset.mul_sum]
          ring
      _ ≤ ∑ k ∈ Finset.range T, ∑ A : Finset (Fin n), ckBern (1 - (1 - p) ^ k) A *
            ∑ u, ∑ W : Finset (Fin n), ckBern p W * ckMI μ {u} W A := by
          refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun A _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (ck_bern_nonneg (hπ k).1 (hπ k).2 A)
          exact Finset.sum_le_sum fun u _ => CKBernA_pair_le hn hμ hp0 hp1 A u
      _ = ∑ k ∈ Finset.range T, ∑ A : Finset (Fin n), ckBern (1 - (1 - p) ^ k) A *
            ∑ W : Finset (Fin n), ckBern p W * ∑ w, ckMI μ {w} W A := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun A _ => ?_
          rw [Finset.sum_comm]
          simp_rw [Finset.mul_sum]
      _ ≤ n * Real.log q := CKBernA_telescope hμ hp0.le hp1.le T
  have hc : 0 < p / (1 + n * p) := by positivity
  have hX' : X ≤ (1 + n * p) / p * (n * Real.log q) := by
    have e : X = (1 + n * p) / p * (p / (1 + n * p) * X) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hX (by positivity)
  calc (T : ℝ)⁻¹ * X ≤ (T : ℝ)⁻¹ * ((1 + n * p) / p * (n * Real.log q)) :=
        mul_le_mul_of_nonneg_left hX' (inv_nonneg.mpr hT'.le)
    _ = (1 + n * p) / p * (n * Real.log q) / T := by ring

end

end ERZeroFreeness
