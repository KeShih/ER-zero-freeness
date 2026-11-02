/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSDefs
import ERZeroFreeness.Multinomial

/-!
# Appendix C: unbalanced colourings and pairs are exponentially rare

Relative-entropy counting, in place of the two uses of Hoeffding's inequality in the proof of
Lemma C.7 (`lem:rs-anchor`: the case `x = 1`, and Step 4):

* `rs_card_devSq_le`: `#{σ ∈ [q]^n : ‖α(σ) - u‖² ≥ ε} ≤ K q^n e^{-rn}`;
* `rs_card_ovDev_le`: `#{(σ,τ) : ‖R_{σ,τ} - R̄‖_F² ≥ ε} ≤ K q^{2n} e^{-rn}`;

for some rate `r ∈ (0,1]` and constant `K ≥ 0` depending only on `q` and `ε`.

**Deviation from the paper.**  The paper's explicit Hoeffding rates (`η²/q²`, `η²/(8q)`) are
replaced by rates that are only shown to exist; this changes the constants `γ_1`, `c_1` of
Lemma C.7 only numerically.

## Proof

By `exists_empKL_ge_of_not_balanced`, colourings outside the balanced window `balanced q n δ` have
`empKL ≥ κ > 0`; by `exists_sum_exp_empKL_le` with `θ = 1/2`, `∑_σ e^{(n/2) empKL(σ)} ≤ C q^n`, so
`#(unbalanced) · e^{nκ/2} ≤ C q^n` (`rsc_card_unbalanced`).  For `devSq`: on the balanced window
`‖α - u‖² ≤ qδ²`, and `δ = min 1 (ε/(2q))` gives `qδ² < ε` (`rsc_delta`).  For pairs, the same
argument applies to the pair map `v ↦ finProdFinEquiv (σ_v, τ_v) ∈ Fin (q·q)` (injective in
`(σ,τ)`), whose colour fractions are the overlap entries `R_{ab}`, with `δ = min 1 (ε/(2q²))`, so
that `q²δ² < ε`.  The rate is `r = min κ 1`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-! ### Unbalanced colourings are exponentially rare -/

/-- `#{σ ∉ 𝓑_n} ≤ C q^n e^{-κ n}` with `C ≥ 0`, from `exists_empKL_ge_of_not_balanced` and
`exists_sum_exp_empKL_le` with `θ = 1/2`. -/
private lemma rsc_card_unbalanced {q : ℕ} (hq : 2 ≤ q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ κ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      ((Finset.univ \ balanced q n δ).card : ℝ) ≤ C * (q : ℝ) ^ n * Real.exp (-(κ * n)) := by
  obtain ⟨κ', hκ', hbal⟩ := exists_empKL_ge_of_not_balanced hq hδ
  obtain ⟨C, hC⟩ := exists_sum_exp_empKL_le (θ := 1 / 2) (by norm_num) (by norm_num) q
  refine ⟨κ' / 2, by positivity, max C 0, le_max_right _ _, fun n hn => ?_⟩
  have hsum := hC (Fin n) (Fin q) (Fintype.card_fin q)
  rw [Fintype.card_fin] at hsum
  have hsum' : ∑ f : Fin n → Fin q, Real.exp (1 / 2 * (n : ℝ) * empKL f) ≤ C * (q : ℝ) ^ n :=
    by convert hsum using 3
  have hlow : ((Finset.univ \ balanced q n δ).card : ℝ) * Real.exp (κ' / 2 * n) ≤
      ∑ f : Fin n → Fin q, Real.exp (1 / 2 * (n : ℝ) * empKL f) := by
    calc ((Finset.univ \ balanced q n δ).card : ℝ) * Real.exp (κ' / 2 * n)
        = ∑ σ ∈ Finset.univ \ balanced q n δ, Real.exp (κ' / 2 * n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ σ ∈ Finset.univ \ balanced q n δ, Real.exp (1 / 2 * (n : ℝ) * empKL σ) := by
          refine Finset.sum_le_sum fun σ hσ => ?_
          have h := hbal n hn σ (Finset.mem_sdiff.mp hσ).2
          apply Real.exp_le_exp.mpr
          have hn' : (0 : ℝ) ≤ n := by positivity
          nlinarith
      _ ≤ ∑ f : Fin n → Fin q, Real.exp (1 / 2 * (n : ℝ) * empKL f) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => (Real.exp_pos _).le)
  have hexp : Real.exp (κ' / 2 * n) * Real.exp (-(κ' / 2 * n)) = 1 := by
    rw [← Real.exp_add, ← Real.exp_zero]
    congr 1
    ring
  calc ((Finset.univ \ balanced q n δ).card : ℝ)
      = ((Finset.univ \ balanced q n δ).card : ℝ) * Real.exp (κ' / 2 * n) *
          Real.exp (-(κ' / 2 * n)) := by rw [mul_assoc, hexp, mul_one]
    _ ≤ C * (q : ℝ) ^ n * Real.exp (-(κ' / 2 * n)) :=
        mul_le_mul_of_nonneg_right (hlow.trans hsum') (Real.exp_pos _).le
    _ ≤ max C 0 * (q : ℝ) ^ n * Real.exp (-(κ' / 2 * n)) := by
        gcongr
        exact le_max_left _ _

/-- Lowering the rate `κ` to `min κ 1` only weakens the bound. -/
private lemma rsc_exp_le_min (κ : ℝ) (n : ℕ) :
    Real.exp (-(κ * n)) ≤ Real.exp (-(min κ 1 * n)) := by
  apply Real.exp_le_exp.mpr
  have : min κ 1 * (n : ℝ) ≤ κ * n :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)
  linarith

/-- The window width `δ = min 1 (ε/(2m))` satisfies `δ > 0` and `m δ² < ε`. -/
private lemma rsc_delta {m ε : ℝ} (hm : 0 < m) (hε : 0 < ε) :
    0 < min 1 (ε / (2 * m)) ∧ m * (min 1 (ε / (2 * m))) ^ 2 < ε := by
  have hδ0 : 0 < min 1 (ε / (2 * m)) := lt_min one_pos (by positivity)
  refine ⟨hδ0, ?_⟩
  have h1 : min 1 (ε / (2 * m)) ≤ 1 := min_le_left _ _
  have h2 : min 1 (ε / (2 * m)) ≤ ε / (2 * m) := min_le_right _ _
  have h3 : (min 1 (ε / (2 * m))) ^ 2 ≤ ε / (2 * m) := by nlinarith
  have h4 : m * (ε / (2 * m)) = ε / 2 := by field_simp
  calc m * (min 1 (ε / (2 * m))) ^ 2 ≤ m * (ε / (2 * m)) :=
        mul_le_mul_of_nonneg_left h3 hm.le
    _ = ε / 2 := h4
    _ < ε := by linarith

/-! ### Colourings: `‖α(σ) - u‖²` -/

/-- On the balanced window, `‖α(σ) - u‖² ≤ q δ²`. -/
private lemma rsc_devSq_le_of_balanced {n q : ℕ} {δ : ℝ} {σ : Fin n → Fin q}
    (hb : σ ∈ balanced q n δ) : rsDevSq σ ≤ q * δ ^ 2 := by
  simp only [balanced, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  unfold rsDevSq
  calc ∑ a, (colorFrac σ a - 1 / (q : ℝ)) ^ 2 ≤ ∑ _a : Fin q, δ ^ 2 :=
        Finset.sum_le_sum fun a _ => by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hb a) 2
    _ = q * δ ^ 2 := by simp

/-- Colourings with `‖α(σ) - u‖² ≥ ε` are exponentially rare. -/
theorem rs_card_devSq_le {q : ℕ} (hq : 2 ≤ q) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, r ≤ 1 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 0 < n →
      ((Finset.univ.filter fun σ : Fin n → Fin q => ε ≤ rsDevSq σ).card : ℝ) ≤
        K * (q : ℝ) ^ n * Real.exp (-(r * n)) := by
  have hq0 : (0 : ℝ) < q := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  obtain ⟨hδ0, hδε⟩ := rsc_delta hq0 hε
  set δ := min 1 (ε / (2 * (q : ℝ))) with hδ
  obtain ⟨κ, hκ, C, hC0, hC⟩ := rsc_card_unbalanced hq hδ0
  refine ⟨min κ 1, lt_min hκ one_pos, min_le_right _ _, C, hC0, fun n hn => ?_⟩
  have hsub : (Finset.univ.filter fun σ : Fin n → Fin q => ε ≤ rsDevSq σ) ⊆
      Finset.univ \ balanced q n δ := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hb => ?_⟩
    have := rsc_devSq_le_of_balanced hb
    linarith
  calc ((Finset.univ.filter fun σ : Fin n → Fin q => ε ≤ rsDevSq σ).card : ℝ)
      ≤ ((Finset.univ \ balanced q n δ).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ C * (q : ℝ) ^ n * Real.exp (-(κ * n)) := hC n hn
    _ ≤ C * (q : ℝ) ^ n * Real.exp (-(min κ 1 * n)) := by
        exact mul_le_mul_of_nonneg_left (rsc_exp_le_min κ n) (mul_nonneg hC0 (by positivity))

/-! ### Pairs of colourings: `‖R_{σ,τ} - R̄‖_F²` -/

/-- The pair map `(σ, τ) ↦ (v ↦ (σ_v, τ_v)) ∈ [q·q]^n`. -/
private def rscPair {n q : ℕ} (st : (Fin n → Fin q) × (Fin n → Fin q)) : Fin n → Fin (q * q) :=
  fun v => finProdFinEquiv (st.1 v, st.2 v)

private lemma rscPair_injective {n q : ℕ} : Function.Injective (@rscPair n q) := by
  intro st st' h
  have h' : ∀ v, (st.1 v, st.2 v) = (st'.1 v, st'.2 v) := fun v =>
    finProdFinEquiv.injective (congrFun h v)
  exact Prod.ext (funext fun v => (Prod.mk.inj (h' v)).1)
    (funext fun v => (Prod.mk.inj (h' v)).2)

/-- The colour fractions of the pair map are the overlap entries. -/
private lemma rscPair_colorFrac {n q : ℕ} (st : (Fin n → Fin q) × (Fin n → Fin q))
    (a b : Fin q) :
    colorFrac (rscPair st) (finProdFinEquiv (a, b)) = overlap st.1 st.2 a b := by
  have h : fiberCard (rscPair st) (finProdFinEquiv (a, b)) =
      fiberCard (fun v => (st.1 v, st.2 v)) (a, b) := by
    unfold fiberCard
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, rscPair, Equiv.apply_eq_iff_eq]
  unfold colorFrac overlap
  rw [h]

/-- If the pair map is balanced, then `‖R_{σ,τ} - R̄‖_F² ≤ q² δ²`. -/
private lemma rsc_ovDev_le_of_balanced {n q : ℕ} {δ : ℝ}
    {st : (Fin n → Fin q) × (Fin n → Fin q)} (hb : rscPair st ∈ balanced (q * q) n δ) :
    rsOvDev st.1 st.2 ≤ (q : ℝ) ^ 2 * δ ^ 2 := by
  simp only [balanced, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  have hqq : ((q * q : ℕ) : ℝ) = (q : ℝ) ^ 2 := by push_cast; ring
  unfold rsOvDev
  calc ∑ a, ∑ b, (overlap st.1 st.2 a b - 1 / (q : ℝ) ^ 2) ^ 2
        ≤ ∑ _a : Fin q, ∑ _b : Fin q, δ ^ 2 :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => by
          have h := hb (finProdFinEquiv (a, b))
          rw [rscPair_colorFrac, hqq] at h
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = (q : ℝ) ^ 2 * δ ^ 2 := by simp; ring

/-- Pairs of colourings with `‖R_{σ,τ} - R̄‖_F² ≥ ε` are exponentially rare. -/
theorem rs_card_ovDev_le {q : ℕ} (hq : 2 ≤ q) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, r ≤ 1 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 0 < n →
      ((Finset.univ.filter fun st : (Fin n → Fin q) × (Fin n → Fin q) =>
          ε ≤ rsOvDev st.1 st.2).card : ℝ) ≤
        K * (q : ℝ) ^ (2 * n) * Real.exp (-(r * n)) := by
  have hq0 : (0 : ℝ) < (q : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    positivity
  have hqq : 2 ≤ q * q := le_trans hq (Nat.le_mul_of_pos_left q (by omega))
  obtain ⟨hδ0, hδε⟩ := rsc_delta hq0 hε
  set δ := min 1 (ε / (2 * (q : ℝ) ^ 2)) with hδ
  obtain ⟨κ, hκ, C, hC0, hC⟩ := rsc_card_unbalanced hqq hδ0
  refine ⟨min κ 1, lt_min hκ one_pos, min_le_right _ _, C, hC0, fun n hn => ?_⟩
  set S := Finset.univ.filter fun st : (Fin n → Fin q) × (Fin n → Fin q) =>
    ε ≤ rsOvDev st.1 st.2 with hS
  have hsub : S.image rscPair ⊆ Finset.univ \ balanced (q * q) n δ := by
    intro ξ hξ
    obtain ⟨st, hst, rfl⟩ := Finset.mem_image.mp hξ
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hst
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hb => ?_⟩
    have := rsc_ovDev_le_of_balanced hb
    linarith
  have hcard : (S.image rscPair).card = S.card :=
    Finset.card_image_of_injective _ rscPair_injective
  calc (S.card : ℝ) = ((S.image rscPair).card : ℝ) := by rw [hcard]
    _ ≤ ((Finset.univ \ balanced (q * q) n δ).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ C * ((q * q : ℕ) : ℝ) ^ n * Real.exp (-(κ * n)) := hC n hn
    _ = C * (q : ℝ) ^ (2 * n) * Real.exp (-(κ * n)) := by
        rw [pow_mul]
        push_cast
        ring
    _ ≤ C * (q : ℝ) ^ (2 * n) * Real.exp (-(min κ 1 * n)) := by
        exact mul_le_mul_of_nonneg_left (rsc_exp_le_min κ n) (mul_nonneg hC0 (by positivity))

end

end ERZeroFreeness
