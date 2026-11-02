/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs
import ERZeroFreeness.Entropy

/-!
# Overlap energy versus relative entropy (`eq:entropy-bound`)

For `q ≥ 3`, `0 < δ < 1/q`, `σ ∈ 𝓑_n(δ)` and any `τ`, the overlap matrix `R = overlap σ τ`
satisfies `q² ∑ R_ij² - 1 ≤ (1 + qδ)/c_q · D(R ‖ U)`, where `U` is uniform on `[q]²` and
`D(R ‖ U) = empKL (σ,τ)` (`overlap_energy_le_empKL`).

Proof.  With `α = colorFrac σ` and `p^{(i)}_j = R_ij/α_i`,
`q²∑R² - 1 = (q∑α² - 1) + q∑_i α_i² (q∑_j (p^{(i)}_j)² - 1)`.
Apply `entropy_comparison` to `α` and to each `p^{(i)}`, use `q α_i² ≤ (1+qδ) α_i` and
`q∑_j (p^{(i)}_j)² - 1 ≥ 0`, and the chain rule
`D(R ‖ U) = D(α ‖ u) + ∑_i α_i D(p^{(i)} ‖ u)`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- For a vector on `Fin q` summing to one, `q ∑ p² - 1 ≥ 0` (Cauchy–Schwarz). -/
private lemma overlap_q_sum_sq_sub_one_nonneg {q : ℕ} (p : Fin q → ℝ) (hp1 : ∑ i, p i = 1) :
    0 ≤ (q : ℝ) * ∑ i, p i ^ 2 - 1 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin q))) (f := p)
  rw [hp1, Finset.card_univ, Fintype.card_fin] at h
  linarith

/-- The real-analytic core of `eq:entropy-bound`: for a nonnegative matrix `R` on `[q]²` with
positive row sums `α_i` summing to one and `q α_i ≤ 1 + qδ`,
`q² ∑ R² - 1 ≤ (1 + qδ)/c_q · ∑ R log(q² R)`. -/
private lemma overlap_core {q : ℕ} (hq : 3 ≤ q) {δ : ℝ} (hδ : 0 ≤ δ)
    (R : Fin q → Fin q → ℝ) (α : Fin q → ℝ)
    (hR0 : ∀ i j, 0 ≤ R i j) (hRα : ∀ i, ∑ j, R i j = α i) (hα0 : ∀ i, 0 < α i)
    (hα1 : ∑ i, α i = 1) (hαδ : ∀ i, (q : ℝ) * α i ≤ 1 + q * δ) :
    (q : ℝ) ^ 2 * ∑ i, ∑ j, R i j ^ 2 - 1 ≤
      (1 + q * δ) / cq q * ∑ i, ∑ j, R i j * Real.log ((q : ℝ) ^ 2 * R i j) := by
  have hc := cq_pos hq
  have hq0 : (0 : ℝ) < q := by
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  -- the conditional distributions `p^{(i)}_j = R_ij / α_i`
  obtain ⟨p, hp⟩ : ∃ p : Fin q → Fin q → ℝ, p = fun i j => R i j / α i := ⟨_, rfl⟩
  have hp0 : ∀ i j, 0 ≤ p i j := fun i j => by
    rw [hp]; exact div_nonneg (hR0 i j) (hα0 i).le
  have hp1 : ∀ i, ∑ j, p i j = 1 := by
    intro i
    rw [hp]
    simp only
    rw [← Finset.sum_div, hRα i]
    exact div_self (hα0 i).ne'
  have hRp : ∀ i j, R i j = α i * p i j := by
    intro i j
    rw [hp]
    field_simp [(hα0 i).ne']
  -- relative entropies and quadratic energies
  obtain ⟨Dα, hDα⟩ : ∃ x : ℝ, x = ∑ i, α i * Real.log ((q : ℝ) * α i) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Fin q → ℝ, D = fun i => ∑ j, p i j * Real.log ((q : ℝ) * p i j) :=
    ⟨_, rfl⟩
  obtain ⟨Eα, hEα⟩ : ∃ x : ℝ, x = (q : ℝ) * ∑ i, α i ^ 2 - 1 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Fin q → ℝ, E = fun i => (q : ℝ) * ∑ j, p i j ^ 2 - 1 := ⟨_, rfl⟩
  have hEα_le : cq q * Eα ≤ Dα := by
    rw [hEα, hDα]; exact entropy_comparison hq α (fun i => (hα0 i).le) hα1
  have hE_le : ∀ i, cq q * E i ≤ D i := fun i => by
    rw [hE, hD]; exact entropy_comparison hq (p i) (hp0 i) (hp1 i)
  have hEα0 : 0 ≤ Eα := by rw [hEα]; exact overlap_q_sum_sq_sub_one_nonneg α hα1
  have hE0 : ∀ i, 0 ≤ E i := fun i => by
    rw [hE]; exact overlap_q_sum_sq_sub_one_nonneg (p i) (hp1 i)
  -- `q² ∑ R² - 1 = (q ∑ α² - 1) + q ∑_i α_i² (q ∑_j (p^{(i)}_j)² - 1)`
  have hdecomp : (q : ℝ) ^ 2 * ∑ i, ∑ j, R i j ^ 2 - 1 =
      Eα + ∑ i, (q : ℝ) * α i ^ 2 * E i := by
    have hterm : ∀ i, (q : ℝ) * α i ^ 2 * E i =
        (q : ℝ) ^ 2 * ∑ j, R i j ^ 2 - (q : ℝ) * α i ^ 2 := by
      intro i
      have hR2 : ∑ j, R i j ^ 2 = α i ^ 2 * ∑ j, p i j ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [hRp i j]; ring
      rw [hR2]
      simp only [hE]
      ring
    have hsum : ∑ i, (q : ℝ) * α i ^ 2 * E i =
        ∑ i, ((q : ℝ) ^ 2 * ∑ j, R i j ^ 2 - (q : ℝ) * α i ^ 2) :=
      Finset.sum_congr rfl fun i _ => hterm i
    rw [hsum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hEα]
    ring
  -- chain rule `D(R ‖ U) = D(α ‖ u) + ∑_i α_i D(p^{(i)} ‖ u)`
  have hchain : ∑ i, ∑ j, R i j * Real.log ((q : ℝ) ^ 2 * R i j) = Dα + ∑ i, α i * D i := by
    have hterm : ∀ i j, R i j * Real.log ((q : ℝ) ^ 2 * R i j) =
        R i j * Real.log ((q : ℝ) * α i) + α i * (p i j * Real.log ((q : ℝ) * p i j)) := by
      intro i j
      rcases (hR0 i j).eq_or_lt with h | h
      · have h' : p i j = 0 := by rw [hp]; simp [← h]
        rw [← h, h']
        simp
      · have hα := hα0 i
        have hpij : 0 < p i j := by rw [hp]; exact div_pos h hα
        have e : (q : ℝ) ^ 2 * R i j = ((q : ℝ) * α i) * ((q : ℝ) * p i j) := by
          rw [hRp i j]; ring
        rw [e, Real.log_mul (by positivity) (by positivity), hRp i j]
        ring
    have hsum : ∑ i, ∑ j, R i j * Real.log ((q : ℝ) ^ 2 * R i j) =
        ∑ i, ∑ j, (R i j * Real.log ((q : ℝ) * α i) +
          α i * (p i j * Real.log ((q : ℝ) * p i j))) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
    rw [hsum]
    simp only [Finset.sum_add_distrib]
    congr 1
    · rw [hDα]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_mul, hRα i]
    · rw [hD]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only
      rw [Finset.mul_sum]
  rw [hdecomp, hchain]
  have h1 : Eα ≤ (1 + q * δ) / cq q * Dα := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    have hD0 : 0 ≤ Dα := le_trans (mul_nonneg hc.le hEα0) hEα_le
    have hqδ : 0 ≤ (q : ℝ) * δ := by positivity
    nlinarith
  have h2 : ∀ i, (q : ℝ) * α i ^ 2 * E i ≤ (1 + q * δ) / cq q * (α i * D i) := by
    intro i
    have hα := hα0 i
    have h3 : (q : ℝ) * α i ^ 2 ≤ (1 + q * δ) * α i := by
      have := hαδ i
      nlinarith
    have h4 : cq q * (α i * E i) ≤ α i * D i := by
      have := hE_le i
      nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    have h5 : (q : ℝ) * α i ^ 2 * E i ≤ (1 + q * δ) * α i * E i :=
      mul_le_mul_of_nonneg_right h3 (hE0 i)
    have h6 : 0 ≤ 1 + (q : ℝ) * δ := by positivity
    have h7 : (1 + q * δ) * (cq q * (α i * E i)) ≤ (1 + q * δ) * (α i * D i) :=
      mul_le_mul_of_nonneg_left h4 h6
    nlinarith
  rw [mul_add, Finset.mul_sum]
  exact add_le_add h1 (Finset.sum_le_sum fun i _ => h2 i)

/-- `|σ⁻¹(i)| = ∑_j |{v : (σ v, τ v) = (i, j)}|`. -/
private lemma overlap_fiberCard_fst {n q : ℕ} (σ τ : Fin n → Fin q) (i : Fin q) :
    fiberCard σ i = ∑ j, fiberCard (fun v => (σ v, τ v)) (i, j) := by
  unfold fiberCard
  rw [Finset.card_eq_sum_card_fiberwise (f := τ) (t := Finset.univ) (by simp)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.filter_filter]
  congr 1
  ext v
  simp [Prod.mk.injEq]

/-- `∑_i |σ⁻¹(i)| = n`. -/
private lemma overlap_sum_fiberCard {n q : ℕ} (σ : Fin n → Fin q) :
    ∑ i, fiberCard σ i = n := by
  have h := Finset.card_eq_sum_card_fiberwise (f := σ) (s := (Finset.univ : Finset (Fin n)))
    (t := Finset.univ) (by simp)
  rw [Finset.card_univ, Fintype.card_fin] at h
  conv_rhs => rw [h]
  unfold fiberCard
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ext v
  simp

/-- **`eq:entropy-bound`.** For `σ` in the balanced window `𝓑_n(δ)` with `0 < δ < 1/q`,
`q² ∑ R_ij² - 1 ≤ (1 + qδ)/c_q · D(R ‖ U)`, where `R = overlap σ τ` and
`D(R ‖ U) = empKL (σ,τ)`. -/
theorem overlap_energy_le_empKL {q : ℕ} (hq : 3 ≤ q) {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ)
    (hδq : δ < 1 / (q : ℝ)) (σ τ : Fin n → Fin q) (hσ : σ ∈ balanced q n δ) :
    (q : ℝ) ^ 2 * ∑ i, ∑ j, overlap σ τ i j ^ 2 - 1 ≤
      (1 + q * δ) / cq q * empKL (fun v => (σ v, τ v)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 : (0 : ℝ) < q := by
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hbal : ∀ i, |colorFrac σ i - 1 / (q : ℝ)| ≤ δ := (Finset.mem_filter.mp hσ).2
  -- `empKL (σ, τ) = ∑_{i,j} R_ij log(q² R_ij)`
  have hKL : empKL (fun v => (σ v, τ v)) =
      ∑ i, ∑ j, overlap σ τ i j * Real.log ((q : ℝ) ^ 2 * overlap σ τ i j) := by
    unfold empKL overlap
    rw [Fintype.sum_prod_type]
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 2
    ring
  rw [hKL]
  refine overlap_core hq hδ.le (overlap σ τ) (colorFrac σ) ?_ ?_ ?_ ?_ ?_
  · intro i j
    unfold overlap
    positivity
  · intro i
    unfold overlap colorFrac
    rw [← Finset.sum_div, overlap_fiberCard_fst σ τ i, Nat.cast_sum]
  · intro i
    have h1 := (abs_le.mp (hbal i)).1
    have h2 : 0 < 1 / (q : ℝ) - δ := by linarith
    linarith
  · unfold colorFrac
    rw [← Finset.sum_div, ← Nat.cast_sum, overlap_sum_fiberCard]
    exact div_self hn0.ne'
  · intro i
    have h := (abs_le.mp (hbal i)).2
    have h' : (q : ℝ) * colorFrac σ i ≤ (q : ℝ) * (1 / q + δ) := by
      apply mul_le_mul_of_nonneg_left _ hq0.le
      linarith
    rw [mul_add, mul_one_div_cancel hq0.ne'] at h'
    exact h'

end

end ERZeroFreeness
