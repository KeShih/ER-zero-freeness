/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSTilt

/-!
# Appendix C, Lemma C.4: exponential moments of the number of edges

The averages "with the extra factor `e^χ` per edge" of `app:rs-split`, Step 1, and a
Cauchy–Schwarz inequality for weighted `tsum`s:

* `rs_exp_edges_hasSum`: `E_{𝖯_s} e^{χ m} = e^{(e^χ - 1) s n/2}`;
* `rs_exp_edges_mul_rsF_le`: `E_{𝖯_s}[e^{χ m} F] ≤ e^{(e^χ - 1) s n/2}` at a real point
  `x ∈ [0,1]` (any real `χ`), using `α(σ)ᵀ M_x α(σ) = 1 + tq‖α(σ) - u‖² ≤ 1`;
* `rs_exp_edges_mul_rsHR_le`: `E_{𝖯_s}[e^{χ m} H] ≤ e^{9(e^χ - 1) s n/8} E_{𝖯_s} H` for `χ ≥ 0`,
  using `0 ≤ M_x(a,a') M_x(b,b') ≤ 9/4`;
* `rs_tsum_mul_le_sqrt`: `∑ w f g ≤ (∑ w f²)^{1/2} (∑ w g²)^{1/2}` for nonnegative `w, f, g`.

## Proof

`e^{χ m} = ∏_{uv} (e^χ)^{N_{uv}}`, so the first identity is `rs_hasSum_poisPi_mul_prod` with the
one-dimensional generating function (`RSPoisPiAux.hasSum_poisPMF_mul_pow`), and
`n² · s/(2n) = sn/2` (`n = 0` separately).  For `F` and `H`, expand `F = q^{-n} ∑_σ w(σ)` and
`H = q^{-2n} ∑_{window} w(σ)w(τ)`; the same generating function with `y_{uv} = e^χ M_x(σ_u,σ_v)`
(resp. `e^χ M_x(σ_u,σ_v) M_x(τ_u,τ_v)`) gives
`E[e^{χm} w(σ)] = exp(∑_{uv} (s/(2n)) (e^χ M_x(σ_u,σ_v) - 1))`.  For one colouring,
`∑_{uv} M_x(σ_u,σ_v) = n²(1 + tq‖α - u‖²) ≤ n²` (`TwoReplicaAux.sum_aa_nonneg`, `t ≤ 0`).  For
pairs, the exponent at `χ ≥ 0` exceeds the exponent at `χ = 0` by at most `9(e^χ - 1)sn/8`,
since `0 ≤ M_x(σ_u,σ_v) M_x(τ_u,τ_v) ≤ 9/4` (`rs_rsM_mem`); summing over the window gives the
bound in terms of `E H`.  Cauchy–Schwarz is `Real.inner_le_Lp_mul_Lq_tsum_of_nonneg` with
`p = q = 2`, applied to `√w f` and `√w g`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- `E_{𝖯_s} e^{χ m} = exp((e^χ - 1) s n / 2)`. -/
theorem rs_exp_edges_hasSum {n : ℕ} {s : ℝ} (hs : 0 ≤ s) (χ : ℝ) :
    HasSum (fun N : RSGraph n => poisPi (rsMean n s) N * Real.exp (χ * (rsEdges N : ℝ)))
      (Real.exp ((Real.exp χ - 1) * s * n / 2)) := by
  have hlam : ∀ uv, 0 ≤ rsMean n s uv := fun uv => by unfold rsMean; positivity
  have H := rs_hasSum_poisPi_mul_prod hlam (fun _ k => Real.exp χ ^ k) (fun _ k => by positivity)
    (fun uv => Real.exp (rsMean n s uv * (Real.exp χ - 1)))
    (fun uv => RSPoisPiAux.hasSum_poisPMF_mul_pow _)
  have e1 : ∀ N : RSGraph n, ∏ uv, Real.exp χ ^ N uv = Real.exp (χ * (rsEdges N : ℝ)) := by
    intro N
    rw [Finset.prod_pow_eq_pow_sum, ← Real.exp_nat_mul]
    unfold rsEdges
    ring_nf
  have e2 : ∏ uv : Fin n × Fin n, Real.exp (rsMean n s uv * (Real.exp χ - 1)) =
      Real.exp ((Real.exp χ - 1) * s * n / 2) := by
    rw [← Real.exp_sum]
    congr 1
    simp only [rsMean, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      push_cast
      field_simp
  rw [e2] at H
  exact H.congr_fun fun N => by rw [e1]

/-! ### Auxiliary lemmas -/

namespace RSSplitMomentsAux

/-- The real generating function of the product Poisson law, for nonnegative `y`:
`E ∏_i y_i^{N_i} = exp(∑_i lam_i (y_i - 1))`. -/
theorem hasSum_poisPi_mul_prod_pow {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (y : ι → ℝ) (hy : ∀ i, 0 ≤ y i) :
    HasSum (fun N : ι → ℕ => poisPi lam N * ∏ i, y i ^ N i)
      (Real.exp (∑ i, lam i * (y i - 1))) := by
  have H := rs_hasSum_poisPi_mul_prod hlam (fun i k => y i ^ k)
    (fun i k => pow_nonneg (hy i) k) (fun i => Real.exp (lam i * (y i - 1)))
    (fun i => RSPoisPiAux.hasSum_poisPMF_mul_pow (y i))
  rwa [← Real.exp_sum] at H

/-- `e^{χ m} = ∏_{uv} (e^χ)^{N_{uv}}`. -/
theorem exp_mul_edges {n : ℕ} (χ : ℝ) (N : RSGraph n) :
    Real.exp (χ * (rsEdges N : ℝ)) = ∏ uv, Real.exp χ ^ N uv := by
  rw [Finset.prod_pow_eq_pow_sum, ← Real.exp_nat_mul]
  unfold rsEdges
  ring_nf

/-- The edge means `s/(2n)` are nonnegative. -/
theorem rsMean_nonneg {n : ℕ} {s : ℝ} (hs : 0 ≤ s) (uv : Fin n × Fin n) :
    0 ≤ rsMean n s uv := by
  unfold rsMean; positivity

/-- `E_{𝖯_s}[e^{χ m} w_{G,x}(σ)] = exp(∑_{uv} (s/(2n)) (e^χ M_x(σ_u,σ_v) - 1))`. -/
theorem hasSum_exp_edges_mul_rsW {q n : ℕ} (hq : 3 ≤ q) {s x : ℝ} (hs : 0 ≤ s) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) (χ : ℝ) (σ : Fin n → Fin q) :
    HasSum (fun N : RSGraph n => poisPi (rsMean n s) N *
        (Real.exp (χ * (rsEdges N : ℝ)) * rsW q (tRe q x) N σ))
      (Real.exp (∑ uv : Fin n × Fin n,
        rsMean n s uv * (Real.exp χ * rsM q (tRe q x) (σ uv.1) (σ uv.2) - 1))) := by
  have H := hasSum_poisPi_mul_prod_pow (rsMean_nonneg hs)
    (fun uv : Fin n × Fin n => Real.exp χ * rsM q (tRe q x) (σ uv.1) (σ uv.2))
    (fun uv => mul_nonneg (Real.exp_pos χ).le (hx0.trans (rs_rsM_mem hq hx0 hx1 _ _).1))
  refine H.congr_fun fun N => ?_
  rw [exp_mul_edges]
  unfold rsW
  simp only [mul_pow, Finset.prod_mul_distrib]

/-- `E_{𝖯_s}[e^{χ m} w_{G,x}(σ) w_{G,x}(τ)] =
exp(∑_{uv} (s/(2n)) (e^χ M_x(σ_u,σ_v) M_x(τ_u,τ_v) - 1))`. -/
theorem hasSum_exp_edges_mul_rsW_pair {q n : ℕ} (hq : 3 ≤ q) {s x : ℝ} (hs : 0 ≤ s)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (χ : ℝ) (σ τ : Fin n → Fin q) :
    HasSum (fun N : RSGraph n => poisPi (rsMean n s) N *
        (Real.exp (χ * (rsEdges N : ℝ)) * (rsW q (tRe q x) N σ * rsW q (tRe q x) N τ)))
      (Real.exp (∑ uv : Fin n × Fin n, rsMean n s uv *
        (Real.exp χ * (rsM q (tRe q x) (σ uv.1) (σ uv.2) * rsM q (tRe q x) (τ uv.1) (τ uv.2))
          - 1))) := by
  have hM := fun a b => rs_rsM_mem hq hx0 hx1 a b
  have H := hasSum_poisPi_mul_prod_pow (rsMean_nonneg hs)
    (fun uv : Fin n × Fin n => Real.exp χ *
      (rsM q (tRe q x) (σ uv.1) (σ uv.2) * rsM q (tRe q x) (τ uv.1) (τ uv.2)))
    (fun uv => mul_nonneg (Real.exp_pos χ).le
      (mul_nonneg (hx0.trans (hM _ _).1) (hx0.trans (hM _ _).1)))
  refine H.congr_fun fun N => ?_
  rw [exp_mul_edges]
  unfold rsW
  simp only [mul_pow, Finset.prod_mul_distrib]

/-- `∑_{uv} A_{σ_u σ_v} = n² q ‖α(σ) - u‖² ≥ 0`. -/
theorem sum_rsA_nonneg {q n : ℕ} (hq : q ≠ 0) (σ : Fin n → Fin q) :
    0 ≤ ∑ uv : Fin n × Fin n, ((rsA q (σ uv.1) (σ uv.2) : ℤ) : ℝ) := by
  rw [Fintype.sum_prod_type]
  simp_rw [rs_rsA_cast_eq_aa]
  exact TwoReplicaAux.sum_aa_nonneg hq σ

/-- `n² · s/(2n) = sn/2` (also for `n = 0`). -/
theorem card_mul_rsMean (n : ℕ) (s : ℝ) : (n : ℝ) * n * (s / (2 * n)) = s * n / 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp

/-- `∑_{uv} (s/(2n)) c = (sn/2) c`. -/
theorem sum_rsMean_mul_const {n : ℕ} (s c : ℝ) :
    ∑ uv : Fin n × Fin n, rsMean n s uv * c = s * n / 2 * c := by
  simp only [rsMean, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  rw [← mul_assoc, card_mul_rsMean]

/-- The one-colouring exponent: `∑_{uv} (s/(2n)) (e^χ M_x(σ_u,σ_v) - 1) ≤ (e^χ - 1) s n/2`. -/
theorem one_exponent_le {q n : ℕ} (hq : 3 ≤ q) {s x : ℝ} (hs : 0 ≤ s) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) (χ : ℝ) (σ : Fin n → Fin q) :
    ∑ uv : Fin n × Fin n,
        rsMean n s uv * (Real.exp χ * rsM q (tRe q x) (σ uv.1) (σ uv.2) - 1) ≤
      (Real.exp χ - 1) * s * n / 2 := by
  have ht : tRe q x ≤ 0 := rs_tRe_nonpos (by omega) hx0 hx1
  have hA := sum_rsA_nonneg (show q ≠ 0 by omega) σ
  have e : ∀ uv : Fin n × Fin n,
      rsMean n s uv * (Real.exp χ * rsM q (tRe q x) (σ uv.1) (σ uv.2) - 1) =
        rsMean n s uv * (Real.exp χ - 1) +
          (s / (2 * n) * Real.exp χ * tRe q x) * ((rsA q (σ uv.1) (σ uv.2) : ℤ) : ℝ) := by
    intro uv; simp only [rsMean, rsM]; ring
  rw [Finset.sum_congr rfl fun uv _ => e uv, Finset.sum_add_distrib, sum_rsMean_mul_const,
    ← Finset.mul_sum]
  have h0 : 0 ≤ s / (2 * n) * Real.exp χ := by positivity
  have h1 : s / (2 * n) * Real.exp χ * tRe q x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0 ht
  have h2 : s / (2 * n) * Real.exp χ * tRe q x *
      ∑ uv : Fin n × Fin n, ((rsA q (σ uv.1) (σ uv.2) : ℤ) : ℝ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg h1 hA
  linarith

/-- The pair exponent, `χ ≥ 0`: with `P_{uv} = M_x(σ_u,σ_v) M_x(τ_u,τ_v) ∈ [0, 9/4]`,
`∑_{uv} (s/(2n)) (e^χ P_{uv} - 1) ≤ 9(e^χ-1)sn/8 + ∑_{uv} (s/(2n)) (P_{uv} - 1)`. -/
theorem pair_exponent_le {q n : ℕ} (hq : 3 ≤ q) {s x χ : ℝ} (hs : 0 ≤ s) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) (hχ : 0 ≤ χ) (σ τ : Fin n → Fin q) :
    ∑ uv : Fin n × Fin n, rsMean n s uv *
        (Real.exp χ * (rsM q (tRe q x) (σ uv.1) (σ uv.2) * rsM q (tRe q x) (τ uv.1) (τ uv.2))
          - 1) ≤
      9 * (Real.exp χ - 1) * s * n / 8 + ∑ uv : Fin n × Fin n, rsMean n s uv *
        (Real.exp 0 * (rsM q (tRe q x) (σ uv.1) (σ uv.2) * rsM q (tRe q x) (τ uv.1) (τ uv.2))
          - 1) := by
  have hM := fun a b => rs_rsM_mem hq hx0 hx1 a b
  have hP : ∀ uv : Fin n × Fin n,
      rsM q (tRe q x) (σ uv.1) (σ uv.2) * rsM q (tRe q x) (τ uv.1) (τ uv.2) ≤ 9 / 4 := by
    intro uv
    have h1 := hM (σ uv.1) (σ uv.2)
    have h2 := hM (τ uv.1) (τ uv.2)
    have h1' : 0 ≤ rsM q (tRe q x) (σ uv.1) (σ uv.2) := hx0.trans h1.1
    have h2' : 0 ≤ rsM q (tRe q x) (τ uv.1) (τ uv.2) := hx0.trans h2.1
    nlinarith [mul_le_mul h1.2 h2.2 h2' (by norm_num : (0:ℝ) ≤ 3 / 2)]
  have hχ' : 0 ≤ Real.exp χ - 1 := by linarith [Real.add_one_le_exp χ]
  rw [Real.exp_zero]
  calc ∑ uv : Fin n × Fin n, rsMean n s uv *
        (Real.exp χ * (rsM q (tRe q x) (σ uv.1) (σ uv.2) * rsM q (tRe q x) (τ uv.1) (τ uv.2))
          - 1)
      = ∑ uv : Fin n × Fin n, (rsMean n s uv * (Real.exp χ - 1) *
          (rsM q (tRe q x) (σ uv.1) (σ uv.2) * rsM q (tRe q x) (τ uv.1) (τ uv.2)) +
          rsMean n s uv *
            (1 * (rsM q (tRe q x) (σ uv.1) (σ uv.2) * rsM q (tRe q x) (τ uv.1) (τ uv.2)) - 1)) :=
        Finset.sum_congr rfl fun uv _ => by ring
    _ ≤ ∑ uv : Fin n × Fin n, (rsMean n s uv * ((Real.exp χ - 1) * (9 / 4)) +
          rsMean n s uv *
            (1 * (rsM q (tRe q x) (σ uv.1) (σ uv.2) * rsM q (tRe q x) (τ uv.1) (τ uv.2)) - 1)) := by
        refine Finset.sum_le_sum fun uv _ => ?_
        have hm := rsMean_nonneg hs uv
        have := mul_le_mul_of_nonneg_left (hP uv) (mul_nonneg hm hχ')
        nlinarith
    _ = 9 * (Real.exp χ - 1) * s * n / 8 + ∑ uv : Fin n × Fin n, rsMean n s uv *
          (1 * (rsM q (tRe q x) (σ uv.1) (σ uv.2) * rsM q (tRe q x) (τ uv.1) (τ uv.2)) - 1) := by
        rw [Finset.sum_add_distrib, sum_rsMean_mul_const]
        ring

/-- Termwise comparison `f_i ≤ e g_i` of two finite sums, pulled through a factor `a ≥ 0`. -/
theorem mul_sum_le_mul_mul_sum {ι : Type*} (s : Finset ι) {a e : ℝ} {f g : ι → ℝ}
    (ha : 0 ≤ a) (h : ∀ i ∈ s, f i ≤ e * g i) :
    a * ∑ i ∈ s, f i ≤ e * (a * ∑ i ∈ s, g i) :=
  calc a * ∑ i ∈ s, f i ≤ a * ∑ i ∈ s, e * g i :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum h) ha
    _ = e * (a * ∑ i ∈ s, g i) := by rw [← Finset.mul_sum]; ring

end RSSplitMomentsAux

open RSSplitMomentsAux

/-- `E_{𝖯_s}[e^{χ m} F_G(x)] ≤ exp((e^χ - 1) s n / 2)` for `x ∈ [0,1]` and every real `χ`. -/
theorem rs_exp_edges_mul_rsF_le {q n : ℕ} (hq : 3 ≤ q) {s x : ℝ} (hs : 0 ≤ s) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) (χ : ℝ) :
    Summable (fun N => poisPi (rsMean n s) N *
        (Real.exp (χ * (rsEdges N : ℝ)) * rsF q (tRe q x) N)) ∧
      rsExp n s (fun N => Real.exp (χ * (rsEdges N : ℝ)) * rsF q (tRe q x) N) ≤
        Real.exp ((Real.exp χ - 1) * s * n / 2) := by
  have Hsum := (hasSum_sum (s := (Finset.univ : Finset (Fin n → Fin q)))
    fun σ _ => hasSum_exp_edges_mul_rsW hq hs hx0 hx1 χ σ).mul_left (((q : ℝ) ^ n)⁻¹)
  have H : HasSum (fun N => poisPi (rsMean n s) N *
      (Real.exp (χ * (rsEdges N : ℝ)) * rsF q (tRe q x) N)) _ := Hsum.congr_fun fun N => by
    simp only [rsF, Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by ring
  refine ⟨H.summable, ?_⟩
  unfold rsExp poisPiExp
  rw [H.tsum_eq]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hQ : (0 : ℝ) < (q : ℝ) ^ n := by positivity
  calc ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q, Real.exp (∑ uv : Fin n × Fin n,
        rsMean n s uv * (Real.exp χ * rsM q (tRe q x) (σ uv.1) (σ uv.2) - 1))
      ≤ ((q : ℝ) ^ n)⁻¹ * ∑ _σ : Fin n → Fin q, Real.exp ((Real.exp χ - 1) * s * n / 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ =>
          Real.exp_le_exp.mpr (one_exponent_le hq hs hx0 hx1 χ σ)) (by positivity)
    _ = Real.exp ((Real.exp χ - 1) * s * n / 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        field_simp

/-- `E_{𝖯_s}[e^{χ m} H] ≤ exp(9 (e^χ - 1) s n / 8) · E_{𝖯_s} H` for `x ∈ [0,1]` and `χ ≥ 0`. -/
theorem rs_exp_edges_mul_rsHR_le {q n : ℕ} (hq : 3 ≤ q) {s x η χ : ℝ} (hs : 0 ≤ s)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hχ : 0 ≤ χ) :
    Summable (fun N => poisPi (rsMean n s) N *
        (Real.exp (χ * (rsEdges N : ℝ)) * rsHR q η (tRe q x) N)) ∧
      rsExp n s (fun N => Real.exp (χ * (rsEdges N : ℝ)) * rsHR q η (tRe q x) N) ≤
        Real.exp (9 * (Real.exp χ - 1) * s * n / 8) * rsExp n s (rsHR q η (tRe q x)) := by
  have Hχ := (hasSum_sum (s := rsWindow q n η)
    fun p _ => hasSum_exp_edges_mul_rsW_pair hq hs hx0 hx1 χ p.1 p.2).mul_left
      ((((q : ℝ) ^ n)⁻¹) ^ 2)
  have H0 := (hasSum_sum (s := rsWindow q n η)
    fun p _ => hasSum_exp_edges_mul_rsW_pair hq hs hx0 hx1 (0 : ℝ) p.1 p.2).mul_left
      ((((q : ℝ) ^ n)⁻¹) ^ 2)
  have Hχ' : HasSum (fun N => poisPi (rsMean n s) N *
      (Real.exp (χ * (rsEdges N : ℝ)) * rsHR q η (tRe q x) N)) _ := Hχ.congr_fun fun N => by
    simp only [rsHR, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  have H0' : HasSum (fun N => poisPi (rsMean n s) N * rsHR q η (tRe q x) N) _ :=
    H0.congr_fun fun N => by
      simp only [rsHR, Finset.mul_sum, zero_mul, Real.exp_zero, one_mul]
      exact Finset.sum_congr rfl fun p _ => by ring
  refine ⟨Hχ'.summable, ?_⟩
  unfold rsExp poisPiExp
  rw [Hχ'.tsum_eq, H0'.tsum_eq]
  refine mul_sum_le_mul_mul_sum _ (by positivity) fun p _ => ?_
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (pair_exponent_le hq hs hx0 hx1 hχ p.1 p.2)

/-- Cauchy–Schwarz for nonnegative weighted `tsum`s. -/
theorem rs_tsum_mul_le_sqrt {α : Type*} {w f g : α → ℝ} (hw : ∀ a, 0 ≤ w a)
    (hf : ∀ a, 0 ≤ f a) (hg : ∀ a, 0 ≤ g a) (hf2 : Summable fun a => w a * f a ^ 2)
    (hg2 : Summable fun a => w a * g a ^ 2) :
    ∑' a, w a * (f a * g a) ≤
      Real.sqrt (∑' a, w a * f a ^ 2) * Real.sqrt (∑' a, w a * g a ^ 2) := by
  have e1 : ∀ a, (Real.sqrt (w a) * f a) ^ (2 : ℝ) = w a * f a ^ 2 := fun a => by
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (hw a)]
  have e2 : ∀ a, (Real.sqrt (w a) * g a) ^ (2 : ℝ) = w a * g a ^ 2 := fun a => by
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (hw a)]
  have e3 : ∀ a, Real.sqrt (w a) * f a * (Real.sqrt (w a) * g a) = w a * (f a * g a) :=
    fun a => by
      have := Real.mul_self_sqrt (hw a)
      calc Real.sqrt (w a) * f a * (Real.sqrt (w a) * g a)
          = (Real.sqrt (w a) * Real.sqrt (w a)) * (f a * g a) := by ring
        _ = w a * (f a * g a) := by rw [this]
  have key := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (f := fun a => Real.sqrt (w a) * f a) (g := fun a => Real.sqrt (w a) * g a)
    (fun a => mul_nonneg (Real.sqrt_nonneg _) (hf a))
    (fun a => mul_nonneg (Real.sqrt_nonneg _) (hg a))
    (by simpa only [e1] using hf2) (by simpa only [e2] using hg2)
  simp only [e1, e2, e3] at key
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  convert key using 3

end

end ERZeroFreeness
