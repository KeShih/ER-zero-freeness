/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSTilt

/-!
# Appendix C, Lemma C.7, Step 2: a test on added edges (`eq:rs-signal`, `eq:rs-test`)

For a colouring `τ` with proportions `β` and a multigraph `G'`, the test statistic is
`S_τ(G') = t q ∑_{(u,v)} N'_{uv} ⟨e_{τ_u} - β, e_{τ_v} - β⟩` (`rsTestStat`), at a real anchor
`x ∈ [0,1]`, `t = t(x)`.

* `rs_test_upper` (**`eq:rs-test`, first bound**): `E_{𝖯_Δ} e^{λ S_τ} ≤ e^{C_t λ² n}` for
  `0 ≤ λ ≤ 1/3`, uniformly in `τ`, with `C_t = 9Δ/2`;
* `rs_test_lower` (**`eq:rs-signal` + `eq:rs-test`, second bound**): for every real `λ`,
  `E_{𝖯^σ_Δ} e^{λ S_τ} ≥ exp(λ (Δ n t² q²/2) ‖R_{σ,τ} - αβᵀ‖_F²)`; on
  `𝒞 = {‖R - αβᵀ‖_F ≥ η/2}` and for `λ ≥ 0` the exponent is `≥ 2λψ_x n`, `ψ_x = Δ t² q² η²/16`.

**Deviation from the paper.**  `C_t = 9Δ/2` instead of `9eΔ/4` (from `|e^y - 1 - y| ≤ y²` for
`|y| ≤ 1`, `Real.abs_exp_sub_one_sub_id_le`); the lower bound holds for every real `λ` (it is the
inequality `e^y - 1 ≥ y` inside the exact Poisson generating function instead of Jensen).

## Proof

This is Step 2 of the paper's proof of Lemma C.7.  The coefficients
`c_{uv} = t q ⟨e_{τ_u} - β, e_{τ_v} - β⟩` satisfy `|⟨e_a - β, e_b - β⟩| ≤ 2`, `q|t| ≤ q/(q-1) ≤ 3/2`
(so `|λ c_{uv}| ≤ 1`), and `∑_{u,v} c_{uv} = t q ‖∑_v (e_{τ_v} - β)‖² = 0`.  By the generating
function (`rs_poisPi_mul_prod_pow`, `rs_hasSum_poisPi`),
`E_{lam} e^{λ S} = exp(∑_{uv} lam_{uv}(e^{λ c_{uv}} - 1))`.  Upper bound: subtract
`∑ lam_{uv} λ c_{uv} = 0` (constant means `Δ/(2n)`) and use `e^y - 1 - y ≤ y²`.  Lower bound:
`e^y - 1 ≥ y` with the means `Δ M_x(σ_u,σ_v)/(2n) ≥ 0`, and the signal identity
`∑_{uv} M_x(σ_u,σ_v) ⟨e_{τ_u} - β, e_{τ_v} - β⟩ = t q n² ‖R - αβᵀ‖_F²`
(`M_x(a,b) = 1 + tq⟨e_a - u, e_b - u⟩`, `∑_u (e_{σ_u} - u)_a (e_{τ_u} - β)_b = n(R_{ab} - α_a β_b)`,
`TwoReplicaAux.sum_sum_sum_mul_eq`).

## Implementation notes

Auxiliary lemmas are in `RSAnchorTestAux`: `hasSum_exp_lin` is the real generating function
`E_{lam} exp(∑_i N_i y_i) = exp(∑_i lam_i (e^{y_i} - 1))`; `abs_testCoef_le`, `sum_testCoef` and
`abs_tRe_mul_le` are the coefficient facts; `signal` is `eq:rs-signal`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

namespace RSAnchorTestAux

/-- Exponential generating function of a product Poisson law:
`E exp(∑_i N_i y_i) = exp(∑_i lam_i (e^{y_i} - 1))`. -/
theorem hasSum_exp_lin {ι : Type*} [Fintype ι] {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (y : ι → ℝ) :
    HasSum (fun N : ι → ℕ => poisPi lam N * Real.exp (∑ i, (N i : ℝ) * y i))
      (Real.exp (∑ i, lam i * (Real.exp (y i) - 1))) := by
  have h2 := (rs_hasSum_poisPi (lam := fun i => lam i * Real.exp (y i))
    (fun i => mul_nonneg (hlam i) (Real.exp_pos _).le)).mul_left
      (Real.exp (∑ i, lam i * (Real.exp (y i) - 1)))
  rw [mul_one] at h2
  refine h2.congr_fun fun N => ?_
  rw [← rs_poisPi_mul_prod_pow lam (fun i => Real.exp (y i)) N, Real.exp_sum]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Real.exp_nat_mul]

theorem sum_fiberCard {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ) :
    ∑ c : κ, fiberCard f c = Fintype.card ι := by
  have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset ι))
    (t := (Finset.univ : Finset κ)) (f := f) (fun x _ => Finset.mem_univ _)
  rw [Finset.card_univ] at this
  exact this.symm

theorem colorFrac_nonneg {n q : ℕ} (τ : Fin n → Fin q) (c : Fin q) : 0 ≤ colorFrac τ c := by
  unfold colorFrac; positivity

theorem colorFrac_le_one {n q : ℕ} (τ : Fin n → Fin q) (c : Fin q) : colorFrac τ c ≤ 1 := by
  unfold colorFrac
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [div_le_one (by exact_mod_cast hn)]
    have : fiberCard τ c ≤ n := by
      unfold fiberCard
      exact (Finset.card_le_univ _).trans (by simp)
    exact_mod_cast this

theorem sum_colorFrac {n q : ℕ} (hn : 0 < n) (τ : Fin n → Fin q) :
    ∑ c, colorFrac τ c = 1 := by
  unfold colorFrac
  rw [← Finset.sum_div]
  have h := sum_fiberCard τ
  rw [Fintype.card_fin] at h
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_eq_one_iff_eq hn']
  exact_mod_cast h

theorem fiberCard_eq_sum_ite {ι κ : Type*} [Fintype ι] [DecidableEq κ] (f : ι → κ) (c : κ) :
    (fiberCard f c : ℝ) = ∑ u, (if f u = c then (1 : ℝ) else 0) := by
  unfold fiberCard
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun u _ => ?_
  split_ifs <;> rfl

/-- `∑_u 1[τ_u = c] = n β_c`. -/
theorem sum_ind_eq {n q : ℕ} (hn : 0 < n) (τ : Fin n → Fin q) (c : Fin q) :
    ∑ u, (if τ u = c then (1 : ℝ) else 0) = n * colorFrac τ c := by
  rw [← fiberCard_eq_sum_ite]
  unfold colorFrac
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- `⟨e_a - β, e_b - β⟩ = 1[a=b] - β_a - β_b + ∑_c β_c²`. -/
theorem testCoef_eq {n q : ℕ} (τ : Fin n → Fin q) (a b : Fin q) :
    rsTestCoef τ a b = (if a = b then (1 : ℝ) else 0) - colorFrac τ a - colorFrac τ b +
      ∑ c, colorFrac τ c ^ 2 := by
  unfold rsTestCoef
  have e : ∀ c, ((if a = c then (1 : ℝ) else 0) - colorFrac τ c) *
      ((if b = c then (1 : ℝ) else 0) - colorFrac τ c) =
      (if a = c then (if b = c then (1 : ℝ) else 0) else 0) - (if a = c then colorFrac τ c else 0)
        - (if b = c then colorFrac τ c else 0) + colorFrac τ c ^ 2 := by
    intro c; split_ifs <;> ring
  simp_rw [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

theorem abs_testCoef_le {n q : ℕ} (hn : 0 < n) (τ : Fin n → Fin q) (a b : Fin q) :
    |rsTestCoef τ a b| ≤ 2 := by
  rw [testCoef_eq]
  have hS0 : 0 ≤ ∑ c, colorFrac τ c ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hS1 : ∑ c, colorFrac τ c ^ 2 ≤ 1 := by
    calc ∑ c, colorFrac τ c ^ 2 ≤ ∑ c, colorFrac τ c := by
          refine Finset.sum_le_sum fun c _ => ?_
          have h0 := colorFrac_nonneg τ c
          have h1 := colorFrac_le_one τ c
          nlinarith
      _ = 1 := sum_colorFrac hn τ
  have ha0 := colorFrac_nonneg τ a
  have ha1 := colorFrac_le_one τ a
  have hb0 := colorFrac_nonneg τ b
  have hb1 := colorFrac_le_one τ b
  have hI0 : (0 : ℝ) ≤ if a = b then (1 : ℝ) else 0 := by split_ifs <;> norm_num
  have hI1 : (if a = b then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  rw [abs_le]
  constructor <;> linarith

theorem sum_testCoef {n q : ℕ} (hn : 0 < n) (τ : Fin n → Fin q) :
    ∑ uv : Fin n × Fin n, rsTestCoef τ (τ uv.1) (τ uv.2) = 0 := by
  rw [Fintype.sum_prod_type]
  unfold rsTestCoef
  rw [TwoReplicaAux.sum_sum_sum_mul_eq
    (fun c u => (if τ u = c then (1 : ℝ) else 0) - colorFrac τ c)]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [Finset.sum_sub_distrib, sum_ind_eq hn, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

theorem sum_ind_mul_ind {n q : ℕ} (hn : 0 < n) (σ τ : Fin n → Fin q) (i j : Fin q) :
    ∑ u, (if σ u = i then (1 : ℝ) else 0) * (if τ u = j then (1 : ℝ) else 0) =
      n * overlap σ τ i j := by
  have e : ∀ u, (if σ u = i then (1 : ℝ) else 0) * (if τ u = j then (1 : ℝ) else 0) =
      if (σ u, τ u) = (i, j) then 1 else 0 := by
    intro u
    by_cases h1 : σ u = i <;> by_cases h2 : τ u = j <;> simp [h1, h2]
  simp_rw [e]
  rw [← fiberCard_eq_sum_ite (fun v => (σ v, τ v)) (i, j)]
  unfold overlap
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- `∑_u (e_{σ_u} - u)_i (e_{τ_u} - β)_j = n (R_{ij} - α_i β_j)`. -/
theorem sum_g_mul_h {n q : ℕ} (hn : 0 < n) (σ τ : Fin n → Fin q) (i j : Fin q) :
    ∑ u, ((if σ u = i then (1 : ℝ) else 0) - 1 / q) *
        ((if τ u = j then (1 : ℝ) else 0) - colorFrac τ j) =
      n * (overlap σ τ i j - colorFrac σ i * colorFrac τ j) := by
  have e : ∀ u, ((if σ u = i then (1 : ℝ) else 0) - 1 / q) *
      ((if τ u = j then (1 : ℝ) else 0) - colorFrac τ j) =
      (if σ u = i then (1 : ℝ) else 0) * (if τ u = j then (1 : ℝ) else 0) -
        colorFrac τ j * (if σ u = i then (1 : ℝ) else 0) -
        1 / q * (if τ u = j then (1 : ℝ) else 0) + 1 / q * colorFrac τ j := by
    intro u; ring
  simp_rw [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_ind_mul_ind hn, sum_ind_eq hn, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- **The signal identity** (`eq:rs-signal`):
`∑_{(u,v)} M_t(σ_u,σ_v) ⟨e_{τ_u} - β, e_{τ_v} - β⟩ = t q n² ‖R_{σ,τ} - αβᵀ‖_F²`. -/
theorem signal {n q : ℕ} (hq : q ≠ 0) (hn : 0 < n) (t : ℝ) (σ τ : Fin n → Fin q) :
    ∑ uv : Fin n × Fin n, rsM q t (σ uv.1) (σ uv.2) * rsTestCoef τ (τ uv.1) (τ uv.2) =
      t * q * n ^ 2 * rsCorrDev σ τ := by
  have e1 : ∀ uv : Fin n × Fin n, rsM q t (σ uv.1) (σ uv.2) * rsTestCoef τ (τ uv.1) (τ uv.2) =
      rsTestCoef τ (τ uv.1) (τ uv.2) +
        t * (TwoReplicaAux.aa q (σ uv.1) (σ uv.2) * rsTestCoef τ (τ uv.1) (τ uv.2)) := by
    intro uv; unfold rsM; rw [rs_rsA_cast_eq_aa]; ring
  simp_rw [e1]
  rw [Finset.sum_add_distrib, sum_testCoef hn, zero_add, ← Finset.mul_sum]
  set g : Fin q → Fin n → ℝ := fun i u => (if σ u = i then (1 : ℝ) else 0) - 1 / q with hg
  set h : Fin q → Fin n → ℝ := fun j u => (if τ u = j then (1 : ℝ) else 0) - colorFrac τ j
    with hh
  have key : ∀ u v : Fin n, TwoReplicaAux.aa q (σ u) (σ v) * rsTestCoef τ (τ u) (τ v) =
      (q : ℝ) * ∑ k : Fin q × Fin q, (g k.1 u * h k.2 u) * (g k.1 v * h k.2 v) := by
    intro u v
    rw [TwoReplicaAux.aa_eq_gram hq, Fintype.sum_prod_type, mul_assoc]
    unfold rsTestCoef
    rw [Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hg, hh]
    ring
  rw [Fintype.sum_prod_type]
  simp_rw [key, ← Finset.mul_sum]
  rw [TwoReplicaAux.sum_sum_sum_mul_eq (fun (k : Fin q × Fin q) u => g k.1 u * h k.2 u),
    Fintype.sum_prod_type]
  have e2 : ∀ i j, ∑ u, g i u * h j u = n * (overlap σ τ i j - colorFrac σ i * colorFrac τ j) :=
    fun i j => sum_g_mul_h hn σ τ i j
  simp_rw [e2]
  unfold rsCorrDev
  simp_rw [mul_pow, ← Finset.mul_sum]
  ring

/-- `|t(x) q| ≤ 3/2` for `x ∈ [0,1]`, `q ≥ 3`. -/
theorem abs_tRe_mul_le {q : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |tRe q x * q| ≤ 3 / 2 := by
  have h1 := rs_tRe_nonpos (by omega : 2 ≤ q) hx0 hx1
  have h2 := rs_tRe_ge (by omega : 2 ≤ q) hx0
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  rw [div_le_iff₀ (by linarith)] at h2
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg (neg_nonneg.mpr h1) (sub_nonneg.mpr hq')]
  · nlinarith

/-- `λ S_τ(N) = ∑_{(u,v)} N_{uv} (λ t q ⟨e_{τ_u} - β, e_{τ_v} - β⟩)`. -/
theorem lam_mul_testStat {n q : ℕ} (t lam : ℝ) (τ : Fin n → Fin q) (N : RSGraph n) :
    lam * rsTestStat q t τ N =
      ∑ uv : Fin n × Fin n, (N uv : ℝ) * (lam * t * q * rsTestCoef τ (τ uv.1) (τ uv.2)) := by
  unfold rsTestStat
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun uv _ => ?_
  ring

end RSAnchorTestAux

open RSAnchorTestAux

/-- **`eq:rs-test`, first bound.** For `0 ≤ λ ≤ 1/3` and every `τ`, `e^{λ S_τ}` is
`𝖯_Δ`-summable and `E_{𝖯_Δ} e^{λ S_τ} ≤ e^{(9Δ/2) λ² n}`. -/
theorem rs_test_upper {q n : ℕ} (hq : 3 ≤ q) {x Δ lam : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hΔ : 0 ≤ Δ) (hn : 0 < n) (τ : Fin n → Fin q) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1 / 3) :
    Summable (fun N => poisPi (rsMean n Δ) N * Real.exp (lam * rsTestStat q (tRe q x) τ N)) ∧
      rsExp n Δ (fun N => Real.exp (lam * rsTestStat q (tRe q x) τ N)) ≤
        Real.exp (9 / 2 * Δ * lam ^ 2 * n) := by
  set t := tRe q x with ht
  set y : Fin n × Fin n → ℝ := fun uv => lam * t * q * rsTestCoef τ (τ uv.1) (τ uv.2) with hy
  have hmean : ∀ uv, 0 ≤ rsMean n Δ uv := fun uv => by unfold rsMean; positivity
  have H := hasSum_exp_lin hmean y
  have hfun : (fun N : RSGraph n => poisPi (rsMean n Δ) N * Real.exp (lam * rsTestStat q t τ N)) =
      fun N => poisPi (rsMean n Δ) N * Real.exp (∑ uv, (N uv : ℝ) * y uv) := by
    funext N
    rw [lam_mul_testStat]
  rw [← hfun] at H
  refine ⟨H.summable, ?_⟩
  unfold rsExp poisPiExp
  rw [H.tsum_eq, Real.exp_le_exp]
  -- the coefficients
  have hy_sum : ∑ uv, y uv = 0 := by
    simp only [hy]
    rw [← Finset.mul_sum, sum_testCoef hn, mul_zero]
  have hy_abs : ∀ uv, |y uv| ≤ 3 * lam := by
    intro uv
    simp only [hy]
    have h1 := abs_tRe_mul_le hq hx0 hx1
    have h2 := abs_testCoef_le hn τ (τ uv.1) (τ uv.2)
    rw [mul_assoc lam, abs_mul, abs_mul, abs_of_nonneg hl0]
    calc lam * |t * q| * |rsTestCoef τ (τ uv.1) (τ uv.2)|
        = lam * (|t * q| * |rsTestCoef τ (τ uv.1) (τ uv.2)|) := mul_assoc _ _ _
      _ ≤ lam * (3 / 2 * 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hl0
          exact mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ = 3 * lam := by ring
  have hy_sq : ∀ uv, Real.exp (y uv) - 1 - y uv ≤ 9 * lam ^ 2 := by
    intro uv
    have h1 : |y uv| ≤ 1 := by linarith [hy_abs uv]
    have h2 := Real.abs_exp_sub_one_sub_id_le h1
    have h3 : y uv ^ 2 ≤ (3 * lam) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hy_abs uv) 2
    calc Real.exp (y uv) - 1 - y uv ≤ |Real.exp (y uv) - 1 - y uv| := le_abs_self _
      _ ≤ y uv ^ 2 := h2
      _ ≤ (3 * lam) ^ 2 := h3
      _ = 9 * lam ^ 2 := by ring
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc ∑ uv, rsMean n Δ uv * (Real.exp (y uv) - 1)
      = ∑ uv, Δ / (2 * n) * (Real.exp (y uv) - 1 - y uv) + Δ / (2 * n) * ∑ uv, y uv := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun uv _ => ?_
        simp only [rsMean]
        ring
    _ ≤ ∑ _uv : Fin n × Fin n, Δ / (2 * n) * (9 * lam ^ 2) + Δ / (2 * n) * 0 := by
        rw [hy_sum]
        refine add_le_add (Finset.sum_le_sum fun uv _ => ?_) le_rfl
        exact mul_le_mul_of_nonneg_left (hy_sq uv) (by positivity)
    _ = 9 / 2 * Δ * lam ^ 2 * n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        field_simp
        ring

/-- **`eq:rs-signal` and `eq:rs-test`, second bound.** For every real `λ`:
`E_{𝖯^σ_Δ} e^{λ S_τ} ≥ exp(λ · (Δ n t² q²/2) ‖R_{σ,τ} - αβᵀ‖_F²)`. -/
theorem rs_test_lower {q n : ℕ} (hq : 3 ≤ q) {x Δ : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hΔ : 0 ≤ Δ) (hn : 0 < n) (σ τ : Fin n → Fin q) (lam : ℝ) :
    Real.exp (lam * (Δ * n * tRe q x ^ 2 * (q : ℝ) ^ 2 / 2 * rsCorrDev σ τ)) ≤
      poisPiExp (cpMean (fun a b => Δ * rsM q (tRe q x) a b) σ)
        (fun N => Real.exp (lam * rsTestStat q (tRe q x) τ N)) := by
  set t := tRe q x with ht
  set y : Fin n × Fin n → ℝ := fun uv => lam * t * q * rsTestCoef τ (τ uv.1) (τ uv.2) with hy
  set m := cpMean (fun a b => Δ * rsM q t a b) σ with hm
  have hmean : ∀ uv, 0 ≤ m uv := by
    intro uv
    simp only [hm, cpMean]
    have := (rs_rsM_mem hq hx0 hx1 (σ uv.1) (σ uv.2)).1
    have : 0 ≤ rsM q t (σ uv.1) (σ uv.2) := le_trans hx0 this
    positivity
  have H := hasSum_exp_lin hmean y
  have hfun : (fun N : RSGraph n => poisPi m N * Real.exp (lam * rsTestStat q t τ N)) =
      fun N => poisPi m N * Real.exp (∑ uv, (N uv : ℝ) * y uv) := by
    funext N
    rw [lam_mul_testStat]
  rw [← hfun] at H
  unfold poisPiExp
  rw [H.tsum_eq, Real.exp_le_exp]
  have hq0 : q ≠ 0 := by omega
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc lam * (Δ * n * t ^ 2 * (q : ℝ) ^ 2 / 2 * rsCorrDev σ τ)
      = Δ / (2 * n) * (lam * t * q) *
          ∑ uv : Fin n × Fin n, rsM q t (σ uv.1) (σ uv.2) * rsTestCoef τ (τ uv.1) (τ uv.2) := by
        rw [signal hq0 hn t σ τ]
        field_simp
    _ = ∑ uv, m uv * y uv := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun uv _ => ?_
        simp only [hm, hy, cpMean]
        field_simp
    _ ≤ ∑ uv, m uv * (Real.exp (y uv) - 1) := by
        refine Finset.sum_le_sum fun uv _ => mul_le_mul_of_nonneg_left ?_ (hmean uv)
        linarith [Real.add_one_le_exp (y uv)]

end

end ERZeroFreeness
