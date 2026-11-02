/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSBetheKS

/-!
# Appendix C: `d_cond(q,x) > 0` (non-vacuity certificate)

* `rs_dCond_pos`: for `q ≥ 3` and `x ∈ [0,1)`, `0 < d_cond(q,x)`; the proof gives
  `d_cond(q,x) ≥ 1/9`.

This is **not** used by Theorem C.1; it certifies that the hypothesis `0 < d < dCond q x_*` of
Theorem C.1 (`potts_zero_free_up_to_condensation`, `potts_zero_free_condensation`) is
satisfiable, i.e. that the Lean encoding of `Ψ` and `d_cond` is not degenerate.  (The paper
obtains non-vacuity only through `d₂(q) ≤ d_cond(q,0)`, which uses [CKPZ, Theorem 1.2]; the
self-contained argument below gives the cruder, `x`-independent bound `d_cond(q,x) ≥ 1/9`.)

## Proof

Fix `ν ∈ 𝒫_u`, `t = t(x) ∈ [-1/(q-1), 0]` and `0 ≤ r ≤ 1/9`; we show `Ψ_{r,x}(ν) ≤ 0`
(`RSBethePosAux.bethePsi_nonpos`), so no `r ≤ 1/9` lies in the set defining `d_cond`, and
`le_csInf` (the set is nonempty by `rs_ks_certificate`) gives `d_cond(q,x) ≥ 1/9`.

* `f_a(ρ) = qρ_a - 1` (`pf`) and `D_{ab} = E_ν[f_a f_b]` (`pD`): `∑_b D_{ab} = 0`,
  `|D_{ab}| ≤ (q-1)²`, and `(M_t ρ)_a = 1 + t f_a(ρ)` (`mvec_eq_pf`, `eq:rs-Mmu`).
* `V_k² = q⁻² ∑_{a,b} ∏_i (1 + t f_a(μ_i))(1 + t f_b(μ_i))`, so by
  `integral_fintype_prod_eq_pow`, `E V_k² = q⁻² ∑_{a,b} (1 + t²D_{ab})^k`.  With
  `v log v ≤ v² - v`, `E V_k = 1` (`rs_integral_betheV`) and `∑ D = 0`:
  `E[V_k log V_k] ≤ q⁻² ∑_{a,b} ((1+y)^k - 1 - ky)`, `y = t²D_{ab}`, and
  `(1+y)^k - 1 - ky ≤ C(k,2) y² 2^k` for `|y| ≤ 1` (induction on `k`; `|y| ≤ t²(q-1)² ≤ 1`).
* `E_x - 1 = (t/q) ∑_a f_a(μ₁) f_a(μ₂)`, so `E(E_x - 1)² = (t/q)² ∑ D²`, and
  `v log v ≥ (v-1) + (v-1)²/3` on `[0, 3/2]` (`E_x ∈ [0, 3/2]` by `rs_betheE_bounds`) together
  with `E E_x = 1` (`rs_integral_betheE`) gives `E[E_x log E_x] ≥ (t/q)² ∑ D² / 3`.
* `∑_k Pois(r)(k) C(k,2) 2^k = 2r² e^r`, so
  `Ψ_{r,x}(ν) ≤ q⁻² t² ∑D² · r (2 t² r e^r - 1/6) ≤ 0` because `t² ≤ 1/4`, `r ≤ 1/9`, `e^r ≤ 3`.
* Measurability is by composition (coordinates, finite sums and products, `Real.log`), and every
  integrand is bounded, hence integrable.
-/

open Polynomial Filter Topology MeasureTheory

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-! ### Helper lemmas (`RSBethePosAux`) -/

namespace RSBethePosAux

/-- `A_{ab} = q·[a = b] - 1`. -/
theorem rsA_eq' (q : ℕ) (a b : Fin q) :
    ((rsA q a b : ℤ) : ℝ) = (q : ℝ) * (if a = b then 1 else 0) - 1 := by
  unfold rsA; split_ifs <;> push_cast <;> ring

/-- `f_a(ρ) = q ρ_a - 1`. -/
def pf (q : ℕ) (a : Fin q) (ρ : rsSimplex q) : ℝ := (q : ℝ) * (ρ : Fin q → ℝ) a - 1

theorem measurable_coord {q : ℕ} (b : Fin q) :
    Measurable (fun ρ : rsSimplex q => (ρ : Fin q → ℝ) b) :=
  (measurable_pi_apply b).comp measurable_subtype_coe

theorem measurable_pf {q : ℕ} (a : Fin q) : Measurable (pf q a) :=
  (measurable_const.mul (measurable_coord a)).sub measurable_const

theorem abs_pf_le {q : ℕ} (hq : 2 ≤ q) (a : Fin q) (ρ : rsSimplex q) :
    |pf q a ρ| ≤ (q : ℝ) - 1 := by
  have h0 : 0 ≤ (ρ : Fin q → ℝ) a := stdSimplex.zero_le ρ a
  have h1 : (ρ : Fin q → ℝ) a ≤ 1 := stdSimplex.le_one ρ a
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  unfold pf
  rw [abs_le]; constructor <;> nlinarith

theorem abs_pf_le' {q : ℕ} (a : Fin q) (ρ : rsSimplex q) : |pf q a ρ| ≤ (q : ℝ) + 1 := by
  have h0 : 0 ≤ (ρ : Fin q → ℝ) a := stdSimplex.zero_le ρ a
  have h1 : (ρ : Fin q → ℝ) a ≤ 1 := stdSimplex.le_one ρ a
  have hq' : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  unfold pf
  rw [abs_le]; constructor <;> nlinarith

theorem sum_pf {q : ℕ} (ρ : rsSimplex q) : ∑ a, pf q a ρ = 0 := by
  unfold pf
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, stdSimplex.sum_eq_one]; simp

theorem mvec_eq_pf {q : ℕ} (t : ℝ) (ρ : rsSimplex q) (a : Fin q) :
    betheMvec q t (ρ : Fin q → ℝ) a = 1 + t * pf q a ρ := by
  have hs : ∑ b, (ρ : Fin q → ℝ) b = 1 := stdSimplex.sum_eq_one ρ
  unfold betheMvec rsM pf
  have h : ∀ b, (1 + t * ((rsA q a b : ℤ) : ℝ)) * (ρ : Fin q → ℝ) b =
      (1 - t) * (ρ : Fin q → ℝ) b +
        t * (q : ℝ) * (if a = b then (ρ : Fin q → ℝ) b else 0) := by
    intro b; rw [rsA_eq']; split_ifs <;> ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, hs]
  ring

theorem measurable_mvec {q : ℕ} (t : ℝ) (a : Fin q) :
    Measurable (fun ρ : rsSimplex q => betheMvec q t (ρ : Fin q → ℝ) a) := by
  unfold betheMvec
  exact Finset.measurable_sum _ fun b _ => measurable_const.mul (measurable_coord b)

theorem integrable_of_bdd {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    {g : X → ℝ} (hg : Measurable g) (C : ℝ) (hC : ∀ ρ, |g ρ| ≤ C) :
    Integrable g ν :=
  Integrable.of_bound hg.aestronglyMeasurable C
    (Eventually.of_forall fun ρ => by rw [Real.norm_eq_abs]; exact hC ρ)

theorem integrable_pf {q : ℕ} (ν : Measure (rsSimplex q)) [IsFiniteMeasure ν] (a : Fin q) :
    Integrable (pf q a) ν :=
  integrable_of_bdd ν (measurable_pf a) _ (abs_pf_le' a)

theorem integrable_pf_mul {q : ℕ} (ν : Measure (rsSimplex q)) [IsFiniteMeasure ν]
    (a b : Fin q) : Integrable (fun ρ => pf q a ρ * pf q b ρ) ν := by
  refine integrable_of_bdd ν ((measurable_pf a).mul (measurable_pf b)) (((q : ℝ) + 1) ^ 2)
    fun ρ => ?_
  rw [abs_mul, sq]
  exact mul_le_mul (abs_pf_le' a ρ) (abs_pf_le' b ρ) (abs_nonneg _)
    ((abs_nonneg _).trans (abs_pf_le' a ρ))

theorem integral_pf {q : ℕ} {ν : ProbabilityMeasure (rsSimplex q)} (hν : ν ∈ rsPu q)
    (a : Fin q) : ∫ ρ, pf q a ρ ∂(ν : Measure (rsSimplex q)) = 0 := by
  have hq : (q : ℝ) ≠ 0 := by
    have : 0 < q := Fin.pos a
    exact_mod_cast this.ne'
  have hi : Integrable (fun ρ : rsSimplex q => (ρ : Fin q → ℝ) a) (ν : Measure (rsSimplex q)) :=
    integrable_of_bdd _ (measurable_coord a) 1 fun ρ => by
      rw [abs_le]; exact ⟨by linarith [stdSimplex.zero_le ρ a], stdSimplex.le_one ρ a⟩
  unfold pf
  rw [integral_sub (hi.const_mul _) (integrable_const _), integral_const_mul, hν a,
    integral_const]
  simp [hq]

/-- `D_{ab} = E_ν[f_a f_b]`. -/
def pD (q : ℕ) (ν : Measure (rsSimplex q)) (a b : Fin q) : ℝ :=
  ∫ ρ, pf q a ρ * pf q b ρ ∂ν

theorem sum_pD {q : ℕ} (ν : Measure (rsSimplex q)) [IsFiniteMeasure ν] (a : Fin q) :
    ∑ b, pD q ν a b = 0 := by
  unfold pD
  rw [← integral_finsetSum _ fun b _ => integrable_pf_mul ν a b]
  simp_rw [← Finset.mul_sum, sum_pf, mul_zero, integral_zero]

theorem abs_pD_le {q : ℕ} (hq : 2 ≤ q) (ν : ProbabilityMeasure (rsSimplex q)) (a b : Fin q) :
    |pD q (ν : Measure (rsSimplex q)) a b| ≤ ((q : ℝ) - 1) ^ 2 := by
  have h := norm_integral_le_of_norm_le_const (μ := (ν : Measure (rsSimplex q)))
    (f := fun ρ => pf q a ρ * pf q b ρ) (C := ((q : ℝ) - 1) ^ 2)
    (Eventually.of_forall fun ρ => by
      rw [Real.norm_eq_abs, abs_mul, sq]
      exact mul_le_mul (abs_pf_le hq a ρ) (abs_pf_le hq b ρ) (abs_nonneg _)
        ((abs_nonneg _).trans (abs_pf_le hq a ρ)))
  simpa [pD] using h

theorem integral_one_add_mul {q : ℕ} {ν : ProbabilityMeasure (rsSimplex q)} (hν : ν ∈ rsPu q)
    (α : ℝ) (a b : Fin q) :
    ∫ ρ, (1 + α * pf q a ρ) * (1 + α * pf q b ρ) ∂(ν : Measure (rsSimplex q)) =
      1 + α ^ 2 * pD q (ν : Measure (rsSimplex q)) a b := by
  have i1 := (integrable_pf (ν : Measure (rsSimplex q)) a).const_mul α
  have i2 := (integrable_pf (ν : Measure (rsSimplex q)) b).const_mul α
  have i3 := (integrable_pf_mul (ν : Measure (rsSimplex q)) a b).const_mul (α ^ 2)
  have i0 := integrable_const (μ := (ν : Measure (rsSimplex q))) (1 : ℝ)
  have e : ∀ ρ, (1 + α * pf q a ρ) * (1 + α * pf q b ρ) =
      ((1 + α * pf q a ρ) + α * pf q b ρ) + α ^ 2 * (pf q a ρ * pf q b ρ) := by
    intro ρ; ring
  have j1 : Integrable (fun ρ => 1 + α * pf q a ρ) (ν : Measure (rsSimplex q)) := i0.add i1
  have j2 : Integrable (fun ρ => 1 + α * pf q a ρ + α * pf q b ρ)
      (ν : Measure (rsSimplex q)) := j1.add i2
  simp_rw [e]
  rw [integral_add j2 i3, integral_add j1 i2, integral_add i0 i1,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_pf hν, integral_pf hν]
  simp [pD]

/-- `log w ≤ (w - w⁻¹)/2` for `w ≥ 1`. -/
theorem log_le_half_sub_inv {w : ℝ} (hw : 1 ≤ w) : Real.log w ≤ (w - w⁻¹) / 2 := by
  have hw0 : 0 < w := by linarith
  have h := Real.self_le_sinh_iff.mpr (Real.log_nonneg hw)
  rw [Real.sinh_eq, Real.exp_neg, Real.exp_log hw0] at h
  exact h

/-- `y + y²/2 ≤ -log(1-y)` for `0 ≤ y < 1`. -/
theorem add_sq_le_neg_log {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    y + y ^ 2 / 2 ≤ -Real.log (1 - y) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := y) (by rw [abs_of_nonneg hy0]; exact hy1)
  have h2 := sum_le_hasSum (Finset.range 2) (fun i _ => by positivity) h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h2
  norm_num at h2
  linarith

/-- `(v - 1) + (v - 1)²/3 ≤ v log v` for `0 ≤ v ≤ 3/2`. -/
theorem mulLog_ge {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 3 / 2) :
    (v - 1) + (v - 1) ^ 2 / 3 ≤ v * Real.log v := by
  rcases hv0.eq_or_lt with hv | hv
  · subst hv; norm_num
  rcases le_or_gt v 1 with hv1' | hv1'
  · -- `0 < v ≤ 1`: `v log v ≥ (v² - 1)/2`
    have h := log_le_half_sub_inv (one_le_inv_iff₀.mpr ⟨hv, hv1'⟩)
    rw [Real.log_inv, inv_inv] at h
    have h1 : (v ^ 2 - 1) / 2 ≤ v * Real.log v := by
      have : v * (-Real.log v) ≤ v * ((v⁻¹ - v) / 2) := mul_le_mul_of_nonneg_left h hv.le
      have e : v * ((v⁻¹ - v) / 2) = (1 - v ^ 2) / 2 := by field_simp
      linarith
    nlinarith
  · -- `1 < v ≤ 3/2`: `v log v ≥ (v-1) + (v-1)²/(2v)`
    have hy0 : 0 ≤ 1 - v⁻¹ := by
      have : v⁻¹ < 1 := inv_lt_one_of_one_lt₀ hv1'
      linarith
    have hy1 : 1 - v⁻¹ < 1 := by
      have : 0 < v⁻¹ := inv_pos.mpr hv
      linarith
    have h := add_sq_le_neg_log hy0 hy1
    rw [sub_sub_cancel, Real.log_inv, neg_neg] at h
    have h1 : (v - 1) + (v - 1) ^ 2 / (2 * v) ≤ v * Real.log v := by
      have : v * ((1 - v⁻¹) + (1 - v⁻¹) ^ 2 / 2) ≤ v * Real.log v :=
        mul_le_mul_of_nonneg_left h hv.le
      have e : v * ((1 - v⁻¹) + (1 - v⁻¹) ^ 2 / 2) = (v - 1) + (v - 1) ^ 2 / (2 * v) := by
        field_simp
      linarith
    have h2 : (v - 1) ^ 2 / 3 ≤ (v - 1) ^ 2 / (2 * v) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
    linarith

/-- `v log v ≤ v² - v` for `v ≥ 0`. -/
theorem mulLog_le {v : ℝ} (hv : 0 ≤ v) : v * Real.log v ≤ v ^ 2 - v := by
  rcases hv.eq_or_lt with rfl | hv'
  · simp
  · have h := Real.log_le_sub_one_of_pos hv'
    have := mul_le_mul_of_nonneg_left h hv
    nlinarith

/-- `|v log v| ≤ 1 + v²` for `v ≥ 0`. -/
theorem abs_mulLog_le {v : ℝ} (hv : 0 ≤ v) : |v * Real.log v| ≤ 1 + v ^ 2 := by
  rcases hv.eq_or_lt with rfl | hv'
  · simp
  · have h1 := Real.log_le_sub_one_of_pos hv'
    have h2 := Real.one_sub_inv_le_log_of_pos hv'
    have h3 : v * (1 - v⁻¹) ≤ v * Real.log v := mul_le_mul_of_nonneg_left h2 hv
    have h4 : v * Real.log v ≤ v * (v - 1) := mul_le_mul_of_nonneg_left h1 hv
    rw [mul_sub, mul_one, mul_inv_cancel₀ hv'.ne'] at h3
    rw [abs_le]
    constructor <;> nlinarith

/-- The Poisson generating function `∑_k Pois(λ)(k) y^k = e^{λ(y-1)}`. -/
theorem hasSum_poisPMF_mul_pow' (lam y : ℝ) :
    HasSum (fun k => poisPMF lam k * y ^ k) (Real.exp (lam * (y - 1))) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (lam * y)
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (Real.exp (-lam))
  have e1 : (fun k : ℕ => poisPMF lam k * y ^ k) =
      fun k : ℕ => Real.exp (-lam) * ((lam * y) ^ k / (k.factorial : ℝ)) := by
    funext k
    unfold poisPMF
    rw [mul_pow]
    ring
  have e2 : Real.exp (lam * (y - 1)) = Real.exp (-lam) * Real.exp (lam * y) := by
    rw [← Real.exp_add]
    ring_nf
  rw [e1, e2]
  exact h2

/-- `∑_k Pois(s)(k) C(k,2) z^k = (sz)² e^{s(z-1)}/2`. -/
theorem hasSum_pois_choose' (s z : ℝ) :
    HasSum (fun k : ℕ => poisPMF s k * ((k.choose 2 : ℝ) * z ^ k))
      ((s * z) ^ 2 * Real.exp (s * (z - 1)) / 2) := by
  have h := (hasSum_poisPMF_mul_pow' s z).mul_left ((s * z) ^ 2 / 2)
  have e : ∀ n : ℕ, poisPMF s (n + 2) * ((((n + 2).choose 2 : ℕ) : ℝ) * z ^ (n + 2)) =
      (s * z) ^ 2 / 2 * (poisPMF s n * z ^ n) := by
    intro n
    unfold poisPMF
    rw [Nat.cast_choose_two, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have h' : HasSum (fun n : ℕ => poisPMF s (n + 2) * ((((n + 2).choose 2 : ℕ) : ℝ) * z ^ (n + 2)))
      ((s * z) ^ 2 * Real.exp (s * (z - 1)) / 2) := by
    rw [funext e, show (s * z) ^ 2 * Real.exp (s * (z - 1)) / 2 =
      (s * z) ^ 2 / 2 * Real.exp (s * (z - 1)) by ring]
    exact h
  have h0 : ∑ i ∈ Finset.range 2, poisPMF s i * ((i.choose 2 : ℝ) * z ^ i) = 0 := by
    simp [Finset.sum_range_succ]
  refine (hasSum_nat_add_iff' 2).mp ?_
  rw [h0, sub_zero]
  exact h'

/-- `(1+y)^k - 1 - ky ≤ C(k,2) y² 2^k` for `|y| ≤ 1`. -/
theorem pow_sub_le {y : ℝ} (hy0 : -1 ≤ y) (hy1 : y ≤ 1) (k : ℕ) :
    (1 + y) ^ k - 1 - k * y ≤ (k.choose 2 : ℝ) * y ^ 2 * 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hb : 0 ≤ (1 + y) ^ k - 1 - k * y := by
      have := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ y) k
      linarith
    have e : (1 + y) ^ (k + 1) - 1 - ((k + 1 : ℕ) : ℝ) * y =
        (1 + y) * ((1 + y) ^ k - 1 - k * y) + k * y ^ 2 := by
      push_cast; ring
    have hc : ((k + 1).choose 2 : ℝ) = k + (k.choose 2 : ℝ) := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]; push_cast; ring
    rw [e, hc]
    have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 : (1 + y) * ((1 + y) ^ k - 1 - k * y) ≤ 2 * ((k.choose 2 : ℝ) * y ^ 2 * 2 ^ k) := by
      calc (1 + y) * ((1 + y) ^ k - 1 - k * y) ≤ 2 * ((1 + y) ^ k - 1 - k * y) :=
            mul_le_mul_of_nonneg_right (by linarith) hb
        _ ≤ 2 * ((k.choose 2 : ℝ) * y ^ 2 * 2 ^ k) := by linarith
    have h3 : (k : ℝ) * y ^ 2 ≤ k * y ^ 2 * (2 * 2 ^ k) := by
      have : (1 : ℝ) ≤ 2 * 2 ^ k := by linarith
      nlinarith [mul_nonneg hk hy2]
    have e2 : ((k : ℝ) + (k.choose 2 : ℝ)) * y ^ 2 * 2 ^ (k + 1) =
        2 * ((k.choose 2 : ℝ) * y ^ 2 * 2 ^ k) + k * y ^ 2 * (2 * 2 ^ k) := by ring
    rw [e2]
    linarith

/-- `V_k` is measurable as a function of `μ : Fin k → rsSimplex q`. -/
theorem measurable_betheV {q k : ℕ} (t : ℝ) :
    Measurable (fun μ : Fin k → rsSimplex q => betheV q t (fun i => (μ i : Fin q → ℝ))) := by
  unfold betheV
  exact measurable_const.mul (Finset.measurable_sum _ fun a _ =>
    Finset.measurable_prod _ fun i _ => (measurable_mvec t a).comp (measurable_pi_apply i))

/-- `E` is measurable as a function of `μ : Fin 2 → rsSimplex q`. -/
theorem measurable_betheE {q : ℕ} (t : ℝ) :
    Measurable (fun μ : Fin 2 → rsSimplex q =>
      betheE q t (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ)) := by
  unfold betheE
  exact Finset.measurable_sum _ fun a _ =>
    ((measurable_coord a).comp (measurable_pi_apply 0)).mul
      ((measurable_mvec t a).comp (measurable_pi_apply 1))

theorem integrable_one_add_mul {q : ℕ} (ν : Measure (rsSimplex q)) [IsFiniteMeasure ν]
    (α : ℝ) (a b : Fin q) :
    Integrable (fun ρ => (1 + α * pf q a ρ) * (1 + α * pf q b ρ)) ν := by
  have i1 := (integrable_pf ν a).const_mul α
  have i2 := (integrable_pf ν b).const_mul α
  have i3 := (integrable_pf_mul ν a b).const_mul (α ^ 2)
  have i0 := integrable_const (μ := ν) (1 : ℝ)
  have j1 : Integrable (fun ρ => 1 + α * pf q a ρ) ν := i0.add i1
  have j2 : Integrable (fun ρ => 1 + α * pf q a ρ + α * pf q b ρ) ν := j1.add i2
  have j3 : Integrable (fun ρ => 1 + α * pf q a ρ + α * pf q b ρ +
      α ^ 2 * (pf q a ρ * pf q b ρ)) ν := j2.add i3
  exact j3.congr (Eventually.of_forall fun ρ => by ring)

theorem betheV_sq_eq {q k : ℕ} (t : ℝ) (μ : Fin k → rsSimplex q) :
    betheV q t (fun i => (μ i : Fin q → ℝ)) ^ 2 =
      ((q : ℝ) ^ 2)⁻¹ * ∑ a, ∑ b, ∏ i, ((1 + t * pf q a (μ i)) * (1 + t * pf q b (μ i))) := by
  unfold betheV
  simp_rw [mvec_eq_pf]
  rw [mul_pow, inv_pow, sq (∑ a, _), Finset.sum_mul_sum]
  simp_rw [Finset.prod_mul_distrib]

theorem integral_betheV_sq {q : ℕ} (t : ℝ) {ν : ProbabilityMeasure (rsSimplex q)}
    (hν : ν ∈ rsPu q) (k : ℕ) :
    ∫ μ : Fin k → rsSimplex q, betheV q t (fun i => (μ i : Fin q → ℝ)) ^ 2
      ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q))) =
      ((q : ℝ) ^ 2)⁻¹ * ∑ a, ∑ b, (1 + t ^ 2 * pD q (ν : Measure (rsSimplex q)) a b) ^ k := by
  simp_rw [betheV_sq_eq]
  have hint : ∀ a b, Integrable (fun μ : Fin k → rsSimplex q =>
      ∏ i, ((1 + t * pf q a (μ i)) * (1 + t * pf q b (μ i))))
      (Measure.pi fun _ => (ν : Measure (rsSimplex q))) := fun a b =>
    Integrable.fintype_prod (f := fun _ ρ => (1 + t * pf q a ρ) * (1 + t * pf q b ρ))
      fun _ => integrable_one_add_mul _ t a b
  rw [integral_const_mul,
    integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint a b]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => hint a b]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_fintype_prod_eq_pow (fun ρ => (1 + t * pf q a ρ) * (1 + t * pf q b ρ)),
    integral_one_add_mul hν, Fintype.card_fin]

theorem integral_mulLog_betheV_le {q : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {ν : ProbabilityMeasure (rsSimplex q)} (hν : ν ∈ rsPu q) (k : ℕ) :
    ∫ μ : Fin k → rsSimplex q, betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)) *
        Real.log (betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)))
      ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q))) ≤
      ((q : ℝ) ^ 2)⁻¹ * ∑ a, ∑ b,
        (1 + tRe q x ^ 2 * pD q (ν : Measure (rsSimplex q)) a b) ^ k - 1 := by
  have hVm := measurable_betheV (q := q) (k := k) (tRe q x)
  have hVb : ∀ μ : Fin k → rsSimplex q, 0 ≤ betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)) ∧
      betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)) ≤ (3 / 2) ^ k := fun μ =>
    rs_betheV_bounds hq hx0 hx1 (μ := fun i => (μ i : Fin q → ℝ)) fun i => (μ i).2
  have iV : Integrable (fun μ : Fin k → rsSimplex q =>
      betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)))
      (Measure.pi fun _ => (ν : Measure (rsSimplex q))) :=
    integrable_of_bdd _ hVm ((3 / 2) ^ k) fun μ => by
      rw [abs_of_nonneg (hVb μ).1]; exact (hVb μ).2
  have iV2 : Integrable (fun μ : Fin k → rsSimplex q =>
      betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)) ^ 2)
      (Measure.pi fun _ => (ν : Measure (rsSimplex q))) :=
    integrable_of_bdd _ (hVm.pow_const 2) (((3 / 2) ^ k) ^ 2) fun μ => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (hVb μ).1 (hVb μ).2 2
  have iVl : Integrable (fun μ : Fin k → rsSimplex q =>
      betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)) *
        Real.log (betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ))))
      (Measure.pi fun _ => (ν : Measure (rsSimplex q))) :=
    integrable_of_bdd _ (hVm.mul (Real.measurable_log.comp hVm)) (1 + ((3 / 2) ^ k) ^ 2)
      fun μ => by
        have h1 := abs_mulLog_le (hVb μ).1
        have h2 := pow_le_pow_left₀ (hVb μ).1 (hVb μ).2 2
        linarith
  calc _ ≤ ∫ μ : Fin k → rsSimplex q, (betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)) ^ 2 -
          betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)))
          ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q))) :=
        integral_mono iVl (iV2.sub iV) fun μ => mulLog_le (hVb μ).1
    _ = _ := by
        rw [integral_sub iV2 iV, integral_betheV_sq _ hν, rs_integral_betheV (by omega) _ hν]

theorem betheE_sub_one {q : ℕ} (hq : q ≠ 0) (t : ℝ) (ρ0 ρ1 : rsSimplex q) :
    betheE q t (ρ0 : Fin q → ℝ) (ρ1 : Fin q → ℝ) - 1 =
      t / q * ∑ a, pf q a ρ0 * pf q a ρ1 := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have h1 : ∀ a, (ρ0 : Fin q → ℝ) a * (1 + t * pf q a ρ1) =
      (ρ0 : Fin q → ℝ) a + t / q * (pf q a ρ0 * pf q a ρ1) + t / q * pf q a ρ1 := by
    intro a; unfold pf; field_simp; ring
  unfold betheE
  simp_rw [mvec_eq_pf, h1, Finset.sum_add_distrib, ← Finset.mul_sum, stdSimplex.sum_eq_one,
    sum_pf]
  ring

theorem betheE_sub_one_sq {q : ℕ} (hq : q ≠ 0) (t : ℝ) (μ : Fin 2 → rsSimplex q) :
    (betheE q t (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ) - 1) ^ 2 =
      (t / q) ^ 2 * ∑ a, ∑ b, ∏ i, (pf q a (μ i) * pf q b (μ i)) := by
  rw [betheE_sub_one hq, mul_pow, sq (∑ a, _), Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Fin.prod_univ_two]; ring

theorem integral_betheE_sub_one_sq {q : ℕ} (hq : q ≠ 0) (t : ℝ)
    (ν : ProbabilityMeasure (rsSimplex q)) :
    ∫ μ : Fin 2 → rsSimplex q, (betheE q t (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ) - 1) ^ 2
      ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q))) =
      (t / q) ^ 2 * ∑ a, ∑ b, pD q (ν : Measure (rsSimplex q)) a b ^ 2 := by
  simp_rw [betheE_sub_one_sq hq]
  have hint : ∀ a b, Integrable (fun μ : Fin 2 → rsSimplex q =>
      ∏ i, (pf q a (μ i) * pf q b (μ i))) (Measure.pi fun _ => (ν : Measure (rsSimplex q))) :=
    fun a b => Integrable.fintype_prod (f := fun _ ρ => pf q a ρ * pf q b ρ)
      fun _ => integrable_pf_mul _ a b
  rw [integral_const_mul,
    integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint a b]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => hint a b]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_fintype_prod_eq_pow (fun ρ => pf q a ρ * pf q b ρ), Fintype.card_fin]
  rfl

theorem integral_mulLog_betheE_ge {q : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {ν : ProbabilityMeasure (rsSimplex q)} (hν : ν ∈ rsPu q) :
    (tRe q x / q) ^ 2 * (∑ a, ∑ b, pD q (ν : Measure (rsSimplex q)) a b ^ 2) / 3 ≤
      ∫ μ : Fin 2 → rsSimplex q, betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ) *
          Real.log (betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ))
        ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q))) := by
  have hq0 : q ≠ 0 := by omega
  have hEm := measurable_betheE (q := q) (tRe q x)
  have hEb : ∀ μ : Fin 2 → rsSimplex q,
      0 ≤ betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ) ∧
        betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ) ≤ 3 / 2 := fun μ =>
    rs_betheE_bounds hq hx0 hx1 (μ 0).2 (μ 1).2
  have iE : Integrable (fun μ : Fin 2 → rsSimplex q =>
      betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ))
      (Measure.pi fun _ => (ν : Measure (rsSimplex q))) :=
    integrable_of_bdd _ hEm (3 / 2) fun μ => by
      rw [abs_of_nonneg (hEb μ).1]; exact (hEb μ).2
  have iE1 : Integrable (fun μ : Fin 2 → rsSimplex q =>
      betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ) - 1)
      (Measure.pi fun _ => (ν : Measure (rsSimplex q))) := iE.sub (integrable_const 1)
  have iE2 : Integrable (fun μ : Fin 2 → rsSimplex q =>
      (betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ) - 1) ^ 2 / 3)
      (Measure.pi fun _ => (ν : Measure (rsSimplex q))) :=
    integrable_of_bdd _ (((hEm.sub measurable_const).pow_const 2).div_const 3) 1 fun μ => by
      have h0 := (hEb μ).1
      have h1 := (hEb μ).2
      rw [abs_of_nonneg (by positivity)]
      nlinarith
  have iEl : Integrable (fun μ : Fin 2 → rsSimplex q =>
      betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ) *
        Real.log (betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ)))
      (Measure.pi fun _ => (ν : Measure (rsSimplex q))) :=
    integrable_of_bdd _ (hEm.mul (Real.measurable_log.comp hEm)) (1 + (3 / 2) ^ 2)
      fun μ => by
        have h1 := abs_mulLog_le (hEb μ).1
        have h2 := pow_le_pow_left₀ (hEb μ).1 (hEb μ).2 2
        linarith
  have hmean : ∫ μ : Fin 2 → rsSimplex q,
      (betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ) - 1)
      ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q))) = 0 := by
    rw [integral_sub iE (integrable_const 1), rs_integral_betheE (by omega) _ hν]
    simp
  calc _ = ∫ μ : Fin 2 → rsSimplex q,
        ((betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ) - 1) +
          (betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ) - 1) ^ 2 / 3)
        ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q))) := by
        rw [integral_add iE1 iE2, hmean, integral_div, integral_betheE_sub_one_sq hq0]
        ring
    _ ≤ _ := integral_mono (iE1.add iE2) iEl fun μ => mulLog_ge (hEb μ).1 (hEb μ).2

/-- **Key estimate.** For `x ∈ [0,1]` and `0 ≤ r ≤ 1/9`, `Ψ_{r,x}(ν) ≤ 0` for every `ν ∈ 𝒫_u`. -/
theorem bethePsi_nonpos {q : ℕ} (hq : 3 ≤ q) {x r : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 9) {ν : ProbabilityMeasure (rsSimplex q)}
    (hν : ν ∈ rsPu q) : bethePsi q r x ν ≤ 0 := by
  have hq2 : 2 ≤ q := by omega
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  have htl : -1 / ((q : ℝ) - 1) ≤ tRe q x := rs_tRe_ge hq2 hx0
  have htu : tRe q x ≤ 0 := rs_tRe_nonpos hq2 hx0 hx1
  have htq : -1 ≤ tRe q x * ((q : ℝ) - 1) := by
    rwa [div_le_iff₀ (by linarith)] at htl
  have htq2 : tRe q x ^ 2 * ((q : ℝ) - 1) ^ 2 ≤ 1 := by
    have h0 : tRe q x * ((q : ℝ) - 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg htu (by linarith)
    have e : tRe q x ^ 2 * ((q : ℝ) - 1) ^ 2 = (tRe q x * ((q : ℝ) - 1)) ^ 2 := by ring
    rw [e]
    nlinarith
  have ht4 : tRe q x ^ 2 ≤ 1 / 4 := by nlinarith
  set t := tRe q x with ht
  set D := pD q (ν : Measure (rsSimplex q)) with hD
  set S := ∑ a, ∑ b, D a b ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hy : ∀ a b, -1 ≤ t ^ 2 * D a b ∧ t ^ 2 * D a b ≤ 1 := by
    intro a b
    have h := abs_pD_le hq2 ν a b
    rw [abs_le] at h
    have ht0 : 0 ≤ t ^ 2 := sq_nonneg t
    constructor <;> nlinarith
  -- the `V`-terms
  have hV : ∀ k : ℕ, ∫ μ : Fin k → rsSimplex q, betheV q t (fun i => (μ i : Fin q → ℝ)) *
        Real.log (betheV q t (fun i => (μ i : Fin q → ℝ)))
        ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q))) ≤
      ((q : ℝ) ^ 2)⁻¹ * t ^ 4 * S * ((k.choose 2 : ℝ) * 2 ^ k) := by
    intro k
    refine (integral_mulLog_betheV_le hq hx0 hx1 hν k).trans ?_
    have hsum : ∑ a, ∑ b, (1 + t ^ 2 * D a b) ^ k = (q : ℝ) ^ 2 +
        ∑ a, ∑ b, ((1 + t ^ 2 * D a b) ^ k - 1 - k * (t ^ 2 * D a b)) := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hD, sum_pD, mul_zero, sub_zero,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hle : ∑ a, ∑ b, ((1 + t ^ 2 * D a b) ^ k - 1 - k * (t ^ 2 * D a b)) ≤
        ∑ a, ∑ b, ((k.choose 2 : ℝ) * (t ^ 2 * D a b) ^ 2 * 2 ^ k) :=
      Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
        pow_sub_le (hy a b).1 (hy a b).2 k
    have heq : ∑ a, ∑ b, ((k.choose 2 : ℝ) * (t ^ 2 * D a b) ^ 2 * 2 ^ k) =
        t ^ 4 * S * ((k.choose 2 : ℝ) * 2 ^ k) := by
      rw [hS, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [hsum, mul_add, inv_mul_cancel₀ hqpos.ne', add_sub_cancel_left]
    calc ((q : ℝ) ^ 2)⁻¹ * ∑ a, ∑ b, ((1 + t ^ 2 * D a b) ^ k - 1 - k * (t ^ 2 * D a b)) ≤
          ((q : ℝ) ^ 2)⁻¹ * (t ^ 4 * S * ((k.choose 2 : ℝ) * 2 ^ k)) :=
          mul_le_mul_of_nonneg_left (hle.trans heq.le) (by positivity)
      _ = _ := by ring
  -- summing over `k`
  have hpois : HasSum (fun k : ℕ => poisPMF r k *
      (((q : ℝ) ^ 2)⁻¹ * t ^ 4 * S * ((k.choose 2 : ℝ) * 2 ^ k)))
      (((q : ℝ) ^ 2)⁻¹ * t ^ 4 * S * (2 * r ^ 2 * Real.exp r)) := by
    have h := (hasSum_pois_choose' r 2).mul_left (((q : ℝ) ^ 2)⁻¹ * t ^ 4 * S)
    have e : (r * 2) ^ 2 * Real.exp (r * (2 - 1)) / 2 = 2 * r ^ 2 * Real.exp r := by
      norm_num; ring
    rw [e] at h
    have e2 : (fun k : ℕ => poisPMF r k *
        (((q : ℝ) ^ 2)⁻¹ * t ^ 4 * S * ((k.choose 2 : ℝ) * 2 ^ k))) =
        fun k : ℕ => ((q : ℝ) ^ 2)⁻¹ * t ^ 4 * S * (poisPMF r k * ((k.choose 2 : ℝ) * 2 ^ k)) := by
      funext k
      ring
    rw [e2]
    exact h
  have hsumm := rs_summable_bethe_series hq hr0 hx0 hx1 ν
  have h1 := hasSum_le (fun k => mul_le_mul_of_nonneg_left (hV k) (poisPMF_nonneg hr0 k))
    hsumm.hasSum hpois
  have h2 := mul_le_mul_of_nonneg_left (integral_mulLog_betheE_ge hq hx0 hx1 hν)
    (by positivity : (0 : ℝ) ≤ r / 2)
  -- the final inequality
  have hexp : Real.exp r ≤ 3 := by
    have := Real.exp_one_lt_d9
    have : Real.exp r ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hb : t ^ 2 * r * Real.exp r ≤ 1 / 12 := by
    have h3 : t ^ 2 * r ≤ 1 / 4 * (1 / 9) :=
      mul_le_mul ht4 hr1 hr0 (by norm_num)
    calc t ^ 2 * r * Real.exp r ≤ 1 / 4 * (1 / 9) * 3 :=
          mul_le_mul h3 hexp (Real.exp_pos r).le (by norm_num)
      _ = 1 / 12 := by norm_num
  have hK : 0 ≤ ((q : ℝ) ^ 2)⁻¹ * t ^ 2 * S := by positivity
  have hfin : ((q : ℝ) ^ 2)⁻¹ * t ^ 4 * S * (2 * r ^ 2 * Real.exp r) -
      r / 2 * ((t / q) ^ 2 * S / 3) =
      ((q : ℝ) ^ 2)⁻¹ * t ^ 2 * S * r * (2 * (t ^ 2 * r * Real.exp r) - 1 / 6) := by
    field_simp
    ring
  have hneg : ((q : ℝ) ^ 2)⁻¹ * t ^ 2 * S * r * (2 * (t ^ 2 * r * Real.exp r) - 1 / 6) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hK hr0) (by linarith)
  unfold bethePsi
  linarith

end RSBethePosAux

/-- **Non-vacuity certificate.** `0 < d_cond(q,x)` for `x ∈ [0,1)` (`q ≥ 3`). -/
theorem rs_dCond_pos {q : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 < dCond q x := by
  -- the set defining `d_cond` is nonempty (Kesten–Stigum certificate) ...
  have hs : (tRe q x ^ 2)⁻¹ < (tRe q x ^ 2)⁻¹ + 1 := by linarith
  obtain ⟨ν, hν, hpos⟩ := rs_ks_certificate hq hx0 hx1 hs
  have hne : {r : ℝ | 0 < r ∧ ∃ ν ∈ rsPu q, 0 < bethePsi q r x ν}.Nonempty :=
    ⟨_, by positivity, ν, hν, hpos⟩
  -- ... and bounded below by `1/9`, since `Ψ_{r,x} ≤ 0` on `𝒫_u` for `r ≤ 1/9`
  have h : (1 / 9 : ℝ) ≤ dCond q x := by
    unfold dCond
    refine le_csInf hne ?_
    rintro r ⟨hr0, ν', hν', hpos'⟩
    exact le_of_not_gt fun hlt => absurd hpos'
      (not_lt.2 (RSBethePosAux.bethePsi_nonpos hq hx0 hx1.le hr0.le hlt.le hν'))
  linarith

end

end ERZeroFreeness
