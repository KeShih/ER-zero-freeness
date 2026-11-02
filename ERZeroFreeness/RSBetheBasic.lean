/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSModel
import ERZeroFreeness.RSPoisPi

/-!
# Appendix C: basic facts about the Bethe functional and `d_cond`

API for `bethePsi`, `rsPu` and `dCond` (`eq:bethe-condensation`), used by the three parts of
Lemma C.3 (`lem:rs-ckpz`):

* `rs_dCond_nonneg`, `rs_dCond_le_of_pos`, `rs_bethePsi_nonpos_of_lt_dCond`: the order
  properties of the infimum; the last one is the bound `sup_ν Ψ_{s,x}(ν) ≤ 0` for
  `0 < s < d_cond(q,x)`, which is the input of `CKPZProp36` ([CKPZ, Prop. 3.6]) with `η = 0`;
* `rs_betheV_bounds`, `rs_betheE_bounds`: `0 ≤ V_k ≤ (3/2)^k` and `0 ≤ E_x ≤ 3/2` at real
  `x ∈ [0,1]`;
* `rs_integral_betheV`, `rs_integral_betheE`: `E[V_k] = 1` and `E[E_x] = 1` for `ν ∈ 𝒫_u` (stated
  after `eq:bethe-condensation`);
* `rs_summable_bethe_series`: the `k`-series defining `E[V_D log V_D]` converges absolutely;
* `rs_integral_mulLog_betheE_nonneg`: `E[E_x log E_x] ≥ 0` (Jensen in the paper).

## Proof

Bounds: for `μ` in the simplex, `(M_x μ)_a` is a convex combination of the entries
`M_x(a,b) ∈ [x, 3/2]` (`rs_rsM_mem`), so it lies in `[x, 3/2]`; products and averages of these
coordinates give the bounds on `V_k` and `E_x`.  Means: linearity of the integral,
`∫ μ_a dν = 1/q`, the row sums `∑_b M_t(a,b) = q`, and `integral_fintype_prod_eq_pow`,
`integral_fintype_prod_eq_prod` for the product measures (`Fin.prod_univ_two` for `ν^{⊗2}`).
Integrability: the coordinates are bounded and measurable, hence integrable (no continuity is
used), and products of them are integrable by `Integrable.fintype_prod`.  Series:
`|v log v| ≤ 1 + v²` for `v ≥ 0`, so the `k`-th integral is at most `1 + (9/4)^k`
(`norm_integral_le_of_norm_le_const`, which needs no integrability), and
`∑_k Pois(r)(k) (1 + (9/4)^k) < ∞`.  Nonnegativity: if `E_x log E_x` is integrable, then
`v log v ≥ v - 1` and `E[E_x] = 1` give `E[E_x log E_x] ≥ 0`; otherwise its Bochner integral
is `0`.
-/

open Polynomial Filter Topology MeasureTheory

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-! ### Order properties of `d_cond` -/

theorem rs_dCond_nonneg (q : ℕ) (x : ℝ) : 0 ≤ dCond q x :=
  Real.sInf_nonneg fun _ hr => hr.1.le

theorem rs_dCond_le_of_pos {q : ℕ} {x r : ℝ} (hr : 0 < r) {ν : ProbabilityMeasure (rsSimplex q)}
    (hν : ν ∈ rsPu q) (h : 0 < bethePsi q r x ν) : dCond q x ≤ r :=
  csInf_le ⟨0, fun _ hr' => hr'.1.le⟩ ⟨hr, ν, hν, h⟩

/-- Below the condensation threshold the Bethe functional is nonpositive on `𝒫_u`. -/
theorem rs_bethePsi_nonpos_of_lt_dCond {q : ℕ} {x s : ℝ} (hs0 : 0 < s) (hs : s < dCond q x) :
    ∀ ν ∈ rsPu q, bethePsi q s x ν ≤ 0 := by
  intro ν hν
  by_contra h
  rw [not_le] at h
  exact absurd (rs_dCond_le_of_pos hs0 hν h) (not_le.2 hs)

/-! ### Bounds and means -/

/-- Each coordinate `(M_x μ)_a` of `M_x μ` lies in `[x, 3/2]` for `μ` in the simplex: it is a
convex combination of the entries `M_x(a,b) ∈ [x, 3/2]` (`rs_rsM_mem`). -/
private lemma rsBB_betheMvec_mem {q : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {μ : Fin q → ℝ} (hμ : μ ∈ stdSimplex ℝ (Fin q)) (a : Fin q) :
    x ≤ betheMvec q (tRe q x) μ a ∧ betheMvec q (tRe q x) μ a ≤ 3 / 2 := by
  have hM := fun b => rs_rsM_mem hq hx0 hx1 a b
  unfold betheMvec
  constructor
  · calc x = ∑ b, x * μ b := by rw [← Finset.mul_sum, hμ.2, mul_one]
      _ ≤ ∑ b, rsM q (tRe q x) a b * μ b :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hM b).1 (hμ.1 b)
  · calc ∑ b, rsM q (tRe q x) a b * μ b ≤ ∑ b, 3 / 2 * μ b :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hM b).2 (hμ.1 b)
      _ = 3 / 2 := by rw [← Finset.mul_sum, hμ.2, mul_one]

/-- `|v log v| ≤ 1 + v²` for `v ≥ 0` (from `v - 1 ≤ v log v ≤ v (v - 1)`). -/
private lemma rsBB_abs_mulLog_le {v : ℝ} (hv : 0 ≤ v) : |v * Real.log v| ≤ 1 + v ^ 2 := by
  rcases hv.eq_or_lt with rfl | hv'
  · simp
  · have h1 := Real.log_le_sub_one_of_pos hv'
    have h2 := Real.one_sub_inv_le_log_of_pos hv'
    have h3 : v * (1 - v⁻¹) ≤ v * Real.log v := mul_le_mul_of_nonneg_left h2 hv
    have h4 : v * Real.log v ≤ v * (v - 1) := mul_le_mul_of_nonneg_left h1 hv
    rw [mul_sub, mul_one, mul_inv_cancel₀ hv'.ne'] at h3
    rw [abs_le]
    constructor <;> nlinarith

/-- `v - 1 ≤ v log v` for `v ≥ 0` (tangent line of `v log v` at `v = 1`). -/
private lemma rsBB_sub_one_le_mulLog {v : ℝ} (hv : 0 ≤ v) : v - 1 ≤ v * Real.log v := by
  rcases hv.eq_or_lt with rfl | hv'
  · simp
  · have h2 := Real.one_sub_inv_le_log_of_pos hv'
    have h3 : v * (1 - v⁻¹) ≤ v * Real.log v := mul_le_mul_of_nonneg_left h2 hv
    rwa [mul_sub, mul_one, mul_inv_cancel₀ hv'.ne'] at h3

/-- The coordinate maps `μ ↦ μ_b` are integrable on the simplex (bounded by `1`, measurable). -/
private lemma rsBB_integrable_coord {q : ℕ} (ν : Measure (rsSimplex q)) [IsFiniteMeasure ν]
    (b : Fin q) : Integrable (fun μ : rsSimplex q => (μ : Fin q → ℝ) b) ν := by
  refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun μ => ?_)
  · exact ((measurable_pi_apply b).comp measurable_subtype_coe).aestronglyMeasurable
  · have h0 := stdSimplex.zero_le μ b
    have h1 := stdSimplex.le_one μ b
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith

/-- `μ ↦ (M_t μ)_a` is integrable on the simplex. -/
private lemma rsBB_integrable_betheMvec {q : ℕ} (t : ℝ) (ν : Measure (rsSimplex q))
    [IsFiniteMeasure ν] (a : Fin q) :
    Integrable (fun μ : rsSimplex q => betheMvec q t (μ : Fin q → ℝ) a) ν := by
  unfold betheMvec
  exact integrable_finsetSum _ fun b _ => (rsBB_integrable_coord ν b).const_mul _

/-- `E[(M_t μ)_a] = 1` for `ν ∈ 𝒫_u`: the mean of `μ` is `u` and the rows of `M_t` sum to `q`. -/
private lemma rsBB_integral_betheMvec {q : ℕ} (hq : 1 ≤ q) (t : ℝ)
    {ν : ProbabilityMeasure (rsSimplex q)} (hν : ν ∈ rsPu q) (a : Fin q) :
    ∫ μ : rsSimplex q, betheMvec q t (μ : Fin q → ℝ) a ∂(ν : Measure (rsSimplex q)) = 1 := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  unfold betheMvec
  rw [integral_finsetSum _ fun b _ => (rsBB_integrable_coord _ b).const_mul _]
  have h : ∀ b, ∫ μ : rsSimplex q, rsM q t a b * (μ : Fin q → ℝ) b ∂(ν : Measure (rsSimplex q))
      = rsM q t a b * (q : ℝ)⁻¹ := by
    intro b
    rw [integral_const_mul, hν b]
  rw [Finset.sum_congr rfl fun b _ => h b, ← Finset.sum_mul, rs_sum_rsM, mul_inv_cancel₀ hq0]

/-- The `a`-th summand `μ₁(a) (M_t μ₂)_a` of `E = μ₁ᵀ M_t μ₂` as a product of one-coordinate
functions on `(rsSimplex q)^2`. -/
private lemma rsBB_betheE_term_eq_prod {q : ℕ} (t : ℝ) (a : Fin q) (μ : Fin 2 → rsSimplex q) :
    (μ 0 : Fin q → ℝ) a * betheMvec q t (μ 1 : Fin q → ℝ) a =
      ∏ i, (![fun ρ : rsSimplex q => (ρ : Fin q → ℝ) a,
        fun ρ : rsSimplex q => betheMvec q t (ρ : Fin q → ℝ) a] i) (μ i) := by
  simp [Fin.prod_univ_two]

/-- Each summand `μ₁(a) (M_t μ₂)_a` of `E` is integrable against `ν^{⊗2}`. -/
private lemma rsBB_integrable_betheE_term {q : ℕ} (t : ℝ) (ν : Measure (rsSimplex q))
    [IsFiniteMeasure ν] (a : Fin q) :
    Integrable (fun μ : Fin 2 → rsSimplex q =>
      (μ 0 : Fin q → ℝ) a * betheMvec q t (μ 1 : Fin q → ℝ) a) (Measure.pi fun _ => ν) := by
  simp_rw [rsBB_betheE_term_eq_prod t a]
  refine Integrable.fintype_prod fun i => ?_
  fin_cases i
  · exact rsBB_integrable_coord ν a
  · exact rsBB_integrable_betheMvec t ν a

/-- `E = μ₁ᵀ M_t μ₂` is integrable against `ν^{⊗2}`. -/
private lemma rsBB_integrable_betheE {q : ℕ} (t : ℝ) (ν : Measure (rsSimplex q))
    [IsFiniteMeasure ν] :
    Integrable (fun μ : Fin 2 → rsSimplex q => betheE q t (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ))
      (Measure.pi fun _ => ν) := by
  unfold betheE
  exact integrable_finsetSum _ fun a _ => rsBB_integrable_betheE_term t ν a

/-- `0 ≤ V_k ≤ (3/2)^k` at a real `x ∈ [0,1]` (`q ≥ 3`), for `μ_i` in the simplex. -/
theorem rs_betheV_bounds {q : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {k : ℕ}
    {μ : Fin k → Fin q → ℝ} (hμ : ∀ i, μ i ∈ stdSimplex ℝ (Fin q)) :
    0 ≤ betheV q (tRe q x) μ ∧ betheV q (tRe q x) μ ≤ (3 / 2) ^ k := by
  have hM := fun i a => rsBB_betheMvec_mem hq hx0 hx1 (hμ i) a
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hprod : ∀ a, 0 ≤ ∏ i, betheMvec q (tRe q x) (μ i) a ∧
      ∏ i, betheMvec q (tRe q x) (μ i) a ≤ (3 / 2) ^ k := by
    intro a
    refine ⟨Finset.prod_nonneg fun i _ => hx0.trans (hM i a).1, ?_⟩
    calc ∏ i, betheMvec q (tRe q x) (μ i) a ≤ ∏ _i : Fin k, (3 / 2 : ℝ) :=
          Finset.prod_le_prod (fun i _ => hx0.trans (hM i a).1) (fun i _ => (hM i a).2)
      _ = (3 / 2) ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold betheV
  constructor
  · exact mul_nonneg (inv_nonneg.2 hq0.le) (Finset.sum_nonneg fun a _ => (hprod a).1)
  · rw [inv_mul_le_iff₀ hq0]
    calc ∑ a, ∏ i, betheMvec q (tRe q x) (μ i) a ≤ ∑ _a : Fin q, (3 / 2 : ℝ) ^ k :=
          Finset.sum_le_sum fun a _ => (hprod a).2
      _ = q * (3 / 2) ^ k := by simp

/-- `0 ≤ E_x ≤ 3/2` at a real `x ∈ [0,1]` (`q ≥ 3`), for `μ₁, μ₂` in the simplex. -/
theorem rs_betheE_bounds {q : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {μ₁ μ₂ : Fin q → ℝ} (h₁ : μ₁ ∈ stdSimplex ℝ (Fin q)) (h₂ : μ₂ ∈ stdSimplex ℝ (Fin q)) :
    0 ≤ betheE q (tRe q x) μ₁ μ₂ ∧ betheE q (tRe q x) μ₁ μ₂ ≤ 3 / 2 := by
  have hM := fun a => rsBB_betheMvec_mem hq hx0 hx1 h₂ a
  unfold betheE
  constructor
  · exact Finset.sum_nonneg fun a _ => mul_nonneg (h₁.1 a) (hx0.trans (hM a).1)
  · calc ∑ a, μ₁ a * betheMvec q (tRe q x) μ₂ a ≤ ∑ a, μ₁ a * (3 / 2) :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hM a).2 (h₁.1 a)
      _ = 3 / 2 := by rw [← Finset.sum_mul, h₁.2, one_mul]

/-- `E[V_k] = 1` for `ν ∈ 𝒫_u` (any `t`, any `k`). -/
theorem rs_integral_betheV {q : ℕ} (hq : 1 ≤ q) (t : ℝ) {ν : ProbabilityMeasure (rsSimplex q)}
    (hν : ν ∈ rsPu q) (k : ℕ) :
    ∫ μ : Fin k → rsSimplex q, betheV q t (fun i => (μ i : Fin q → ℝ))
      ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q))) = 1 := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have key : ∀ a : Fin q, ∫ μ : Fin k → rsSimplex q, ∏ i, betheMvec q t (μ i : Fin q → ℝ) a
      ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q))) = 1 := by
    intro a
    rw [integral_fintype_prod_eq_pow (fun μ : rsSimplex q => betheMvec q t (μ : Fin q → ℝ) a),
      rsBB_integral_betheMvec hq t hν a, one_pow]
  simp only [betheV]
  rw [integral_const_mul, integral_finsetSum _ fun a _ => Integrable.fintype_prod
    (f := fun _ (μ : rsSimplex q) => betheMvec q t (μ : Fin q → ℝ) a)
    fun _ => rsBB_integrable_betheMvec t _ a]
  rw [Finset.sum_congr rfl fun a _ => key a]
  simp [hq0]

/-- `E[E] = E[μ₁ᵀ M_t μ₂] = 1` for `ν ∈ 𝒫_u` (any `t`). -/
theorem rs_integral_betheE {q : ℕ} (hq : 1 ≤ q) (t : ℝ) {ν : ProbabilityMeasure (rsSimplex q)}
    (hν : ν ∈ rsPu q) :
    ∫ μ : Fin 2 → rsSimplex q, betheE q t (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ)
      ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q))) = 1 := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have key : ∀ a : Fin q, ∫ μ : Fin 2 → rsSimplex q,
      (μ 0 : Fin q → ℝ) a * betheMvec q t (μ 1 : Fin q → ℝ) a
      ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q))) = (q : ℝ)⁻¹ := by
    intro a
    simp_rw [rsBB_betheE_term_eq_prod t a]
    rw [integral_fintype_prod_eq_prod]
    simp [Fin.prod_univ_two, hν a, rsBB_integral_betheMvec hq t hν a]
  unfold betheE
  rw [integral_finsetSum _ fun a _ => rsBB_integrable_betheE_term t _ a,
    Finset.sum_congr rfl fun a _ => key a]
  simp [hq0]

/-- The series `∑_k Pois(r)(k) E[V_k log V_k]` defining `E[V_D log V_D]` converges (absolutely),
for every probability measure `ν` on the simplex, `r ≥ 0` and real `x ∈ [0,1]`. -/
theorem rs_summable_bethe_series {q : ℕ} (hq : 3 ≤ q) {r x : ℝ} (hr : 0 ≤ r) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) (ν : ProbabilityMeasure (rsSimplex q)) :
    Summable (fun k : ℕ => poisPMF r k *
      ∫ μ : Fin k → rsSimplex q,
        betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)) *
          Real.log (betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)))
        ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q)))) := by
  have hI : ∀ k : ℕ, |∫ μ : Fin k → rsSimplex q,
      betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)) *
        Real.log (betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)))
      ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q)))| ≤ 1 + (9 / 4) ^ k := by
    intro k
    have h := norm_integral_le_of_norm_le_const
      (μ := Measure.pi fun _ : Fin k => (ν : Measure (rsSimplex q))) (C := 1 + (9 / 4) ^ k)
      (f := fun μ : Fin k → rsSimplex q => betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)) *
        Real.log (betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ))))
      (Filter.Eventually.of_forall fun μ => ?_)
    · simpa using h
    · have hV := rs_betheV_bounds hq hx0 hx1 (μ := fun i => (μ i : Fin q → ℝ)) fun i => (μ i).2
      have h1 := rsBB_abs_mulLog_le hV.1
      have h2 : betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)) ^ 2 ≤ ((3 / 2 : ℝ) ^ k) ^ 2 :=
        pow_le_pow_left₀ hV.1 hV.2 2
      have h3 : ((3 / 2 : ℝ) ^ k) ^ 2 = (9 / 4) ^ k := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      rw [Real.norm_eq_abs]
      linarith
  have hpois : ∀ k, 0 ≤ poisPMF r k := fun k => by unfold poisPMF; positivity
  have hg : Summable fun k : ℕ => poisPMF r k * (1 + (9 / 4) ^ k) := by
    have h := ((RSPoisPiAux.hasSum_poisPMF_mul_pow (lam := r) 1).summable).add
      (RSPoisPiAux.hasSum_poisPMF_mul_pow (lam := r) (9 / 4)).summable
    refine h.congr fun k => ?_
    simp only [one_pow]
    ring
  refine Summable.of_norm_bounded hg fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpois k)]
  exact mul_le_mul_of_nonneg_left (hI k) (hpois k)

/-- `E[E_x log E_x] ≥ 0` for `ν ∈ 𝒫_u` (real `x ∈ [0,1]`). -/
theorem rs_integral_mulLog_betheE_nonneg {q : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) {ν : ProbabilityMeasure (rsSimplex q)} (hν : ν ∈ rsPu q) :
    0 ≤ ∫ μ : Fin 2 → rsSimplex q,
        betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ) *
          Real.log (betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ))
        ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q))) := by
  set m := Measure.pi fun _ : Fin 2 => (ν : Measure (rsSimplex q)) with hm
  set E : (Fin 2 → rsSimplex q) → ℝ :=
    fun μ => betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ) with hE
  have hE0 : ∀ μ, 0 ≤ E μ := fun μ => (rs_betheE_bounds hq hx0 hx1 (μ 0).2 (μ 1).2).1
  have hEint : Integrable E m := rsBB_integrable_betheE _ _
  have hEmean : ∫ μ, E μ ∂m = 1 := rs_integral_betheE (by omega) _ hν
  by_cases hint : Integrable (fun μ => E μ * Real.log (E μ)) m
  · calc (0 : ℝ) = ∫ μ, (E μ - 1) ∂m := by
          rw [integral_sub hEint (integrable_const 1), hEmean]
          simp
      _ ≤ ∫ μ, E μ * Real.log (E μ) ∂m :=
          integral_mono (hEint.sub (integrable_const 1)) hint
            fun μ => rsBB_sub_one_le_mulLog (hE0 μ)
  · exact (integral_undef hint).ge

end

end ERZeroFreeness
