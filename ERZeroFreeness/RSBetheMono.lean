/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSBetheKS

/-!
# Appendix C: monotonicity of `x ↦ d_cond(q,x)` (Lemma C.3, first assertion)

* `rs_bethePsi_shrink`: for `0 ≤ y ≤ x < 1`, `r ≥ 0` and `ν ∈ 𝒫_u`, the law `ν'` of
  `u + α₀(μ - u)` (`μ ∼ ν`, `α₀ = t(x)/t(y) ∈ (0,1]`) lies in `𝒫_u` and `Ψ_{r,y}(ν') ≥ Ψ_{r,x}(ν)`
  (the argument of [CWZ, proof of Lemma 4.1, eq. (19)]);
* `rs_dCond_mono`: `d_cond(q,y) ≤ d_cond(q,x)` for `0 ≤ y ≤ x < 1`, from `rs_bethePsi_shrink` and
  `rs_ks_certificate`.

## Proof

`shrink α : simplex → simplex`, `μ ↦ ((1-α)/q + α μ_b)_b`, is measurable (coordinatewise; no
continuity is used), and `ν' = ν.map (shrink α₀)` is a probability measure with mean `u`
(`ProbabilityMeasure.map`, `integral_map`).  By `eq:rs-Mmu`, `M_{t(y)}(shrink μ) = M_{t(x)} μ`
(since `t(y) α₀ = t(x)`), so the `V_k` integrands agree term by term (`Measure.pi_map_pi`,
`integral_map`), while `E' = 1 + α₀ (E_x - 1)`.  Convexity of `Λ(v) = v log v`
(`Real.convexOn_mul_log`) at the points `1` and `E_x ≥ 0` gives `Λ(E') ≤ α₀ Λ(E_x)`, and
`E[Λ(E_x)] ≥ 0` (`rs_integral_mulLog_betheE_nonneg`) gives `E[Λ(E')] ≤ E[Λ(E_x)]`; multiply by
`-r/2 ≤ 0`.  For the infimum: the defining set at `x` is contained in the one at `y`, it is
nonempty (`rs_ks_certificate`) and both are bounded below by `0` (`csInf_le_csInf`).
-/

open Polynomial Filter Topology MeasureTheory

namespace ERZeroFreeness

open scoped Classical

noncomputable section

namespace RSBetheMonoAux

/-! ### The shrinking map `μ ↦ u + α(μ - u)` -/

/-- The vector `u + α(μ - u) = ((1-α)/q + α μ_b)_b`. -/
def shrinkVec (q : ℕ) (α : ℝ) (μ : Fin q → ℝ) : Fin q → ℝ := fun b => (1 - α) / q + α * μ b

/-- `u + α(μ - u)` lies in the simplex for `μ` in the simplex and `α ∈ [0,1]`. -/
theorem shrinkVec_mem {q : ℕ} {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) {μ : Fin q → ℝ}
    (hμ : μ ∈ stdSimplex ℝ (Fin q)) : shrinkVec q α μ ∈ stdSimplex ℝ (Fin q) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exfalso
    have := hμ.2
    simp at this
  have hq' : (q : ℝ) ≠ 0 := by positivity
  refine ⟨fun b => ?_, ?_⟩
  · unfold shrinkVec
    have := hμ.1 b
    have : 0 ≤ 1 - α := by linarith
    positivity
  · unfold shrinkVec
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Finset.mul_sum, hμ.2, nsmul_eq_mul]
    field_simp
    ring

/-- The shrinking map `shrink α` of the simplex towards `u`. -/
def shrinkPt (q : ℕ) {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (μ : rsSimplex q) : rsSimplex q :=
  ⟨shrinkVec q α μ, shrinkVec_mem h0 h1 μ.2⟩

theorem shrinkPt_coe (q : ℕ) {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (μ : rsSimplex q) :
    ((shrinkPt q h0 h1 μ : rsSimplex q) : Fin q → ℝ) = shrinkVec q α μ := rfl

/-! ### Measurability -/

/-- The coordinate map `μ ↦ μ_b` of the simplex is measurable. -/
theorem bm_measurable_coord (q : ℕ) (b : Fin q) :
    Measurable (fun μ : rsSimplex q => (μ : Fin q → ℝ) b) :=
  (measurable_pi_apply b).comp measurable_subtype_coe

theorem measurable_shrinkPt (q : ℕ) {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    Measurable (shrinkPt q h0 h1) := by
  refine Measurable.subtype_mk (measurable_pi_lambda _ fun b => ?_)
  exact ((bm_measurable_coord q b).const_mul α).const_add _

theorem bm_measurable_betheV (q : ℕ) (t : ℝ) (k : ℕ) :
    Measurable (fun μ : Fin k → rsSimplex q => betheV q t (fun i => (μ i : Fin q → ℝ))) := by
  unfold betheV betheMvec
  refine Measurable.const_mul (Finset.measurable_sum _ fun a _ => Finset.measurable_prod _
    fun i _ => Finset.measurable_sum _ fun b _ => ?_) _
  exact ((bm_measurable_coord q b).comp (measurable_pi_apply i)).const_mul _

theorem bm_measurable_betheE (q : ℕ) (t : ℝ) :
    Measurable (fun μ : Fin 2 → rsSimplex q =>
      betheE q t (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ)) := by
  unfold betheE betheMvec
  refine Finset.measurable_sum _ fun a _ => Measurable.mul ?_
    (Finset.measurable_sum _ fun b _ => ?_)
  · exact (bm_measurable_coord q a).comp (measurable_pi_apply 0)
  · exact ((bm_measurable_coord q b).comp (measurable_pi_apply 1)).const_mul _

/-! ### `eq:rs-Mmu`: the effect of shrinking on `M_t μ`, `V_k` and `E` -/

/-- `(M_t (u + α(μ - u)))_a = (M_{tα} μ)_a` for `∑_b μ_b = 1`. -/
theorem betheMvec_shrink {q : ℕ} (t α : ℝ) {μ : Fin q → ℝ} (hμ : ∑ b, μ b = 1) (a : Fin q) :
    betheMvec q t (shrinkVec q α μ) a = betheMvec q (t * α) μ a := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp at hμ
  have hq' : (q : ℝ) ≠ 0 := by positivity
  unfold betheMvec shrinkVec rsM
  have e : ∀ b, (1 + t * ((rsA q a b : ℤ) : ℝ)) * ((1 - α) / q + α * μ b) =
      (1 - α) / q + t * ((1 - α) / q) * ((rsA q a b : ℤ) : ℝ) + α * μ b +
        t * α * (((rsA q a b : ℤ) : ℝ) * μ b) := by
    intro b; ring
  have e2 : ∀ b, (1 + t * α * ((rsA q a b : ℤ) : ℝ)) * μ b =
      μ b + t * α * (((rsA q a b : ℤ) : ℝ) * μ b) := by
    intro b; ring
  simp only [e, e2, Finset.sum_add_distrib, ← Finset.mul_sum, rs_sum_rsA, hμ, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The columns of `A` sum to zero (`A` is symmetric). -/
theorem bm_sum_rsA_col (q : ℕ) (b : Fin q) : ∑ a, ((rsA q a b : ℤ) : ℝ) = 0 := by
  have h : ∀ a, rsA q a b = rsA q b a := by
    intro a; unfold rsA; simp only [eq_comm]
  simp only [h]
  exact rs_sum_rsA q b

/-- The columns of `M_t` sum to `q`, so `∑_a (M_t μ)_a = q` for `∑_b μ_b = 1`. -/
theorem bm_sum_betheMvec {q : ℕ} (t : ℝ) {μ : Fin q → ℝ} (hμ : ∑ b, μ b = 1) :
    ∑ a, betheMvec q t μ a = q := by
  have hcol : ∀ b, ∑ a, rsM q t a b = q := by
    intro b
    unfold rsM
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, bm_sum_rsA_col]
    simp
  unfold betheMvec
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, hcol, ← Finset.mul_sum, hμ, mul_one]

/-- `E_t(u + α(μ₁ - u), u + α(μ₂ - u)) = 1 + α (E_{tα}(μ₁, μ₂) - 1)`. -/
theorem betheE_shrink {q : ℕ} (t α : ℝ) {μ₁ μ₂ : Fin q → ℝ} (h₁ : ∑ b, μ₁ b = 1)
    (h₂ : ∑ b, μ₂ b = 1) :
    betheE q t (shrinkVec q α μ₁) (shrinkVec q α μ₂) = 1 + α * (betheE q (t * α) μ₁ μ₂ - 1) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp at h₁
  have hq' : (q : ℝ) ≠ 0 := by positivity
  unfold betheE
  simp only [betheMvec_shrink t α h₂]
  unfold shrinkVec
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc,
    bm_sum_betheMvec (t * α) h₂]
  field_simp
  ring

/-- `V_k` at `t` of the shrunk points is `V_k` at `tα` of the original ones. -/
theorem betheV_shrink {q : ℕ} (t α : ℝ) {k : ℕ} {μ : Fin k → Fin q → ℝ}
    (hμ : ∀ i, ∑ b, μ i b = 1) :
    betheV q t (fun i => shrinkVec q α (μ i)) = betheV q (t * α) μ := by
  unfold betheV
  simp only [betheMvec_shrink t α (hμ _)]

/-! ### `v log v`: integrability and convexity -/

/-- `|v log v| ≤ 1 + v²` for `v ≥ 0`. -/
theorem bm_abs_mulLog_le {v : ℝ} (hv : 0 ≤ v) : |v * Real.log v| ≤ 1 + v ^ 2 := by
  rcases hv.eq_or_lt with rfl | hv'
  · simp
  · have h1 := Real.log_le_sub_one_of_pos hv'
    have h2 := Real.one_sub_inv_le_log_of_pos hv'
    have h3 : v * (1 - v⁻¹) ≤ v * Real.log v := mul_le_mul_of_nonneg_left h2 hv
    have h4 : v * Real.log v ≤ v * (v - 1) := mul_le_mul_of_nonneg_left h1 hv
    rw [mul_sub, mul_one, mul_inv_cancel₀ hv'.ne'] at h3
    rw [abs_le]
    constructor <;> nlinarith

/-- `v log v` of a bounded nonnegative measurable function is integrable (finite measure). -/
theorem bm_integrable_mulLog {X : Type*} [MeasurableSpace X] {m : Measure X} [IsFiniteMeasure m]
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (h0 : ∀ x, 0 ≤ f x) (hB : ∀ x, f x ≤ B) :
    Integrable (fun x => f x * Real.log (f x)) m := by
  refine Integrable.of_bound (hf.mul (Real.measurable_log.comp hf)).aestronglyMeasurable
    (1 + B ^ 2) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  calc |f x * Real.log (f x)| ≤ 1 + f x ^ 2 := bm_abs_mulLog_le (h0 x)
    _ ≤ 1 + B ^ 2 := by
      have := pow_le_pow_left₀ (h0 x) (hB x) 2
      linarith

/-- Convexity of `Λ(v) = v log v` between `1` and `E ≥ 0`: `Λ(1 + α(E-1)) ≤ α Λ(E)`
(`Λ(1) = 0`). -/
theorem bm_mulLog_affine_le {E α : ℝ} (hE : 0 ≤ E) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    (1 + α * (E - 1)) * Real.log (1 + α * (E - 1)) ≤ α * (E * Real.log E) := by
  have h := Real.convexOn_mul_log.2 (Set.mem_Ici.2 zero_le_one) (Set.mem_Ici.2 hE)
    (by linarith : (0 : ℝ) ≤ 1 - α) h0 (by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, mul_one, zero_add] at h
  have e : 1 + α * (E - 1) = 1 - α + α * E := by ring
  rw [e]
  exact h

/-! ### The two terms of `Ψ` under the shrinking map -/

/-- The `V_k`-integrals of `Ψ` are transported exactly: `E_{ν'}[Λ(V_k^{t})] = E_ν[Λ(V_k^{tα})]`
(`Measure.pi_map_pi`, `integral_map`). -/
theorem integral_mulLog_betheV_shrink {q : ℕ} {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (t : ℝ)
    (ν : Measure (rsSimplex q)) [IsProbabilityMeasure ν] (k : ℕ) :
    ∫ μ : Fin k → rsSimplex q, betheV q t (fun i => (μ i : Fin q → ℝ)) *
        Real.log (betheV q t (fun i => (μ i : Fin q → ℝ)))
      ∂(Measure.pi fun _ => ν.map (shrinkPt q h0 h1)) =
    ∫ μ : Fin k → rsSimplex q, betheV q (t * α) (fun i => (μ i : Fin q → ℝ)) *
        Real.log (betheV q (t * α) (fun i => (μ i : Fin q → ℝ)))
      ∂(Measure.pi fun _ => ν) := by
  have hm := measurable_shrinkPt q h0 h1
  rw [← Measure.pi_map_pi (fun _ => hm.aemeasurable)]
  rw [integral_map]
  · congr 1
    funext μ
    simp only [shrinkPt_coe]
    rw [betheV_shrink t α (fun i => stdSimplex.sum_eq_one (μ i))]
  · exact (measurable_pi_lambda _ fun i => hm.comp (measurable_pi_apply i)).aemeasurable
  · exact ((bm_measurable_betheV q t k).mul
      (Real.measurable_log.comp (bm_measurable_betheV q t k))).aestronglyMeasurable

/-- The `E`-integral of `Ψ` does not increase under the shrinking map when `tα = t(x)`:
`E_{ν'}[Λ(E_t)] = E_ν[Λ(1 + α(E_x - 1))] ≤ α E_ν[Λ(E_x)] ≤ E_ν[Λ(E_x)]`. -/
theorem integral_mulLog_betheE_shrink_le {q : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) {t : ℝ} (ht : t * α = tRe q x)
    {ν : ProbabilityMeasure (rsSimplex q)} (hν : ν ∈ rsPu q) :
    ∫ μ : Fin 2 → rsSimplex q, betheE q t (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ) *
        Real.log (betheE q t (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ))
      ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q)).map (shrinkPt q h0 h1)) ≤
    ∫ μ : Fin 2 → rsSimplex q, betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ) *
        Real.log (betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ))
      ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q))) := by
  have hm := measurable_shrinkPt q h0 h1
  set m := Measure.pi fun _ : Fin 2 => (ν : Measure (rsSimplex q)) with hmdef
  set E : (Fin 2 → rsSimplex q) → ℝ :=
    fun μ => betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ) with hE
  have hEb : ∀ μ, 0 ≤ E μ ∧ E μ ≤ 3 / 2 := fun μ => rs_betheE_bounds hq hx0 hx1 (μ 0).2 (μ 1).2
  have hEm : Measurable E := bm_measurable_betheE q (tRe q x)
  rw [← Measure.pi_map_pi (fun _ => hm.aemeasurable)]
  rw [integral_map]
  rotate_left
  · exact (measurable_pi_lambda _ fun i => hm.comp (measurable_pi_apply i)).aemeasurable
  · exact ((bm_measurable_betheE q t).mul
      (Real.measurable_log.comp (bm_measurable_betheE q t))).aestronglyMeasurable
  have hpt : ∀ μ : Fin 2 → rsSimplex q,
      betheE q t ((shrinkPt q h0 h1 (μ 0) : rsSimplex q) : Fin q → ℝ)
        ((shrinkPt q h0 h1 (μ 1) : rsSimplex q) : Fin q → ℝ) = 1 + α * (E μ - 1) := by
    intro μ
    simp only [shrinkPt_coe]
    rw [betheE_shrink t α (stdSimplex.sum_eq_one (μ 0)) (stdSimplex.sum_eq_one (μ 1)), ht]
  simp only [hpt]
  have hI0 : 0 ≤ ∫ μ, E μ * Real.log (E μ) ∂m := rs_integral_mulLog_betheE_nonneg hq hx0 hx1 hν
  have hG : Measurable fun μ => 1 + α * (E μ - 1) :=
    ((hEm.sub_const 1).const_mul α).const_add 1
  calc ∫ μ, (1 + α * (E μ - 1)) * Real.log (1 + α * (E μ - 1)) ∂m
      ≤ ∫ μ, α * (E μ * Real.log (E μ)) ∂m := by
        refine integral_mono (bm_integrable_mulLog hG (B := 3 / 2) (fun μ => ?_) (fun μ => ?_))
          ((bm_integrable_mulLog hEm (B := 3 / 2) (fun μ => (hEb μ).1)
            (fun μ => (hEb μ).2)).const_mul α) (fun μ => ?_)
        · nlinarith [hEb μ]
        · nlinarith [hEb μ]
        · exact bm_mulLog_affine_le (hEb μ).1 h0 h1
    _ = α * ∫ μ, E μ * Real.log (E μ) ∂m := integral_const_mul _ _
    _ ≤ ∫ μ, E μ * Real.log (E μ) ∂m := by nlinarith

/-! ### The shrunk law stays in `𝒫_u` -/

/-- The coordinates are integrable on the simplex (bounded by `1`, measurable). -/
theorem bm_integrable_coord {q : ℕ} (ν : Measure (rsSimplex q)) [IsFiniteMeasure ν]
    (b : Fin q) : Integrable (fun μ : rsSimplex q => (μ : Fin q → ℝ) b) ν := by
  refine Integrable.of_bound (bm_measurable_coord q b).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun μ => ?_)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [stdSimplex.zero_le μ b, stdSimplex.le_one μ b]

/-- `ν' = ν.map (shrink α)` has mean `(1-α)u + αu = u`. -/
theorem map_shrink_mem {q : ℕ} {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1)
    {ν : ProbabilityMeasure (rsSimplex q)} (hν : ν ∈ rsPu q) :
    ν.map (measurable_shrinkPt q h0 h1).aemeasurable ∈ rsPu q := by
  intro a
  rw [ProbabilityMeasure.toMeasure_map, integral_map (measurable_shrinkPt q h0 h1).aemeasurable
    (bm_measurable_coord q a).aestronglyMeasurable]
  simp only [shrinkPt_coe, shrinkVec]
  rw [integral_add (integrable_const _) ((bm_integrable_coord _ a).const_mul α), integral_const,
    integral_const_mul, hν a]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

end RSBetheMonoAux

open RSBetheMonoAux

/-- Shrinking towards `u` transports `Ψ_{r,x}` to `Ψ_{r,y}` without decreasing it (`y ≤ x`). -/
theorem rs_bethePsi_shrink {q : ℕ} (hq : 3 ≤ q) {x y r : ℝ} (hy0 : 0 ≤ y) (hyx : y ≤ x)
    (hx1 : x < 1) (hr : 0 ≤ r) {ν : ProbabilityMeasure (rsSimplex q)} (hν : ν ∈ rsPu q) :
    ∃ ν' ∈ rsPu q, bethePsi q r x ν ≤ bethePsi q r y ν' := by
  have hq2 : 2 ≤ q := by omega
  have hx0 : 0 ≤ x := hy0.trans hyx
  have hty : tRe q y < 0 := rs_tRe_neg hq2 hy0 (hyx.trans_lt hx1)
  have htx : tRe q x < 0 := rs_tRe_neg hq2 hx0 hx1
  have htyx : tRe q y ≤ tRe q x := rs_tRe_mono hq2 hy0 hyx
  -- `α₀ = t(x)/t(y) ∈ [0,1]` and `t(y) α₀ = t(x)`
  set α := tRe q x / tRe q y with hαdef
  have h0 : 0 ≤ α := div_nonneg_of_nonpos htx.le hty.le
  have h1 : α ≤ 1 := (div_le_one_of_neg hty).2 htyx
  have ht : tRe q y * α = tRe q x := mul_div_cancel₀ _ hty.ne
  refine ⟨ν.map (measurable_shrinkPt q h0 h1).aemeasurable, map_shrink_mem h0 h1 hν, ?_⟩
  -- the `V`-series agree term by term
  have hV : ∀ k : ℕ,
      poisPMF r k * ∫ μ : Fin k → rsSimplex q, betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)) *
          Real.log (betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)))
        ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q))) =
      poisPMF r k * ∫ μ : Fin k → rsSimplex q, betheV q (tRe q y) (fun i => (μ i : Fin q → ℝ)) *
          Real.log (betheV q (tRe q y) (fun i => (μ i : Fin q → ℝ)))
        ∂(Measure.pi fun _ => ((ν.map (measurable_shrinkPt q h0 h1).aemeasurable :
          ProbabilityMeasure (rsSimplex q)) : Measure (rsSimplex q))) := by
    intro k
    rw [ProbabilityMeasure.toMeasure_map, integral_mulLog_betheV_shrink h0 h1, ht]
  -- the `E`-term does not increase
  have hE := integral_mulLog_betheE_shrink_le hq hx0 hx1.le h0 h1 ht hν
  rw [← ProbabilityMeasure.toMeasure_map ν (measurable_shrinkPt q h0 h1).aemeasurable] at hE
  unfold bethePsi
  rw [tsum_congr hV]
  have := mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ r / 2)
  linarith

/-- **Lemma C.3, monotonicity.** `x ↦ d_cond(q,x)` is nondecreasing on `[0,1)`. -/
theorem rs_dCond_mono {q : ℕ} (hq : 3 ≤ q) {x y : ℝ} (hy0 : 0 ≤ y) (hyx : y ≤ x) (hx1 : x < 1) :
    dCond q y ≤ dCond q x := by
  refine csInf_le_csInf ⟨0, fun _ hr => hr.1.le⟩ ?_ ?_
  · obtain ⟨ν, hν, hpos⟩ := rs_ks_certificate hq (hy0.trans hyx) hx1 (lt_add_one _)
    exact ⟨_, lt_of_le_of_lt (inv_nonneg.2 (sq_nonneg _)) (lt_add_one _), ν, hν, hpos⟩
  · rintro r ⟨hr, ν, hν, hpos⟩
    obtain ⟨ν', hν', hle⟩ := rs_bethePsi_shrink hq hy0 hyx hx1 hr.le hν
    exact ⟨hr, ν', hν', hpos.trans_le hle⟩

end

end ERZeroFreeness
