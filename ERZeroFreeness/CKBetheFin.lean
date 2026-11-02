/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.CKDefs
import ERZeroFreeness.RSPoisPi
import ERZeroFreeness.RSModel
import ERZeroFreeness.RSBetheBasic
import ERZeroFreeness.RSPoisSplit
import ERZeroFreeness.Poisson

/-!
# Proof of [CKPZ, Prop. 3.6]: Fact 0.2 (`Ψ` at finitely supported laws)

Part of the self-contained proof of `CKPZProp36 q`, the Potts case of the planted free-energy
bound of Coja-Oghlan, Krzakala, Perkins and Zdeborová [CKPZ, Prop. 3.6], which Lemma C.3
(`lem:rs-ckpz`) cites.  Appendix C is formalized in two layers: the `RS*` modules prove
Theorem C.1 from `CKPZProp36 q` as an explicit hypothesis, and the `CK*` modules prove
`CKPZProp36 q`.  Numbering refers to `docs/ckpz-proof.md`.

`ck_bethePsi_fin` (Fact 0.2): for weights `w` and atoms `μ_j` with mean `u` (`ckFinPu`), some
`ν ∈ 𝒫_u` (`rsPu`), namely the law `∑_j w_j δ_{μ_j}` on the simplex, has Bethe functional
`Ψ_{r,x}(ν)` (`bethePsi`, defined by integrals against `ν^{⊗d}`) equal to the finite sum
`ckPsi q (tRe q x) r w μ`.

## Proof

Take `ν = ∑_j ofReal(w_j) • δ_{μ_j}`.  On any space with measurable singletons, `ckBF_pi_eq`
identifies the `d`-fold product of `∑_j c_j δ_{x_j}` with `∑_y (∏_i c_{y_i}) • δ_{(x_{y_i})_i}`
via `Measure.pi_eq` on boxes and `Fintype.prod_sum`, and `ckBF_integral_sum_dirac` evaluates
integrals against such sums (every function is integrable against a finite sum of finite point
masses).  Thus each integral in `bethePsi` is the corresponding finite sum in `ckPsi`, the two
`tsum`s agree termwise (no summability is needed), and the `E`-term is reindexed by
`finTwoArrowEquiv`.  The hypothesis `1 ≤ q` is not used.
-/

open Filter Topology MeasureTheory

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-! ### Finite sums of point masses -/

/-- Every function is integrable against a finite sum of finite multiples of point masses, and
the integral is the weighted sum of its values at the atoms. -/
private lemma ckBF_integral_sum_dirac {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {ι : Type*} [Fintype ι] (c : ι → ENNReal) (hc : ∀ j, c j ≠ ⊤)
    (pt : ι → α) (f : α → ℝ) :
    ∫ a, f a ∂(∑ j, c j • Measure.dirac (pt j)) = ∑ j, (c j).toReal * f (pt j) := by
  rw [integral_finsetSum_measure fun j _ =>
    (integrable_dirac (f := f) (a := pt j) enorm_lt_top).smul_measure (hc j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul]

/-- The point mass at a tuple, evaluated on a box, is the product of the coordinate point
masses evaluated on the sides. -/
private lemma ckBF_dirac_pi {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {d : ℕ} (z : Fin d → α) (s : Fin d → Set α) :
    Measure.dirac z (Set.pi Set.univ s) = ∏ i, Measure.dirac (z i) (s i) := by
  simp only [Measure.dirac_apply]
  by_cases hz : ∀ i, z i ∈ s i
  · have hmem : z ∈ Set.pi Set.univ s := fun i _ => hz i
    rw [Set.indicator_of_mem hmem]
    simp [Set.indicator_of_mem (hz _)]
  · push Not at hz
    obtain ⟨i, hi⟩ := hz
    have hmem : z ∉ Set.pi Set.univ s := fun h => hi (h i (Set.mem_univ i))
    rw [Set.indicator_of_notMem hmem]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Set.indicator_of_notMem hi])).symm

/-- The `d`-fold product of `∑_j c_j δ_{x_j}` is `∑_y (∏_i c_{y_i}) δ_{(x_{y_1}, …, x_{y_d})}`. -/
private lemma ckBF_pi_eq {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {K : ℕ} (c : Fin K → ENNReal) (pt : Fin K → α) (ν : Measure α) [SigmaFinite ν]
    (hν : ν = ∑ j, c j • Measure.dirac (pt j)) (d : ℕ) :
    Measure.pi (fun _ : Fin d => ν) =
      ∑ y : Fin d → Fin K, (∏ i, c (y i)) • Measure.dirac (fun i => pt (y i)) := by
  refine Measure.pi_eq fun s _ => ?_
  subst hν
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_mul_distrib, ckBF_dirac_pi]

/-- Integrals against `ν^{⊗d}` for `ν = ∑_j c_j δ_{x_j}` are finite sums over index tuples. -/
private lemma ckBF_integral_pi {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {K : ℕ} (c : Fin K → ENNReal) (hc : ∀ j, c j ≠ ⊤) (pt : Fin K → α) (ν : Measure α)
    [SigmaFinite ν] (hν : ν = ∑ j, c j • Measure.dirac (pt j)) (d : ℕ)
    (F : (Fin d → α) → ℝ) :
    ∫ z, F z ∂(Measure.pi fun _ : Fin d => ν) =
      ∑ y : Fin d → Fin K, (∏ i, (c (y i)).toReal) * F (fun i => pt (y i)) := by
  rw [ckBF_pi_eq c pt ν hν d,
    ckBF_integral_sum_dirac _ (fun y => ENNReal.prod_ne_top fun i _ => hc (y i)) _ F]
  simp only [ENNReal.toReal_prod]

/-- Fact 0.2: if `w`, `μ` describe a finitely supported law with mean `u` (`ckFinPu`), then some
`ν ∈ 𝒫_u`, namely `∑_j w_j δ_{μ_j}`, satisfies `Ψ_{r,x}(ν) = ckPsi q (tRe q x) r w μ`. -/
theorem ck_bethePsi_fin {q : ℕ} (hq : 1 ≤ q) {K : ℕ} {w : Fin K → ℝ} {μ : Fin K → Fin q → ℝ}
    (h : ckFinPu q w μ) (r x : ℝ) :
    ∃ ν ∈ rsPu q, bethePsi q r x ν = ckPsi q (tRe q x) r w μ := by
  obtain ⟨⟨hw0, hw1, hμ⟩, hmean⟩ := h
  -- the atoms `μ_j` as points of the simplex, and their weights
  let pt : Fin K → rsSimplex q := fun j => ⟨μ j, hμ j⟩
  let c : Fin K → ENNReal := fun j => ENNReal.ofReal (w j)
  have hc : ∀ j, c j ≠ ⊤ := fun j => ENNReal.ofReal_ne_top
  have hcR : ∀ j, (c j).toReal = w j := fun j => ENNReal.toReal_ofReal (hw0 j)
  -- `ν = ∑_j w_j δ_{μ_j}` is a probability measure
  let νm : Measure (rsSimplex q) := ∑ j, c j • Measure.dirac (pt j)
  have hprob : IsProbabilityMeasure νm := by
    constructor
    simp only [νm, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one, c]
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => hw0 j, hw1, ENNReal.ofReal_one]
  let ν : ProbabilityMeasure (rsSimplex q) := ⟨νm, hprob⟩
  have hν : (ν : Measure (rsSimplex q)) = ∑ j, c j • Measure.dirac (pt j) := rfl
  -- integrals against `ν^{⊗d}` are finite sums over index tuples
  have hint : ∀ (d : ℕ) (F : (Fin d → rsSimplex q) → ℝ),
      ∫ z, F z ∂(Measure.pi fun _ : Fin d => (ν : Measure (rsSimplex q))) =
        ∑ y : Fin d → Fin K, (∏ i, w (y i)) * F (fun i => pt (y i)) := by
    intro d F
    rw [ckBF_integral_pi c hc pt _ hν d F]
    simp only [hcR]
  refine ⟨ν, ?_, ?_⟩
  · -- the mean of `ν` is `u`
    intro a
    rw [hν, ckBF_integral_sum_dirac c hc pt]
    simp only [hcR]
    exact hmean a
  · unfold bethePsi ckPsi ckBV ckBE
    congr 1
    · refine tsum_congr fun d => ?_
      rw [hint d]
      rfl
    · congr 1
      rw [hint 2, ← Fintype.sum_prod_type']
      refine Fintype.sum_equiv (finTwoArrowEquiv (Fin K)) _ _ fun y => ?_
      rw [Fin.prod_univ_two]
      rfl

end

end ERZeroFreeness
