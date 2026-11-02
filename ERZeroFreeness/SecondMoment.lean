/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs
import ERZeroFreeness.ErdosRenyi
import ERZeroFreeness.Entropy
import ERZeroFreeness.Multinomial
import ERZeroFreeness.TwoReplica
import ERZeroFreeness.Overlap

/-!
# The uniform second moment (`lem:moment-bound`)

For `q ≥ 3` and `0 < d < d₂(q)` there are `δ > 0` and `ρ₀ > 0` such that, for every
`ρ ∈ (0, ρ₀]`, `E|Ẑ^B_{G_n}(t)|²` is bounded uniformly in `n ≥ d` and `t ∈ L_{4ρ}(I)`,
`I = [-1/(q-1), 0]` (`second_moment_bound`).  The paper's lemma also arranges
`cond:remainder`; here the bound holds for every small `ρ`, and `first_moment_bound` shrinks `ρ`
to meet the remainder condition.

Proof.  Choose `δ ∈ (0, 1/q)` with `d(1+qδ) < d₂(q)` (`cond:delta`), then `ρ₀ > 0` so that with
`T = 1/(q-1) + 4ρ₀`: `θ = d(1+qδ)T²/(2c_q) < 1` and `4ρ₀ ≤ 1/(q-1)² ≤ T²` (`cond:entropy`);
note `d₂(q) = 2(q-1)² c_q` (`d2_eq`).  For `ρ ≤ ρ₀` and `t ∈ L_{4ρ}(I)`: `‖t‖ ≤ T`,
`Re t ≤ T²`.  `two_replica_bound` with `B = 𝓑_n(δ)`, then `overlap_energy_le_empKL`
turns the exponent into `θ n D(R ‖ U)`; enlarge the sum to all pairs, identify
`(σ,τ) ↦ (v ↦ (σ v, τ v))` with functions `Fin n → Fin q × Fin q`, and apply
`exists_sum_exp_empKL_le` with `k = q²`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

namespace SecondMomentAux

/-- Choice of `δ` (`cond:delta`): `0 < δ < 1/q` and `d(1+qδ) < d₂(q)`. -/
theorem exists_delta {q : ℕ} (hq : 3 ≤ q) {d : ℝ} (hd : 0 < d) (hd2 : d < d2 q) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / (q : ℝ) ∧ d * (1 + q * δ) < d2 q := by
  have hq0 : (0 : ℝ) < q := by
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  set ε := d2 q - d with hε
  have hε0 : 0 < ε := by linarith
  refine ⟨min (1 / (2 * (q : ℝ))) (ε / (2 * d * q)), lt_min (by positivity) (by positivity), ?_, ?_⟩
  · calc min (1 / (2 * (q : ℝ))) (ε / (2 * d * q)) ≤ 1 / (2 * (q : ℝ)) := min_le_left _ _
      _ < 1 / q := one_div_lt_one_div_of_lt hq0 (by linarith)
  · have h1 : min (1 / (2 * (q : ℝ))) (ε / (2 * d * q)) ≤ ε / (2 * d * q) := min_le_right _ _
    have h2 : d * (1 + q * min (1 / (2 * (q : ℝ))) (ε / (2 * d * q))) ≤
        d * (1 + q * (ε / (2 * d * q))) := by gcongr
    have h3 : d * (1 + q * (ε / (2 * d * q))) = d + ε / 2 := by field_simp
    linarith

/-- Choice of `ρ₀` (`cond:entropy`): with `T = a + 4ρ₀`, `K T² < 1` and `4ρ₀ ≤ a²`. -/
theorem exists_rho {K a : ℝ} (hK : 0 < K) (ha : 0 < a) (hKa : K * a ^ 2 < 1) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ K * (a + 4 * ρ₀) ^ 2 < 1 ∧ 4 * ρ₀ ≤ a ^ 2 := by
  set ε := 1 - K * a ^ 2 with hε
  have hε0 : 0 < ε := by linarith
  set r := min (a ^ 2 / 4) (min a (ε / (48 * K * a))) with hr
  have hr0 : 0 < r := lt_min (by positivity) (lt_min ha (by positivity))
  have hr1 : r ≤ a ^ 2 / 4 := min_le_left _ _
  have hr2 : r ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hr3 : r ≤ ε / (48 * K * a) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r, hr0, ?_, by linarith⟩
  have hsq : (a + 4 * r) ^ 2 ≤ a ^ 2 + 24 * a * r := by nlinarith
  have hKar : 48 * K * a * r ≤ ε := by
    rw [le_div_iff₀ (by positivity)] at hr3
    linarith
  have : K * (a + 4 * r) ^ 2 ≤ K * (a ^ 2 + 24 * a * r) := mul_le_mul_of_nonneg_left hsq hK.le
  nlinarith

/-- On the tube `L_r(I_s)`: `‖t‖ ≤ s + r` and `Re t ≤ r`. -/
theorem tube_bounds {s r : ℝ} {t : ℂ} (ht : t ∈ tube s r) : ‖t‖ ≤ s + r ∧ t.re ≤ r := by
  obtain ⟨x, ⟨hx1, hx2⟩, hxt⟩ := ht
  constructor
  · calc ‖t‖ = ‖(t - x) + (x : ℂ)‖ := by ring_nf
      _ ≤ ‖t - x‖ + ‖(x : ℂ)‖ := norm_add_le _ _
      _ ≤ r + s := by
        gcongr
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hx2]
        linarith
      _ = s + r := by ring
  · have h1 : (t - x).re ≤ ‖t - x‖ := Complex.re_le_norm _
    have h2 : (t - x).re = t.re - x := by simp
    linarith

/-- Reindexing a double sum over pairs of colourings as a sum over `Fin n → Fin q × Fin q`. -/
theorem sum_sum_pair_eq {n q : ℕ} {M : Type*} [AddCommMonoid M] (F : (Fin n → Fin q × Fin q) → M) :
    ∑ σ : Fin n → Fin q, ∑ τ : Fin n → Fin q, F (fun v => (σ v, τ v)) =
      ∑ f : Fin n → Fin q × Fin q, F f := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow _ _ _).symm _ _ (fun p => rfl)

end SecondMomentAux

/-- **`lem:moment-bound`.** For `q ≥ 3` and `0 < d < d₂(q)` there are `δ, ρ₀ > 0` such that for
every `ρ ∈ (0, ρ₀]` the second moment `E|Ẑ^B_{G_n}(t)|²` is bounded uniformly in `n ≥ d` and
`t ∈ L_{4ρ}([-1/(q-1), 0])`. -/
theorem second_moment_bound {q : ℕ} (hq : 3 ≤ q) {d : ℝ} (hd : 0 < d) (hd2 : d < d2 q) :
    ∃ δ > 0, ∃ ρ₀ > 0, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ B : ℝ, ∀ n : ℕ, d ≤ n →
      ∀ t ∈ tube (1 / ((q : ℝ) - 1)) (4 * ρ),
        erExp n (d / n) (fun G => ‖zhatB G q δ t‖ ^ 2) ≤ B := by
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hq2 : 2 ≤ q := by omega
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hcq := cq_pos hq
  obtain ⟨δ, hδ0, hδq, hδd⟩ := SecondMomentAux.exists_delta hq hd hd2
  set a : ℝ := 1 / ((q : ℝ) - 1) with ha_def
  have ha : 0 < a := by rw [ha_def]; exact div_pos one_pos hq1
  set K : ℝ := d * (1 + q * δ) / (2 * cq q) with hK_def
  have hK : 0 < K := by positivity
  have hd2pos : 0 < d2 q := by linarith
  have hKa : K * a ^ 2 < 1 := by
    have e : K * a ^ 2 = d * (1 + q * δ) / d2 q := by
      rw [d2_eq, hK_def, ha_def]
      field_simp
    rw [e, div_lt_one hd2pos]
    exact hδd
  obtain ⟨ρ₀, hρ₀, hθ1, h4ρ⟩ := SecondMomentAux.exists_rho hK ha hKa
  set T : ℝ := a + 4 * ρ₀ with hT_def
  have hT : 0 ≤ T := by positivity
  set θ : ℝ := K * T ^ 2 with hθ_def
  have hθ0 : 0 ≤ θ := by positivity
  obtain ⟨C, hC⟩ := two_replica_bound hq2 hd hT
  obtain ⟨C', hC'⟩ := exists_sum_exp_empKL_le hθ0 hθ1 (q ^ 2)
  refine ⟨δ, hδ0, ρ₀, hρ₀, fun ρ hρ hρρ₀ => ⟨max C 0 * C', fun n hn t ht => ?_⟩⟩
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := lt_of_lt_of_le hd hn
    exact_mod_cast this
  obtain ⟨htn, htre⟩ := SecondMomentAux.tube_bounds ht
  have htT : ‖t‖ ≤ T := by rw [hT_def]; linarith
  have htT2 : t.re ≤ T ^ 2 := by
    have : a ^ 2 ≤ T ^ 2 := by rw [hT_def]; gcongr; linarith
    linarith
  have h1 := hC n hn (balanced q n δ) t htT htT2
  have hz : (fun G => ‖zhatB G q δ t‖ ^ 2) = fun G : SimpleGraph (Fin n) =>
      ‖((q : ℂ) ^ n)⁻¹ * ∑ σ ∈ balanced q n δ, ∏ e ∈ G.edgeFinset, (1 + t * edgeA q σ e)‖ ^ 2 :=
    rfl
  rw [hz]
  refine h1.trans ?_
  -- the overlap sum
  have hS : ∑ σ ∈ balanced q n δ, ∑ τ ∈ balanced q n δ, Real.exp (d * n * T ^ 2 / 2 *
      ((q : ℝ) ^ 2 * ∑ i, ∑ j, overlap σ τ i j ^ 2 - 1)) ≤ C' * ((q : ℝ) ^ 2) ^ n := by
    calc _ ≤ ∑ σ ∈ balanced q n δ, ∑ τ ∈ balanced q n δ,
          Real.exp (θ * n * empKL (fun v => (σ v, τ v))) := by
          refine Finset.sum_le_sum fun σ hσ => Finset.sum_le_sum fun τ _ => ?_
          refine Real.exp_le_exp.2 ?_
          have h := overlap_energy_le_empKL hq hn0 hδ0 hδq σ τ hσ
          have hc : 0 ≤ d * n * T ^ 2 / 2 := by positivity
          calc d * n * T ^ 2 / 2 * ((q : ℝ) ^ 2 * ∑ i, ∑ j, overlap σ τ i j ^ 2 - 1)
              ≤ d * n * T ^ 2 / 2 * ((1 + q * δ) / cq q * empKL (fun v => (σ v, τ v))) :=
                mul_le_mul_of_nonneg_left h hc
            _ = θ * n * empKL (fun v => (σ v, τ v)) := by
                rw [hθ_def, hK_def]
                field_simp
      _ ≤ ∑ σ ∈ balanced q n δ, ∑ τ : Fin n → Fin q,
          Real.exp (θ * n * empKL (fun v => (σ v, τ v))) :=
          Finset.sum_le_sum fun σ _ => Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _) (fun _ _ _ => (Real.exp_pos _).le)
      _ ≤ ∑ σ : Fin n → Fin q, ∑ τ : Fin n → Fin q,
          Real.exp (θ * n * empKL (fun v => (σ v, τ v))) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
      _ = ∑ f : Fin n → Fin q × Fin q, Real.exp (θ * n * empKL f) :=
          SecondMomentAux.sum_sum_pair_eq (fun f => Real.exp (θ * n * empKL f))
      _ ≤ C' * ((q : ℝ) ^ 2) ^ n := by
          have h := hC' (Fin n) (Fin q × Fin q) (by simp [sq])
          convert h using 3 <;> simp
  set S := ∑ σ ∈ balanced q n δ, ∑ τ ∈ balanced q n δ, Real.exp (d * n * T ^ 2 / 2 *
      ((q : ℝ) ^ 2 * ∑ i, ∑ j, overlap σ τ i j ^ 2 - 1)) with hS_def
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have hx : 0 ≤ (((q : ℝ) ^ n)⁻¹) ^ 2 := by positivity
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  calc C * (((q : ℝ) ^ n)⁻¹) ^ 2 * S ≤ max C 0 * (((q : ℝ) ^ n)⁻¹) ^ 2 * S := by
        gcongr
        exact le_max_left _ _
    _ ≤ max C 0 * (((q : ℝ) ^ n)⁻¹) ^ 2 * (C' * ((q : ℝ) ^ 2) ^ n) := by
        have : 0 ≤ max C 0 := le_max_right _ _
        gcongr
    _ = max C 0 * C' := by
        rw [← pow_mul, mul_comm 2 n, pow_mul]
        field_simp

end

end ERZeroFreeness
