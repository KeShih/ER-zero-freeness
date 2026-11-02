/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.SecondMoment

/-! # `lem:moment-bound` on `L_{4ρ}(I_s)` (Appendix B)

For `q ≥ 3`, `s > 0` and `d s² < 2 c_q`, the balanced second moment `E|Ẑ^B_{G_n}(t)|²` is
bounded uniformly in `n ≥ d` and `t ∈ L_{4ρ}(I_s)`, `I_s = [-s, 0]`, for all small `ρ > 0`
(`pt_second_moment_bound`).  For `s = 1/(q-1)` this is `second_moment_bound`.

Proof.  As for `second_moment_bound`, with `1/(q-1)` replaced by `s`.  `pt_exists_delta`:
with `a := d s²` and `ε := 2c_q - a`, take `δ := min (1/(2q)) (ε/(2(a+1)q))`.
`pt_second_moment_bound`: `K := d(1+qδ)/(2c_q)` satisfies `K s² < 1`;
`SecondMomentAux.exists_rho K s` gives `ρ₀` with `K(s+4ρ₀)² < 1` and `4ρ₀ ≤ s²`; put
`T := s + 4ρ₀` and `θ := K T² < 1`.  On `L_{4ρ}(I_s)` with `ρ ≤ ρ₀`, `‖t‖ ≤ T` and
`Re t ≤ 4ρ ≤ s² ≤ T²` (`SecondMomentAux.tube_bounds`); then `two_replica_bound`,
`overlap_energy_le_empKL`, `SecondMomentAux.sum_sum_pair_eq` and `exists_sum_exp_empKL_le` with
`k = q²` give the bound `max C 0 * C'`, as in `second_moment_bound`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- Choice of `δ` (Appendix B: "Fix `δ` with `d(1+qδ)s² < 2c_q`"): if `d s² < 2 c_q` there is
`δ ∈ (0, 1/q)` with `d (1 + qδ) s² < 2 c_q`.  Generalizes `SecondMomentAux.exists_delta` (the
case `s = 1/(q-1)`). -/
theorem pt_exists_delta {q : ℕ} (hq : 3 ≤ q) {d : ℝ} (hd : 0 < d) {s : ℝ}
    (hds : d * s ^ 2 < 2 * cq q) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / (q : ℝ) ∧ d * (1 + q * δ) * s ^ 2 < 2 * cq q := by
  have hq0 : (0 : ℝ) < q := by
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  set a := d * s ^ 2 with ha
  have ha0 : 0 ≤ a := by positivity
  set ε := 2 * cq q - a with hε
  have hε0 : 0 < ε := by linarith
  refine ⟨min (1 / (2 * (q : ℝ))) (ε / (2 * (a + 1) * q)),
    lt_min (by positivity) (by positivity), ?_, ?_⟩
  · calc min (1 / (2 * (q : ℝ))) (ε / (2 * (a + 1) * q)) ≤ 1 / (2 * (q : ℝ)) := min_le_left _ _
      _ < 1 / q := one_div_lt_one_div_of_lt hq0 (by linarith)
  · set δ := min (1 / (2 * (q : ℝ))) (ε / (2 * (a + 1) * q))
    have h1 : δ ≤ ε / (2 * (a + 1) * q) := min_le_right _ _
    have h2 : d * (1 + q * δ) * s ^ 2 = a + q * δ * a := by rw [ha]; ring
    have h3 : q * δ ≤ ε / (2 * (a + 1)) := by
      calc q * δ ≤ q * (ε / (2 * (a + 1) * q)) := by gcongr
        _ = ε / (2 * (a + 1)) := by field_simp
    have h4 : q * δ * a ≤ ε / (2 * (a + 1)) * a := mul_le_mul_of_nonneg_right h3 ha0
    have h5 : ε / (2 * (a + 1)) * a < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith

/-- **`lem:moment-bound` on the tube `L_{4ρ}(I_s)`** (Appendix B, with `T = s + 4ρ₀`).
Generalizes `second_moment_bound` (the case `s = 1/(q-1)`, where `d s² < 2 c_q` is
`d < d₂(q)`). -/
theorem pt_second_moment_bound {q : ℕ} (hq : 3 ≤ q) {d : ℝ} (hd : 0 < d) {s : ℝ} (hs : 0 < s)
    (hds : d * s ^ 2 < 2 * cq q) :
    ∃ δ > 0, ∃ ρ₀ > 0, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ B : ℝ, ∀ n : ℕ, d ≤ n →
      ∀ t ∈ tube s (4 * ρ),
        erExp n (d / n) (fun G => ‖zhatB G q δ t‖ ^ 2) ≤ B := by
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hq2 : 2 ≤ q := by omega
  have hcq := cq_pos hq
  obtain ⟨δ, hδ0, hδq, hδd⟩ := pt_exists_delta hq hd hds
  set K : ℝ := d * (1 + q * δ) / (2 * cq q) with hK_def
  have hK : 0 < K := by positivity
  have hKa : K * s ^ 2 < 1 := by
    have e : K * s ^ 2 = d * (1 + q * δ) * s ^ 2 / (2 * cq q) := by
      rw [hK_def]; ring
    rw [e, div_lt_one (by positivity)]
    exact hδd
  obtain ⟨ρ₀, hρ₀, hθ1, h4ρ⟩ := SecondMomentAux.exists_rho hK hs hKa
  set T : ℝ := s + 4 * ρ₀ with hT_def
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
    have : s ^ 2 ≤ T ^ 2 := by rw [hT_def]; gcongr; linarith
    linarith
  have h1 := hC n hn (balanced q n δ) t htT htT2
  have hz : (fun G => ‖zhatB G q δ t‖ ^ 2) = fun G : SimpleGraph (Fin n) =>
      ‖((q : ℂ) ^ n)⁻¹ * ∑ σ ∈ balanced q n δ, ∏ e ∈ G.edgeFinset, (1 + t * edgeA q σ e)‖ ^ 2 :=
    rfl
  rw [hz]
  refine h1.trans ?_
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
