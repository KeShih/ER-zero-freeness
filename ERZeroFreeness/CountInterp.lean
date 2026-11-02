/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.CountLogCoeff

/-! # The interpolation estimate of Patel and Regts

Barvinok's interpolation method in the form of [PR]: if `p(0) = 1`, `p` has no zeros in the
open disk of radius `M` and `|t| < M`, then the exponential of `∑_{j ≤ k} ℓ_j(p) t^j` is a
multiplicative `ε`-approximation to `p(t)` once `k ≥ max{1, log(deg(p)/ε)} / (1 - |t|/M)`
(the paragraph before Proposition 8.4).

## Main results

* `eq_multiset_prod_one_sub_of_eval_zero`: `p = ∏_ζ (1 - t/ζ)` over the roots of `p`.
* `logCoeff_eq_sum_roots`: Newton's identity `ℓ_j(p) = -(1/j) ∑_ζ ζ^{-j}`.
* `exists_eval_eq_exp_logCoeff`: the bound (8) in the proof of [PR, Lemma 2.2].
* `interpolation_estimate`: the threshold form used in the paper.

## Proof

Over `ℂ`, `p = C a · ∏_{ζ ∈ roots} (X - C ζ)` (`C_leadingCoeff_mul_prod_multiset_X_sub_C`,
`IsAlgClosed.card_roots_eq_natDegree`); `p(0) = 1` gives `ζ ≠ 0` and `p = ∏ (1 - C ζ⁻¹ X)`.
Newton's identity follows from `logCoeff_multiset_prod` and `logCoeff_one_sub_C_mul_X`.
Bound (8): `p(t) = ∏ (1 + w_ζ)`, `w_ζ = -t/ζ`, `‖w_ζ‖ ≤ ‖t‖/M =: θ < 1` (every root has
`‖ζ‖ ≥ M`); `1 + w = exp(log(1 + w))`, `log(1 + w) = logTaylor (k+1) w + R_ζ` with
`‖R_ζ‖ ≤ θ^{k+1}(1-θ)⁻¹/(k+1)` (`Complex.norm_log_sub_logTaylor_le`), and
`∑_ζ logTaylor (k+1) (-t/ζ) = ∑_{j=1}^{k} ℓ_j t^j` by Newton's identity; then `E = ∑_ζ R_ζ`,
and there are `deg(p)` roots.  The threshold form follows from bound (8) by the elementary
estimate `CountInterp_tail_le` (`θ ≤ e^{θ-1}`, `k(1-θ) ≥ 1`).

## References

* [PR] V. Patel and G. Regts, *Deterministic polynomial-time approximation algorithms for
  partition functions and graph polynomials*, SIAM J. Comput. 46(6) (2017), 1893–1919.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

section CountInterp

/-- A polynomial with `p(0) = 1` is not zero. -/
private theorem CountInterp_ne_zero {p : ℂ[X]} (hp : p.eval 0 = 1) : p ≠ 0 := by
  rintro rfl
  rw [eval_zero] at hp
  exact zero_ne_one hp

/-- The roots of a polynomial with `p(0) = 1` are nonzero. -/
private theorem CountInterp_root_ne_zero {p : ℂ[X]} (hp : p.eval 0 = 1) {ζ : ℂ}
    (hζ : ζ ∈ p.roots) : ζ ≠ 0 := by
  rintro rfl
  rw [mem_roots (CountInterp_ne_zero hp), IsRoot.def, hp] at hζ
  exact one_ne_zero hζ

/-- `X - ζ = (-ζ) (1 - ζ⁻¹ X)` for `ζ ≠ 0`. -/
private theorem CountInterp_X_sub_C {ζ : ℂ} (hζ : ζ ≠ 0) :
    X - C ζ = C (-ζ) * (1 - C ζ⁻¹ * X) := by
  have h1 : C ζ * C ζ⁻¹ = (1 : ℂ[X]) := by rw [← C_mul, mul_inv_cancel₀ hζ, C_1]
  rw [C_neg]
  linear_combination (-X) * h1

/-- The product `∏_ζ (1 - ζ⁻¹ X)` takes the value `1` at `0`. -/
private theorem CountInterp_eval_zero_prod (s : Multiset ℂ) :
    ((s.map fun ζ => 1 - C ζ⁻¹ * X).prod).eval 0 = 1 := by
  rw [eval_multiset_prod, Multiset.map_map]
  refine Multiset.prod_eq_one fun x hx => ?_
  obtain ⟨ζ, -, rfl⟩ := Multiset.mem_map.mp hx
  simp

/-- A polynomial with `p(0) = 1` is the product of `1 - t/ζ` over its roots (with
multiplicity). -/
theorem eq_multiset_prod_one_sub_of_eval_zero {p : ℂ[X]} (hp : p.eval 0 = 1) :
    p = (p.roots.map fun ζ => 1 - C ζ⁻¹ * X).prod := by
  have hsplit : C p.leadingCoeff * (p.roots.map fun a => X - C a).prod = p :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree
  have hc : p = C (p.leadingCoeff * (p.roots.map fun ζ => -ζ).prod) *
      (p.roots.map fun ζ => 1 - C ζ⁻¹ * X).prod := by
    conv_lhs => rw [← hsplit]
    rw [Multiset.map_congr rfl fun ζ hζ => CountInterp_X_sub_C (CountInterp_root_ne_zero hp hζ),
      Multiset.prod_map_mul, C_mul, mul_assoc, _root_.map_multiset_prod C, Multiset.map_map]
    rfl
  have hc1 : p.leadingCoeff * (p.roots.map fun ζ => -ζ).prod = 1 := by
    have := congrArg (eval 0) hc
    rw [hp, eval_mul, eval_C, CountInterp_eval_zero_prod, mul_one] at this
    exact this.symm
  rw [hc1, C_1, one_mul] at hc
  exact hc

/-- Newton's identity `ℓ_j(p) = -(1/j) ∑_ζ ζ^{-j}` for `j ≥ 1`, summed over the roots with
multiplicity (proof of [PR, Lemma 2.2]). -/
theorem logCoeff_eq_sum_roots {p : ℂ[X]} (hp : p.eval 0 = 1) {j : ℕ} (hj : 1 ≤ j) :
    logCoeff p j = -(p.roots.map fun ζ => ζ⁻¹ ^ j).sum / j := by
  have hs : ∀ q ∈ p.roots.map (fun ζ => 1 - C ζ⁻¹ * X), q.coeff 0 = 1 := by
    intro q hq
    obtain ⟨ζ, -, rfl⟩ := Multiset.mem_map.mp hq
    simp
  calc logCoeff p j = logCoeff (p.roots.map fun ζ => 1 - C ζ⁻¹ * X).prod j :=
        congrArg (fun q => logCoeff q j) (eq_multiset_prod_one_sub_of_eval_zero hp)
    _ = ((p.roots.map fun ζ => 1 - C ζ⁻¹ * X).map fun q => logCoeff q j).sum :=
        logCoeff_multiset_prod _ hs j
    _ = (p.roots.map fun ζ => -(ζ⁻¹ ^ j) / (j : ℂ)).sum := by
        rw [Multiset.map_map]
        congr 1
        exact Multiset.map_congr rfl fun ζ _ => logCoeff_one_sub_C_mul_X ζ⁻¹ hj
    _ = -(p.roots.map fun ζ => ζ⁻¹ ^ j).sum / j := by
        rw [Multiset.sum_map_div, Multiset.sum_map_neg]

/-- A multiset sum of finite sums is the finite sum of the multiset sums. -/
private theorem CountInterp_msum_fsum {ι : Type*} (s : Multiset ι) (S : Finset ℕ)
    (f : ι → ℕ → ℂ) :
    (s.map fun a => ∑ j ∈ S, f a j).sum = ∑ j ∈ S, (s.map fun a => f a j).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Multiset.map_cons, Multiset.sum_cons]

/-- The `j`-th term of `logTaylor` at `w = -t/ζ`. -/
private theorem CountInterp_term (ζ t : ℂ) (j : ℕ) :
    (-1) ^ (j + 1) * (-(ζ⁻¹ * t)) ^ j / (j : ℂ) = ζ⁻¹ ^ j * (-(t ^ j) / j) := by
  have h : ((-1 : ℂ)) ^ (j + 1) * (-1) ^ j = -1 := by
    rw [← pow_add]
    exact Odd.neg_one_pow ⟨j, by ring⟩
  have h3 : (-(ζ⁻¹ * t)) ^ j = (-1) ^ j * (ζ⁻¹ ^ j * t ^ j) := by rw [neg_pow, mul_pow]
  rw [h3]
  linear_combination (ζ⁻¹ ^ j * t ^ j / j) * h

/-- Newton's identity summed against `t^j`: the sum over the roots of the
Taylor polynomials `logTaylor (k+1) (-t/ζ)` is `∑_{j=1}^{k} ℓ_j t^j`. -/
private theorem CountInterp_sum_logTaylor {p : ℂ[X]} (hp : p.eval 0 = 1) (t : ℂ) (k : ℕ) :
    (p.roots.map fun ζ => Complex.logTaylor (k + 1) (-(ζ⁻¹ * t))).sum =
      ∑ j ∈ Finset.Icc 1 k, logCoeff p j * t ^ j := by
  have h1 : (p.roots.map fun ζ => Complex.logTaylor (k + 1) (-(ζ⁻¹ * t))).sum =
      ∑ j ∈ Finset.range (k + 1),
        (p.roots.map fun ζ => (-1) ^ (j + 1) * (-(ζ⁻¹ * t)) ^ j / (j : ℂ)).sum :=
    CountInterp_msum_fsum p.roots (Finset.range (k + 1))
      (fun ζ j => (-1) ^ (j + 1) * (-(ζ⁻¹ * t)) ^ j / (j : ℂ))
  have h2 : ∀ j : ℕ, (p.roots.map fun ζ => (-1) ^ (j + 1) * (-(ζ⁻¹ * t)) ^ j / (j : ℂ)).sum =
      (p.roots.map fun ζ => ζ⁻¹ ^ j).sum * (-(t ^ j) / j) := by
    intro j
    rw [← Multiset.sum_map_mul_right]
    congr 1
    exact Multiset.map_congr rfl fun ζ _ => CountInterp_term ζ t j
  have h3 : ∀ j : ℕ, (p.roots.map fun ζ => (-1) ^ (j + 1) * (-(ζ⁻¹ * t)) ^ j / (j : ℂ)).sum =
      logCoeff p j * t ^ j := by
    intro j
    rw [h2]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [logCoeff_zero]
    · rw [logCoeff_eq_sum_roots hp hj]
      ring
  rw [h1, Finset.sum_congr rfl fun j _ => h3 j]
  refine (Finset.sum_subset (fun j hj => ?_) (fun j hj hj' => ?_)).symm
  · rw [Finset.mem_Icc] at hj
    rw [Finset.mem_range]
    omega
  · rw [Finset.mem_Icc] at hj'
    rw [Finset.mem_range] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    rw [logCoeff_zero, zero_mul]

/-- The Taylor remainder of `log(1 + w)` for `‖w‖ ≤ θ < 1`
(`Complex.norm_log_sub_logTaylor_le`, and `x ↦ x^{k+1}/(1-x)` is increasing on `[0,1)`). -/
private theorem CountInterp_remainder_le {w : ℂ} {θ : ℝ} (hw : ‖w‖ ≤ θ) (hθ1 : θ < 1) (k : ℕ) :
    ‖Complex.log (1 + w) - Complex.logTaylor (k + 1) w‖ ≤
      θ ^ (k + 1) * (1 - θ)⁻¹ / (k + 1) := by
  have hw1 : ‖w‖ < 1 := lt_of_le_of_lt hw hθ1
  have h1 : 0 < 1 - θ := by linarith
  have h2 : (1 - ‖w‖)⁻¹ ≤ (1 - θ)⁻¹ := inv_anti₀ h1 (by linarith)
  refine (Complex.norm_log_sub_logTaylor_le k hw1).trans ?_
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hw _) h2
    (inv_nonneg.mpr (by linarith)) (pow_nonneg ((norm_nonneg _).trans hw) _)

/-- `1 + w = exp(logTaylor (k+1) w + R)` with
`R = log(1 + w) - logTaylor (k+1) w`, for `‖w‖ < 1`. -/
private theorem CountInterp_one_add_eq_exp {w : ℂ} (hw : ‖w‖ < 1) (k : ℕ) :
    1 + w = Complex.exp (Complex.logTaylor (k + 1) w +
      (Complex.log (1 + w) - Complex.logTaylor (k + 1) w)) := by
  have hne : 1 + w ≠ 0 := by
    intro h
    have hw' : w = -1 := by linear_combination h
    rw [hw', norm_neg, norm_one] at hw
    exact lt_irrefl _ hw
  rw [add_sub_cancel, Complex.exp_log hne]

/-- **Interpolation estimate (bound (8) in the proof of [PR, Lemma 2.2]).** If `p(0) = 1`,
`p` has no zeros in the open disk of radius `M` and `|t| < M`, then
`p(t) = exp(∑_{j ≤ k} ℓ_j(p) t^j + E)` with
`|E| ≤ deg(p) (|t|/M)^{k+1} / ((k+1)(1 - |t|/M))`. -/
theorem exists_eval_eq_exp_logCoeff {p : ℂ[X]} (hp : p.eval 0 = 1) {M : ℝ}
    (hzf : ∀ z : ℂ, ‖z‖ < M → p.eval z ≠ 0) {t : ℂ} (ht : ‖t‖ < M) (k : ℕ) :
    ∃ E : ℂ, p.eval t = Complex.exp (∑ j ∈ Finset.Icc 1 k, logCoeff p j * t ^ j + E) ∧
      ‖E‖ ≤ p.natDegree * (‖t‖ / M) ^ (k + 1) / ((k + 1) * (1 - ‖t‖ / M)) := by
  have hM : 0 < M := lt_of_le_of_lt (norm_nonneg t) ht
  have hθ1 : ‖t‖ / M < 1 := by rw [div_lt_one hM]; exact ht
  have hp0 : p ≠ 0 := CountInterp_ne_zero hp
  -- every root lies outside the disk, so `‖-t/ζ‖ ≤ ‖t‖/M`
  have hw_le : ∀ ζ ∈ p.roots, ‖-(ζ⁻¹ * t)‖ ≤ ‖t‖ / M := by
    intro ζ hζ
    have h1 : M ≤ ‖ζ‖ := by
      by_contra h
      exact hzf ζ (not_le.mp h) ((mem_roots hp0).mp hζ)
    rw [norm_neg, norm_mul, norm_inv, inv_mul_eq_div]
    exact div_le_div_of_nonneg_left (norm_nonneg t) hM h1
  refine ⟨(p.roots.map fun ζ => Complex.log (1 + -(ζ⁻¹ * t)) -
    Complex.logTaylor (k + 1) (-(ζ⁻¹ * t))).sum, ?_, ?_⟩
  · have heval : p.eval t = (p.roots.map fun ζ => 1 + -(ζ⁻¹ * t)).prod := by
      have h := congrArg (eval t) (eq_multiset_prod_one_sub_of_eval_zero hp)
      rw [h, eval_multiset_prod, Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun ζ _ => ?_
      rw [Function.comp_apply, eval_sub, eval_one, eval_mul, eval_C, eval_X, sub_eq_add_neg]
    rw [heval, ← CountInterp_sum_logTaylor hp t k, ← Multiset.sum_map_add,
      Complex.exp_multiset_sum, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun ζ hζ => ?_
    exact CountInterp_one_add_eq_exp (lt_of_le_of_lt (hw_le ζ hζ) hθ1) k
  · calc ‖(p.roots.map fun ζ => Complex.log (1 + -(ζ⁻¹ * t)) -
          Complex.logTaylor (k + 1) (-(ζ⁻¹ * t))).sum‖
        ≤ (p.roots.map fun ζ => ‖Complex.log (1 + -(ζ⁻¹ * t)) -
          Complex.logTaylor (k + 1) (-(ζ⁻¹ * t))‖).sum := by
          refine (norm_multiset_sum_le _).trans_eq ?_
          rw [Multiset.map_map]
          rfl
      _ ≤ (p.roots.map fun _ => (‖t‖ / M) ^ (k + 1) * (1 - ‖t‖ / M)⁻¹ / (k + 1)).sum :=
          Multiset.sum_map_le_sum_map _ _ fun ζ hζ =>
            CountInterp_remainder_le (hw_le ζ hζ) hθ1 k
      _ = p.natDegree * ((‖t‖ / M) ^ (k + 1) * (1 - ‖t‖ / M)⁻¹ / (k + 1)) := by
          rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul,
            IsAlgClosed.card_roots_eq_natDegree]
      _ = p.natDegree * (‖t‖ / M) ^ (k + 1) / ((k + 1) * (1 - ‖t‖ / M)) := by
          simp only [div_eq_mul_inv, mul_inv]
          ring

/-- The step from bound (8) (`exists_eval_eq_exp_logCoeff`) to the paper's threshold: if
`k ≥ max{1, log(N/ε)}/(1-θ)` then `N θ^{k+1} / ((k+1)(1-θ)) ≤ ε` (by `θ ≤ e^{θ-1}` and
`k(1-θ) ≥ 1`). -/
private theorem CountInterp_tail_le {N θ ε : ℝ} (hN : 0 ≤ N) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hε : 0 < ε) {k : ℕ} (hk : max 1 (Real.log (N / ε)) / (1 - θ) ≤ k) :
    N * θ ^ (k + 1) / ((k + 1) * (1 - θ)) ≤ ε := by
  have h1θ : 0 < 1 - θ := by linarith
  rw [div_le_iff₀ h1θ] at hk
  have hk1 : 1 ≤ (k : ℝ) * (1 - θ) := le_trans (le_max_left _ _) hk
  have hkl : Real.log (N / ε) ≤ (k : ℝ) * (1 - θ) := le_trans (le_max_right _ _) hk
  have hden : 1 ≤ ((k : ℝ) + 1) * (1 - θ) := by nlinarith
  have hθk : θ ^ (k + 1) ≤ Real.exp (-((k : ℝ) * (1 - θ))) := by
    have h1 : θ ≤ Real.exp (θ - 1) := by linarith [Real.add_one_le_exp (θ - 1)]
    have h2 : θ ^ k ≤ Real.exp (θ - 1) ^ k := pow_le_pow_left₀ hθ0 h1 k
    rw [← Real.exp_nat_mul] at h2
    have h3 : θ ^ (k + 1) ≤ θ ^ k := pow_le_pow_of_le_one hθ0 hθ1.le (Nat.le_succ k)
    calc θ ^ (k + 1) ≤ θ ^ k := h3
      _ ≤ Real.exp (k * (θ - 1)) := h2
      _ = Real.exp (-((k : ℝ) * (1 - θ))) := by congr 1; ring
  have hnum : N * θ ^ (k + 1) ≤ ε := by
    rcases hN.eq_or_lt with h | h
    · rw [← h, zero_mul]; exact hε.le
    · have hexp : Real.exp (-((k : ℝ) * (1 - θ))) ≤ ε / N := by
        calc Real.exp (-((k : ℝ) * (1 - θ))) ≤ Real.exp (-Real.log (N / ε)) :=
              Real.exp_le_exp.mpr (by linarith)
          _ = ε / N := by rw [Real.exp_neg, Real.exp_log (div_pos h hε), inv_div]
      calc N * θ ^ (k + 1) ≤ N * (ε / N) := mul_le_mul_of_nonneg_left (hθk.trans hexp) hN
        _ = ε := by field_simp
  calc N * θ ^ (k + 1) / ((k + 1) * (1 - θ)) ≤ N * θ ^ (k + 1) :=
        div_le_self (mul_nonneg hN (pow_nonneg hθ0 _)) hden
    _ ≤ ε := hnum

/-- **The interpolation estimate in the paper's threshold form** (paragraph before
`prop:counting`): under the hypotheses of `exists_eval_eq_exp_logCoeff`, once
`k ≥ max{1, log(deg(p)/ε)} / (1 - |t|/M)`, the exponential of `∑_{j ≤ k} ℓ_j(p) t^j` is a
multiplicative `ε`-approximation to `p(t)`: `p(t) = exp(∑_{j ≤ k} ℓ_j t^j + E)` with `|E| ≤ ε`
(so the modulus ratio lies in `[e^{-ε}, e^{ε}]` and the angle is at most `ε`, as in
[PR, Definition 1.1]). -/
theorem interpolation_estimate {p : ℂ[X]} (hp : p.eval 0 = 1) {M : ℝ}
    (hzf : ∀ z : ℂ, ‖z‖ < M → p.eval z ≠ 0) {t : ℂ} (ht : ‖t‖ < M) {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} (hk : max 1 (Real.log (p.natDegree / ε)) / (1 - ‖t‖ / M) ≤ k) :
    ∃ E : ℂ, p.eval t = Complex.exp (∑ j ∈ Finset.Icc 1 k, logCoeff p j * t ^ j + E) ∧
      ‖E‖ ≤ ε := by
  obtain ⟨E, hE, hEb⟩ := exists_eval_eq_exp_logCoeff hp hzf ht k
  have hM : 0 < M := lt_of_le_of_lt (norm_nonneg t) ht
  refine ⟨E, hE, hEb.trans (CountInterp_tail_le (Nat.cast_nonneg _)
    (div_nonneg (norm_nonneg t) hM.le) ?_ hε hk)⟩
  rwa [div_lt_one hM]

end CountInterp

end

end ERZeroFreeness
