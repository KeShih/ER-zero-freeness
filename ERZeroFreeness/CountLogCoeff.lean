/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.CountDefs

/-! # The logarithmic coefficients of a polynomial

Properties of `logCoeff` (`eq:log-coefficients`), the logarithmic coefficients `ℓ_j(p)` of a
polynomial `p` with `p(0) = 1`.

## Main results

* `logCoeff_recursion`, `logCoeff_unique`: `ℓ(p)` is the unique sequence `ℓ` with `ℓ_0 = 0` and
  `j a_j = ∑_{r=1}^{j} r ℓ_r a_{j-r}` for all `j` (the recursion of the proof of Lemma 8.3).
* `logCoeff_mul`, `logCoeff_multiset_prod`: `log(pq) = log p + log q` coefficientwise.
* `logCoeff_one_sub_C_mul_X`: `ℓ_j(1 - c t) = -c^j / j` for `j ≥ 1`.
* `logCoeff_map`: `ℓ_j` commutes with field homomorphisms.
* `logCoeff_eq_coeff_logOf`: `ℓ_j(p)` is the `j`-th coefficient of the formal logarithm
  `PowerSeries.logOf p`.

## Proof

`logCoeff_zero`, `logCoeff_eq`: unfold the recursion (`rw [logCoeff]`) and reindex
`Fin j ↦ Ico 1 (j+1)`.  `logCoeff_recursion`: `logCoeff_eq` with `a_0 = 1` and `j ≠ 0` in
characteristic zero.  `logCoeff_unique`, `logCoeff_one`, `logCoeff_map`: strong induction on `j`.
`logCoeff_mul`: in `K⟦X⟧` put `D_ℓ = mk (fun i => (i+1) ℓ_{i+1})`; for any sequence `ℓ`, the
recursion for `(p, ℓ)` is equivalent to the ODE `p' = D_ℓ · p` (coefficient `i` is the recursion
at `j = i+1`: `CountLogCoeff_coeff_mk_mul`, `CountLogCoeff_ode_of_rec`,
`CountLogCoeff_rec_of_ode`).  The Leibniz rule (`Polynomial.derivative_mul`) gives
`(pq)' = (D_{ℓ(p)} + D_{ℓ(q)}) · pq`, so `ℓ(p) + ℓ(q)` satisfies the recursion for `pq`, and
`logCoeff_unique` concludes.  `logCoeff_multiset_prod`: multiset induction.
`logCoeff_one_sub_C_mul_X`: `logCoeff_unique` with `ℓ_r = -c^r/r`.
`logCoeff_eq_coeff_logOf`: `G = d/dX log(1 + X) = mk ((-1)^n)` (`PowerSeries.deriv_log`)
satisfies `G · (1 + X) = 1`, hence `G(P - 1) · P = 1` (`substAlgHom` is a ring map); the chain
rule `PowerSeries.derivative_subst` gives `(logOf P)' = G(P - 1) · P'`, i.e.
`P' = (logOf P)' · P`, which is the ODE for `ℓ_r = coeff r (logOf P)`; then `logCoeff_unique`.

Implementation note: `simp [logCoeff]` loops; unfold with a single `rw [logCoeff]`, or use
`logCoeff_eq`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

section CountLogCoeff

variable {K : Type*} [Field K]

/-- `ℓ_0 = 0`. -/
theorem logCoeff_zero (p : K[X]) : logCoeff p 0 = 0 := by
  rw [logCoeff]

/-- The defining recursion in summation form: for `j ≥ 1`,
`ℓ_j = a_j - (1/j) ∑_{r=1}^{j-1} r ℓ_r a_{j-r}` (the displayed recursion of the proof of
`lem:coefficient-oracle`). -/
theorem logCoeff_eq (p : K[X]) {j : ℕ} (hj : 1 ≤ j) :
    logCoeff p j = p.coeff j -
      (∑ r ∈ Finset.Ico 1 j, (r : K) * logCoeff p r * p.coeff (j - r)) / j := by
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [logCoeff]
  congr 2
  · rw [Finset.sum_Ico_eq_sum_range, Fin.sum_univ_eq_sum_range
      (fun r => (((r : ℕ) : K) + 1) * logCoeff p (r + 1) * p.coeff (j - r))]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [add_comm 1 r]
    push_cast
    congr 2
  · simp

/-- `j a_j = ∑_{r=1}^{j} r ℓ_r a_{j-r}` when `a_0 = 1` (logarithmic differentiation of
`eq:log-coefficients`: `p' = p · (log p)'`). -/
theorem logCoeff_recursion [CharZero K] {p : K[X]} (hp : p.coeff 0 = 1) (j : ℕ) :
    (j : K) * p.coeff j = ∑ r ∈ Finset.Icc 1 j, (r : K) * logCoeff p r * p.coeff (j - r) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  rw [← Finset.Ico_insert_right (by omega : 1 ≤ j), Finset.sum_insert (by simp),
    Nat.sub_self, hp, mul_one, logCoeff_eq p hj]
  have hj0 : (j : K) ≠ 0 := by exact_mod_cast hj.ne'
  field_simp
  ring

/-- Uniqueness: the recursion of `logCoeff_recursion`, with `ℓ_0 = 0`, determines the
logarithmic coefficients. -/
theorem logCoeff_unique [CharZero K] {p : K[X]} (hp : p.coeff 0 = 1) {ℓ : ℕ → K} (h0 : ℓ 0 = 0)
    (h : ∀ j : ℕ, (j : K) * p.coeff j = ∑ r ∈ Finset.Icc 1 j, (r : K) * ℓ r * p.coeff (j - r)) :
    ℓ = logCoeff p := by
  funext j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [h0, logCoeff_zero]
    have h1 := h j
    have h2 := logCoeff_recursion hp j
    rw [← Finset.Ico_insert_right (by omega : 1 ≤ j), Finset.sum_insert (by simp),
      Nat.sub_self, hp, mul_one] at h1 h2
    have hs : ∑ r ∈ Finset.Ico 1 j, (r : K) * ℓ r * p.coeff (j - r) =
        ∑ r ∈ Finset.Ico 1 j, (r : K) * logCoeff p r * p.coeff (j - r) :=
      Finset.sum_congr rfl fun r hr => by rw [ih r (Finset.mem_Ico.mp hr).2]
    have hj0 : (j : K) ≠ 0 := by exact_mod_cast hj.ne'
    have : (j : K) * ℓ j = (j : K) * logCoeff p j := by
      rw [hs] at h1; linear_combination h2 - h1
    exact mul_left_cancel₀ hj0 this

/-- `log 1 = 0`. -/
theorem logCoeff_one (j : ℕ) : logCoeff (1 : K[X]) j = 0 := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact logCoeff_zero _
    rw [logCoeff_eq _ hj, Polynomial.coeff_one, if_neg (by omega)]
    rw [Finset.sum_eq_zero fun r hr => by rw [ih r (Finset.mem_Ico.mp hr).2]; ring]
    simp

/-- Coefficient `i` of `D_ℓ · p` in `K⟦X⟧`, where `D_ℓ = ∑ (n+1) ℓ_{n+1} Xⁿ`: it is the
right-hand side of the recursion at `j = i + 1`. -/
private theorem CountLogCoeff_coeff_mk_mul (p : K[X]) (ℓ : ℕ → K) (i : ℕ) :
    PowerSeries.coeff i
        (PowerSeries.mk (fun n => ((n : K) + 1) * ℓ (n + 1)) * (p : PowerSeries K)) =
      ∑ r ∈ Finset.Icc 1 (i + 1), (r : K) * ℓ r * p.coeff (i + 1 - r) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun u v => PowerSeries.coeff u (PowerSeries.mk fun n => ((n : K) + 1) * ℓ (n + 1)) *
      PowerSeries.coeff v (p : PowerSeries K)),
    ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by simp) fun k _ => ?_
  rw [PowerSeries.coeff_mk, Polynomial.coeff_coe, show i + 1 - (1 + k) = i - k by omega,
    add_comm 1 k]
  push_cast
  ring

/-- The recursion of `logCoeff_recursion` for `(p, ℓ)` gives the ODE `p' = D_ℓ · p` in
`K⟦X⟧`. -/
private theorem CountLogCoeff_ode_of_rec {p : K[X]} {ℓ : ℕ → K}
    (h : ∀ j : ℕ, (j : K) * p.coeff j = ∑ r ∈ Finset.Icc 1 j, (r : K) * ℓ r * p.coeff (j - r)) :
    ((Polynomial.derivative p : K[X]) : PowerSeries K) =
      PowerSeries.mk (fun n => ((n : K) + 1) * ℓ (n + 1)) * (p : PowerSeries K) := by
  ext i
  rw [CountLogCoeff_coeff_mk_mul, Polynomial.coeff_coe, Polynomial.coeff_derivative,
    ← h (i + 1)]
  push_cast
  ring

/-- Conversely, the ODE `p' = D_ℓ · p` gives the recursion of `logCoeff_recursion` for
`(p, ℓ)`. -/
private theorem CountLogCoeff_rec_of_ode {p : K[X]} {ℓ : ℕ → K}
    (h : ((Polynomial.derivative p : K[X]) : PowerSeries K) =
      PowerSeries.mk (fun n => ((n : K) + 1) * ℓ (n + 1)) * (p : PowerSeries K)) (j : ℕ) :
    (j : K) * p.coeff j = ∑ r ∈ Finset.Icc 1 j, (r : K) * ℓ r * p.coeff (j - r) := by
  rcases j with _ | i
  · simp
  have := congrArg (PowerSeries.coeff i) h
  rw [CountLogCoeff_coeff_mk_mul, Polynomial.coeff_coe, Polynomial.coeff_derivative] at this
  rw [← this]
  push_cast
  ring

/-- Additivity: `log(pq) = log p + log q` coefficientwise (`p(0) = q(0) = 1`). -/
theorem logCoeff_mul [CharZero K] {p q : K[X]} (hp : p.coeff 0 = 1) (hq : q.coeff 0 = 1)
    (j : ℕ) : logCoeff (p * q) j = logCoeff p j + logCoeff q j := by
  have hpq : (p * q).coeff 0 = 1 := by rw [Polynomial.mul_coeff_zero, hp, hq, one_mul]
  have key := logCoeff_unique hpq (ℓ := fun r => logCoeff p r + logCoeff q r)
    (by rw [logCoeff_zero, logCoeff_zero, add_zero]) ?_
  · exact (congrFun key j).symm
  apply CountLogCoeff_rec_of_ode
  have h1 := CountLogCoeff_ode_of_rec (logCoeff_recursion hp)
  have h2 := CountLogCoeff_ode_of_rec (logCoeff_recursion hq)
  have hD : PowerSeries.mk (fun n => ((n : K) + 1) * (logCoeff p (n + 1) + logCoeff q (n + 1))) =
      PowerSeries.mk (fun n => ((n : K) + 1) * logCoeff p (n + 1)) +
        PowerSeries.mk (fun n => ((n : K) + 1) * logCoeff q (n + 1)) := by
    ext n
    rw [PowerSeries.coeff_mk, map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk, mul_add]
  rw [Polynomial.derivative_mul, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_mul, h1,
    h2, Polynomial.coe_mul, hD]
  ring

/-- Additivity over a finite product. -/
theorem logCoeff_multiset_prod [CharZero K] (s : Multiset K[X]) (hs : ∀ p ∈ s, p.coeff 0 = 1)
    (j : ℕ) : logCoeff s.prod j = (s.map fun p => logCoeff p j).sum := by
  induction s using Multiset.induction_on with
  | empty => rw [Multiset.prod_zero, logCoeff_one, Multiset.map_zero, Multiset.sum_zero]
  | cons a s ih =>
    have ha : a.coeff 0 = 1 := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ p ∈ s, p.coeff 0 = 1 := fun p hp => hs p (Multiset.mem_cons_of_mem hp)
    have hprod : s.prod.coeff 0 = 1 := by
      rw [Polynomial.coeff_zero_multiset_prod]
      refine Multiset.prod_eq_one fun x hx => ?_
      obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hx
      exact hs' p hp
    rw [Multiset.prod_cons, logCoeff_mul ha hprod, ih hs', Multiset.map_cons, Multiset.sum_cons]

/-- `log(1 - c t) = -∑_{j ≥ 1} c^j t^j / j`. -/
theorem logCoeff_one_sub_C_mul_X [CharZero K] (c : K) {j : ℕ} (hj : 1 ≤ j) :
    logCoeff (1 - C c * X) j = -c ^ j / j := by
  -- the hypothesis `1 ≤ j` is not needed: at `j = 0` both sides are `0` (as `x / 0 = 0`)
  have _ := hj
  have hp : (1 - C c * X : K[X]).coeff 0 = 1 := by simp
  have key := logCoeff_unique hp (ℓ := fun r => -c ^ r / r) (by simp) ?_
  · exact (congrFun key j).symm
  intro j
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · interval_cases j
    · simp
    · simp [Finset.Icc_self, Polynomial.coeff_one]
  · -- only `r = j` and `r = j - 1` contribute
    have hcoeff : ∀ i, (1 - C c * X : K[X]).coeff i =
        if i = 0 then 1 else if i = 1 then -c else 0 := by
      intro i
      rcases i with _ | _ | i <;> simp [Polynomial.coeff_one, Polynomial.coeff_X]
    rw [hcoeff j, if_neg (by omega), if_neg (by omega), mul_zero]
    rw [Finset.sum_eq_add_of_mem (j - 1) j (by simp; omega) (by simp; omega) (by omega)]
    · rw [hcoeff, hcoeff, if_neg (by omega), if_pos (by omega), Nat.sub_self, if_pos rfl]
      have hj0 : (j : K) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
      have hj1 : ((j - 1 : ℕ) : K) ≠ 0 := by exact_mod_cast (by omega : j - 1 ≠ 0)
      have hjc : (j : K) = ((j - 1 : ℕ) : K) + 1 := by
        rw [← Nat.cast_succ]; congr 1; omega
      have hpow : c ^ j = c ^ (j - 1) * c := by rw [← pow_succ]; congr 1; omega
      rw [hpow]
      field_simp
      ring
    · intro r hr hne
      rw [hcoeff]
      have : j - r ≠ 0 ∧ j - r ≠ 1 := by
        simp only [Finset.mem_Icc] at hr; omega
      rw [if_neg this.1, if_neg this.2, mul_zero]

/-- The logarithmic coefficients commute with field homomorphisms. -/
theorem logCoeff_map {L : Type*} [Field L] (φ : K →+* L) (p : K[X]) (j : ℕ) :
    logCoeff (p.map φ) j = φ (logCoeff p j) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [logCoeff_zero, logCoeff_zero, map_zero]
    rw [logCoeff_eq _ hj, logCoeff_eq _ hj, map_sub, map_div₀, map_sum, map_natCast,
      Polynomial.coeff_map]
    congr 2
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [ih r (Finset.mem_Ico.mp hr).2, map_mul, map_mul, map_natCast, Polynomial.coeff_map]

/-- **Faithfulness of `logCoeff` to `eq:log-coefficients`.** For `p(0) = 1`, `ℓ_j(p)` is the
`j`-th coefficient of the formal logarithm `log p = ∑_{i ≥ 1} (-1)^{i+1} (p - 1)^i / i`
(Mathlib's `PowerSeries.logOf`, i.e. `log(1+X)` substituted at `p - 1`), the expansion used in
the proof of `lem:local-decomposition`. -/
theorem logCoeff_eq_coeff_logOf {p : ℂ[X]} (hp : p.coeff 0 = 1) (j : ℕ) :
    logCoeff p j = PowerSeries.coeff j (PowerSeries.logOf (p : PowerSeries ℂ)) := by
  set P : PowerSeries ℂ := (p : PowerSeries ℂ) with hPdef
  have hP0 : PowerSeries.constantCoeff P = 1 := by rw [hPdef, Polynomial.constantCoeff_coe, hp]
  have hQ : PowerSeries.constantCoeff (P - 1) = 0 := by rw [map_sub, hP0, map_one, sub_self]
  have hsub : PowerSeries.HasSubst (P - 1) := PowerSeries.HasSubst.of_constantCoeff_zero' hQ
  set G : PowerSeries ℂ := PowerSeries.mk fun n => algebraMap ℚ ℂ ((-1 : ℚ) ^ n) with hGdef
  -- `G = 1/(1+X)`
  have hG : G * (1 + PowerSeries.X) = 1 := by
    ext n
    rw [mul_add, mul_one, map_add]
    rcases n with _ | n
    · simp [hGdef]
    · rw [PowerSeries.coeff_succ_mul_X, hGdef, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
        PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n)]
      simp [pow_succ]
  -- substituting `X ↦ P - 1`: `G(P - 1) · P = 1`
  have hGsub : G.subst (P - 1) * P = 1 := by
    have h := congrArg (PowerSeries.substAlgHom hsub (R := ℂ)) hG
    rw [map_mul, map_add, map_one, PowerSeries.substAlgHom_X, add_sub_cancel,
      PowerSeries.coe_substAlgHom] at h
    exact h
  -- chain rule: `(log P)' = G(P - 1) · P'`
  have hdL : PowerSeries.derivative ℂ (PowerSeries.logOf P) =
      G.subst (P - 1) * PowerSeries.derivative ℂ P := by
    rw [PowerSeries.logOf_eq, PowerSeries.derivative_subst hsub, PowerSeries.deriv_log, map_sub,
      Derivation.map_one_eq_zero, sub_zero]
  have hode : PowerSeries.derivative ℂ P = PowerSeries.derivative ℂ (PowerSeries.logOf P) * P := by
    rw [hdL]
    linear_combination (-(PowerSeries.derivative ℂ P)) * hGsub
  have h0 : PowerSeries.coeff 0 (PowerSeries.logOf P) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_logOf hP0]
  have key := logCoeff_unique hp (ℓ := fun r => PowerSeries.coeff r (PowerSeries.logOf P)) h0 ?_
  · exact (congrFun key j).symm
  apply CountLogCoeff_rec_of_ode
  have hmk : PowerSeries.mk (fun n => ((n : ℂ) + 1) * PowerSeries.coeff (n + 1) (PowerSeries.logOf P))
      = PowerSeries.derivative ℂ (PowerSeries.logOf P) := by
    ext n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_derivative, mul_comm]
  rw [← PowerSeries.derivative_coe, hmk]
  exact hode

end CountLogCoeff

end

end ERZeroFreeness
