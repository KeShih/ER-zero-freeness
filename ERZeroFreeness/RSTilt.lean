/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSPoisPi
import ERZeroFreeness.RSModel

/-!
# Appendix C: Poisson averages (`app:rs-poisson`)

The tilting identities of `app:rs-poisson`, as pointwise identities of mass functions (so that the
expectation forms hold for every integrand, with no integrability side conditions), and the
first-moment facts `eq:rs-first-moment`, `eq:rs-marginal`:

* `rs_one_tilt_pt`, `rs_one_tilt` (`eq:rs-one-tilt`):
  `𝖯_s(N) w_{N,t}(σ) = e^{κ_s(σ)} 𝖯^σ_s(N)`;
* `rs_pair_tilt_pt`, `rs_pair_tilt` (`eq:rs-pair-tilt`):
  `𝖯_s(N) w_{N,t}(σ) w_{N,t}(τ) = e^{n φ^s_{x,x}(R)} 𝖯^{σ,τ}_s(N)`;
* `rs_two_tilt` (`eq:rs-two-tilt` with `z' = z̄`, complex `t`):
  `E_{𝖯_s}[w_{G,t}(σ) conj w_{G,t}(τ)] = e^{n φ^s_{t,t̄}(R)}`;
* `rs_poisson_first_moment` (`eq:rs-first-moment`): `e^{-s/2} ≤ E_{𝖯_s} F_G(x) ≤ 1`;
* `rs_marginal` (`eq:rs-marginal`): `E_{𝖯_s}[q^{-n} ∑_{σ ∈ 𝒜} w_{G,x}(σ)] ≤ |𝒜|/q^n`.

## Proof

Tilts: `rs_poisPi_mul_prod_pow` with `y_{uv} = M_t(σ_u,σ_v)` (resp. the product of two entries),
`∑_{uv} (s/(2n))(M_t(σ_u,σ_v) - 1) = κ_s(σ)` (`Fintype.sum_prod_type`), and
`(s/(2n)) M = s M/(2n)`.  Expectation forms: `tsum_mul_left`.  Complex two-tilt:
`rs_hasSum_poisPi_mul_prod_pow_complex` with `y_{uv} = M_t(σ_u,σ_v) conj M_t(τ_u,τ_v)`
(`map_prod`, `map_pow`, `mul_pow`).  First moment: by the one-tilt with `Φ = 1` and total mass one
of `𝖯^σ_s` (`rs_hasSum_poisPi`), `E F = q^{-n} ∑_σ e^{κ_s(σ)}`.  Upper bound: `κ_s ≤ 0` because
`∑_{u,v} A_{σ_uσ_v} = n² q ‖α(σ) - u‖² ≥ 0` (`TwoReplicaAux.sum_aa_nonneg`) and `t ≤ 0`.  Lower
bound (Jensen via `e^y ≥ e^m (1 + y - m)`, `Real.add_one_le_exp`): for `n ≥ 1` the average of
`κ_s` is `s t (q-1)/2 ≥ -s/2`, since `∑_σ A_{σ_uσ_v} = 0` for `u ≠ v` (`Equiv.funSplitAt`, row
sums of `A` vanish) and `= q^n (q-1)` for `u = v`, and `t (q-1) ≥ -1`; for `n = 0` it is `0`.
Marginal: the same identity restricted to `σ ∈ 𝒜`, with `e^{κ_s} ≤ 1`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- **`eq:rs-one-tilt`, pointwise.** `𝖯_s(N) w_{N,t}(σ) = e^{κ_s(σ)} 𝖯^σ_s(N)` (any real `s, t`). -/
theorem rs_one_tilt_pt {q n : ℕ} (s t : ℝ) (σ : Fin n → Fin q) (N : RSGraph n) :
    poisPi (rsMean n s) N * rsW q t N σ =
      Real.exp (rsKappa q n s t σ) * poisPi (cpMean (fun a b => s * rsM q t a b) σ) N := by
  have h := rs_poisPi_mul_prod_pow (rsMean n s) (fun uv => rsM q t (σ uv.1) (σ uv.2)) N
  have e1 : (fun uv : Fin n × Fin n => rsMean n s uv * rsM q t (σ uv.1) (σ uv.2)) =
      cpMean (fun a b => s * rsM q t a b) σ := by
    funext uv
    simp only [rsMean, cpMean]
    ring
  have e2 : ∑ uv : Fin n × Fin n, rsMean n s uv * (rsM q t (σ uv.1) (σ uv.2) - 1) =
      rsKappa q n s t σ := by
    simp only [rsMean, rsKappa, rsM, add_sub_cancel_left, Fintype.sum_prod_type, Finset.mul_sum]
  rw [e1, e2] at h
  exact h

/-- **`eq:rs-one-tilt`.** `E_{𝖯_s}[w_{G,t}(σ) Φ(G)] = e^{κ_s(σ)} E_{𝖯^σ_s} Φ` (every `Φ`; both sides
are `tsum`s of families that are summable simultaneously). -/
theorem rs_one_tilt {q n : ℕ} (s t : ℝ) (σ : Fin n → Fin q) (Φ : RSGraph n → ℝ) :
    rsExp n s (fun N => rsW q t N σ * Φ N) =
      Real.exp (rsKappa q n s t σ) * poisPiExp (cpMean (fun a b => s * rsM q t a b) σ) Φ := by
  unfold rsExp poisPiExp
  rw [← tsum_mul_left]
  refine tsum_congr fun N => ?_
  rw [← mul_assoc, rs_one_tilt_pt, mul_assoc]

/-- **`eq:rs-pair-tilt`, pointwise.**
`𝖯_s(N) w_{N,t}(σ) w_{N,t}(τ) = e^{n φ^s_{x,x}(R_{σ,τ})} 𝖯^{σ,τ}_s(N)` (any real `s, t`). -/
theorem rs_pair_tilt_pt {q n : ℕ} (s t : ℝ) (σ τ : Fin n → Fin q) (N : RSGraph n) :
    poisPi (rsMean n s) N * (rsW q t N σ * rsW q t N τ) =
      Real.exp (rsPairExpoR q n s t σ τ) *
        poisPi (cpMean (rsPairK q s t) (fun v => (σ v, τ v))) N := by
  have hw : rsW q t N σ * rsW q t N τ =
      ∏ uv : Fin n × Fin n, (rsM q t (σ uv.1) (σ uv.2) * rsM q t (τ uv.1) (τ uv.2)) ^ N uv := by
    simp only [rsW, mul_pow, Finset.prod_mul_distrib]
  have h := rs_poisPi_mul_prod_pow (rsMean n s)
    (fun uv => rsM q t (σ uv.1) (σ uv.2) * rsM q t (τ uv.1) (τ uv.2)) N
  have e1 : (fun uv : Fin n × Fin n =>
      rsMean n s uv * (rsM q t (σ uv.1) (σ uv.2) * rsM q t (τ uv.1) (τ uv.2))) =
      cpMean (rsPairK q s t) (fun v => (σ v, τ v)) := by
    funext uv
    simp only [rsMean, cpMean, rsPairK]
    ring
  have e2 : ∑ uv : Fin n × Fin n,
      rsMean n s uv * (rsM q t (σ uv.1) (σ uv.2) * rsM q t (τ uv.1) (τ uv.2) - 1) =
      rsPairExpoR q n s t σ τ := by
    simp only [rsMean, rsPairExpoR, Fintype.sum_prod_type, Finset.mul_sum]
  rw [e1, e2] at h
  rw [hw]
  exact h

/-- **`eq:rs-pair-tilt`.** `E_{𝖯_s}[w(σ) w(τ) Φ] = e^{n φ^s_{x,x}(R)} E_{𝖯^{σ,τ}_s} Φ` (every `Φ`).
-/
theorem rs_pair_tilt {q n : ℕ} (s t : ℝ) (σ τ : Fin n → Fin q) (Φ : RSGraph n → ℝ) :
    rsExp n s (fun N => rsW q t N σ * rsW q t N τ * Φ N) =
      Real.exp (rsPairExpoR q n s t σ τ) *
        poisPiExp (cpMean (rsPairK q s t) (fun v => (σ v, τ v))) Φ := by
  unfold rsExp poisPiExp
  rw [← tsum_mul_left]
  refine tsum_congr fun N => ?_
  rw [← mul_assoc, rs_pair_tilt_pt, mul_assoc]

/-- **`eq:rs-two-tilt`** (with `z' = z̄`): for complex `t` and `s ≥ 0`,
`E_{𝖯_s}[w_{G,t}(σ) conj(w_{G,t}(τ))] = exp(n φ^s_{t,t̄}(R_{σ,τ}))`, absolutely convergent. -/
theorem rs_two_tilt {q n : ℕ} {s : ℝ} (hs : 0 ≤ s) (t : ℂ) (σ τ : Fin n → Fin q) :
    HasSum (fun N : RSGraph n =>
        (poisPi (rsMean n s) N : ℂ) * (rsW q t N σ * starRingEnd ℂ (rsW q t N τ)))
      (Complex.exp (rsPairExpo q n s t σ τ)) := by
  have hlam : ∀ uv, 0 ≤ rsMean n s uv := fun uv => by unfold rsMean; positivity
  have H := rs_hasSum_poisPi_mul_prod_pow_complex hlam (fun uv =>
    rsM q t (σ uv.1) (σ uv.2) * starRingEnd ℂ (rsM q t (τ uv.1) (τ uv.2)))
  have hval : rsPairExpo q n s t σ τ = ∑ uv : Fin n × Fin n, ((rsMean n s uv : ℝ) : ℂ) *
      (rsM q t (σ uv.1) (σ uv.2) * starRingEnd ℂ (rsM q t (τ uv.1) (τ uv.2)) - 1) := by
    simp only [rsPairExpo, rsMean]
    rw [Finset.mul_sum, Fintype.sum_prod_type]
    simp only [Finset.mul_sum]
  rw [hval]
  refine H.congr_fun fun N => ?_
  simp only [rsW, map_prod, map_pow, mul_pow, Finset.prod_mul_distrib]

namespace RSTiltAux

open TwoReplicaAux

/-- `κ_s(σ)` written with the real entries `aa` of `A`. -/
theorem rsKappa_eq_aa {q n : ℕ} (s t : ℝ) (σ : Fin n → Fin q) :
    rsKappa q n s t σ = s / (2 * n) * (t * ∑ u, ∑ v, aa q (σ u) (σ v)) := by
  simp only [rsKappa, rs_rsA_cast_eq_aa]

/-- `κ_s(σ) ≤ 0` for `s ≥ 0`, `t ≤ 0`. -/
theorem rsKappa_nonpos {q n : ℕ} (hq : q ≠ 0) {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ 0)
    (σ : Fin n → Fin q) : rsKappa q n s t σ ≤ 0 := by
  rw [rsKappa_eq_aa]
  have h := sum_aa_nonneg hq σ
  have h1 : t * ∑ u, ∑ v, aa q (σ u) (σ v) ≤ 0 := by nlinarith
  have h2 : 0 ≤ s / (2 * n) := by positivity
  nlinarith

/-- For `u ≠ v`, `∑_σ A_{σ_u σ_v} = 0` (the rows of `A` sum to zero). -/
theorem sum_sigma_rsA_of_ne {n q : ℕ} {u v : Fin n} (h : u ≠ v) :
    ∑ σ : Fin n → Fin q, ((rsA q (σ u) (σ v) : ℤ) : ℝ) = 0 := by
  rw [← (Equiv.funSplitAt v (Fin q)).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.funSplitAt_symm_apply, dif_pos, dif_neg h]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun σ' _ => rs_sum_rsA _ _

/-- `∑_σ ∑_{u,v} A_{σ_u σ_v} = q^n · n (q-1)`. -/
theorem sum_sigma_sum_rsA {n q : ℕ} :
    ∑ σ : Fin n → Fin q, ∑ u, ∑ v, ((rsA q (σ u) (σ v) : ℤ) : ℝ) =
      (q : ℝ) ^ n * (n * ((q : ℝ) - 1)) := by
  rw [Finset.sum_comm]
  have hu : ∀ u : Fin n, ∑ σ : Fin n → Fin q, ∑ v, ((rsA q (σ u) (σ v) : ℤ) : ℝ) =
      (q : ℝ) ^ n * ((q : ℝ) - 1) := by
    intro u
    rw [Finset.sum_comm, Finset.sum_eq_single u]
    · simp [rsA]
      ring
    · intro v _ hv
      exact sum_sigma_rsA_of_ne (Ne.symm hv)
    · simp
  rw [Finset.sum_congr rfl fun u _ => hu u]
  simp
  ring

/-- **Jensen.** `E_σ e^{κ_s(σ)} ≥ e^{E_σ κ_s(σ)} ≥ e^{-s/2}` for `t ≥ -1/(q-1)`, `s ≥ 0`
(any `n`; for `n = 0` both `κ_s` and its average vanish). -/
theorem avg_exp_kappa_ge {n q : ℕ} (hq : 2 ≤ q) {s t : ℝ} (hs : 0 ≤ s)
    (ht0 : -1 / ((q : ℝ) - 1) ≤ t) :
    Real.exp (-(s / 2)) ≤
      ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q, Real.exp (rsKappa q n s t σ) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hQ : (0 : ℝ) < (q : ℝ) ^ n := pow_pos (by linarith) n
  set m := ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q, rsKappa q n s t σ with hm
  have hmge : -(s / 2) ≤ m := by
    rw [hm]
    simp only [rsKappa]
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_sigma_sum_rsA]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [CharP.cast_eq_zero, mul_zero, zero_mul, mul_zero]
      linarith
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have htq : -1 ≤ t * ((q : ℝ) - 1) := by
        rw [div_le_iff₀ hq1] at ht0
        linarith
      have e : ((q : ℝ) ^ n)⁻¹ * (s / (2 * n) * (t * ((q : ℝ) ^ n * (n * ((q : ℝ) - 1))))) =
          s * (t * ((q : ℝ) - 1)) / 2 := by
        field_simp
      rw [e]
      nlinarith
  have hjensen : Real.exp m ≤
      ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q, Real.exp (rsKappa q n s t σ) := by
    have hpt : ∀ σ : Fin n → Fin q,
        Real.exp m * (1 + (rsKappa q n s t σ - m)) ≤ Real.exp (rsKappa q n s t σ) := by
      intro σ
      have := Real.add_one_le_exp (rsKappa q n s t σ - m)
      calc Real.exp m * (1 + (rsKappa q n s t σ - m))
          ≤ Real.exp m * Real.exp (rsKappa q n s t σ - m) :=
            mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
        _ = Real.exp (rsKappa q n s t σ) := by rw [← Real.exp_add]; ring_nf
    have hsum := Finset.sum_le_sum fun σ (_ : σ ∈ Finset.univ) => hpt σ
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at hsum
    have hm' : ∑ σ : Fin n → Fin q, rsKappa q n s t σ = (q : ℝ) ^ n * m := by
      rw [hm]
      field_simp
    push_cast at hsum
    rw [hm'] at hsum
    rw [le_inv_mul_iff₀ hQ]
    nlinarith [Real.exp_pos m]
  exact (Real.exp_le_exp.2 hmge).trans hjensen

/-- `E_σ e^{κ_s(σ)} 1_𝒜(σ) ≤ |𝒜|/q^n` for `t ≤ 0` (since `κ_s ≤ 0`). -/
theorem avg_exp_kappa_le {n q : ℕ} (hq : q ≠ 0) {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ 0)
    (A : Finset (Fin n → Fin q)) :
    ((q : ℝ) ^ n)⁻¹ * ∑ σ ∈ A, Real.exp (rsKappa q n s t σ) ≤ (A.card : ℝ) / (q : ℝ) ^ n := by
  rw [div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ∑ σ ∈ A, Real.exp (rsKappa q n s t σ) ≤ ∑ _σ ∈ A, (1 : ℝ) :=
        Finset.sum_le_sum fun σ _ => Real.exp_le_one_iff.2 (rsKappa_nonpos hq hs ht σ)
    _ = A.card := by simp

/-- **`eq:rs-one-tilt` with `Φ = 1`.** `E_{𝖯_s} w_{G,x}(σ) = e^{κ_s(σ)}` at a real anchor. -/
theorem hasSum_rsW {q n : ℕ} (hq : 3 ≤ q) {s x : ℝ} (hs : 0 ≤ s) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (σ : Fin n → Fin q) :
    HasSum (fun N => poisPi (rsMean n s) N * rsW q (tRe q x) N σ)
      (Real.exp (rsKappa q n s (tRe q x) σ)) := by
  have hm : ∀ e, 0 ≤ cpMean (fun a b => s * rsM q (tRe q x) a b) σ e := fun e =>
    div_nonneg (mul_nonneg hs (hx0.trans (rs_rsM_mem hq hx0 hx1 _ _).1)) (by positivity)
  have h := (rs_hasSum_poisPi hm).mul_left (Real.exp (rsKappa q n s (tRe q x) σ))
  rw [mul_one] at h
  exact h.congr_fun fun N => rs_one_tilt_pt s (tRe q x) σ N

/-- `E_{𝖯_s}[q^{-n} ∑_{σ ∈ 𝒜} w_{G,x}(σ)] = q^{-n} ∑_{σ ∈ 𝒜} e^{κ_s(σ)}`, as a `HasSum`. -/
theorem hasSum_partial {q n : ℕ} (hq : 3 ≤ q) {s x : ℝ} (hs : 0 ≤ s) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) (A : Finset (Fin n → Fin q)) :
    HasSum (fun N => poisPi (rsMean n s) N *
        (((q : ℝ) ^ n)⁻¹ * ∑ σ ∈ A, rsW q (tRe q x) N σ))
      (((q : ℝ) ^ n)⁻¹ * ∑ σ ∈ A, Real.exp (rsKappa q n s (tRe q x) σ)) := by
  have h := (hasSum_sum (s := A) fun σ _ => hasSum_rsW hq hs hx0 hx1 σ).mul_left
    (((q : ℝ) ^ n)⁻¹)
  refine h.congr_fun fun N => ?_
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

end RSTiltAux

open RSTiltAux

/-- **`eq:rs-first-moment`.** At a real anchor `x ∈ [0,1]` (`q ≥ 3`, `s ≥ 0`, any `n`),
`E_{𝖯_s} F_G(x) = E_σ e^{κ_s(σ)} ∈ [e^{-s/2}, 1]`; in particular `F_G(x)` is `𝖯_s`-summable. -/
theorem rs_poisson_first_moment {q n : ℕ} (hq : 3 ≤ q) {s x : ℝ} (hs : 0 ≤ s) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) :
    Summable (fun N => poisPi (rsMean n s) N * rsF q (tRe q x) N) ∧
      Real.exp (-(s / 2)) ≤ rsExp n s (rsF q (tRe q x)) ∧
      rsExp n s (rsF q (tRe q x)) ≤ 1 := by
  have H := hasSum_partial (n := n) hq hs hx0 hx1 Finset.univ
  have hF : (fun N => poisPi (rsMean n s) N * rsF q (tRe q x) N) =
      fun N => poisPi (rsMean n s) N *
        (((q : ℝ) ^ n)⁻¹ * ∑ σ ∈ Finset.univ, rsW q (tRe q x) N σ) := by
    funext N
    rfl
  have hE : rsExp n s (rsF q (tRe q x)) =
      ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q, Real.exp (rsKappa q n s (tRe q x) σ) := by
    unfold rsExp poisPiExp
    rw [hF, H.tsum_eq]
  have hq0 : q ≠ 0 := by omega
  have hq2 : 2 ≤ q := by omega
  refine ⟨hF ▸ H.summable, ?_, ?_⟩
  · rw [hE]
    exact avg_exp_kappa_ge hq2 hs (rs_tRe_ge hq2 hx0)
  · rw [hE]
    have h := avg_exp_kappa_le hq0 hs (rs_tRe_nonpos hq2 hx0 hx1)
      (Finset.univ : Finset (Fin n → Fin q))
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at h
    have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq0
    rwa [div_self (pow_ne_zero n hqR)] at h

/-- **`eq:rs-marginal`.** For every set `𝒜` of colourings, at a real anchor `x ∈ [0,1]`, the sum
defining `E_{𝖯_s}[q^{-n} ∑_{σ ∈ 𝒜} w_{G,x}(σ)] = E_{𝖯_s}[F Pr_{μ_G}[𝒜]]` converges, and this
expectation equals `E_σ[e^{κ_s(σ)} 1_𝒜(σ)] ≤ |𝒜|/q^n`. -/
theorem rs_marginal {q n : ℕ} (hq : 3 ≤ q) {s x : ℝ} (hs : 0 ≤ s) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (A : Finset (Fin n → Fin q)) :
    Summable (fun N => poisPi (rsMean n s) N *
        (((q : ℝ) ^ n)⁻¹ * ∑ σ ∈ A, rsW q (tRe q x) N σ)) ∧
      rsExp n s (fun N => ((q : ℝ) ^ n)⁻¹ * ∑ σ ∈ A, rsW q (tRe q x) N σ) ≤
        (A.card : ℝ) / (q : ℝ) ^ n := by
  have H := hasSum_partial hq hs hx0 hx1 A
  refine ⟨H.summable, ?_⟩
  unfold rsExp poisPiExp
  rw [H.tsum_eq]
  exact avg_exp_kappa_le (by omega) hs (rs_tRe_nonpos (show 2 ≤ q by omega) hx0 hx1) A

end

end ERZeroFreeness
