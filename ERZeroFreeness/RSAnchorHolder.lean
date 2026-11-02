/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSAnchorFree
import ERZeroFreeness.RSAnchorTest

/-!
# Appendix C, Lemma C.7, Step 3: correlated pairs (`eq:rs-J-id`)

At a real anchor `x ∈ (0,1]` (`t = t(x)`, `ℓ = log(e/x)`, `F = F_G(x)`, `μ_G(σ) = q^{-n} w_G(σ)/F`),
with `𝒞 = {(σ,τ) : ‖R_{σ,τ} - αβᵀ‖_F² ≥ η²/4}`, `ψ_x = Δ t² q² η²/16`,
`C'_⋆ = 1 + (3/2)(d+Δ) + (9/4)(d+Δ)²`, `C_t = 9Δ/2` (the constant of `rs_test_upper`; the paper
has `9eΔ/4`) and
`Ξ = E_{𝖯_d}[F ∑_{(σ,τ) ∈ 𝒞} μ_G(σ) μ_G(τ) e^{κ_Δ(σ)}]
   = E_{𝖯_d}[q^{-2n} ∑_{𝒞} w_G(σ) w_G(τ) e^{κ_Δ(σ)} / F]`:

* `rs_J_id` (**`eq:rs-J-id`**, non-asymptotic): for `0 ≤ λ ≤ 1/3`, `0 < h`, `hℓ ≤ 1`, `n ≥ 1`
  and `λ' = λh/(1+h)`,
  `e^{2λ'ψ_x n} Ξ ≤ exp{(h/(1+h)) [f̄_n + C'_⋆ h ℓ² n + C_t λ² n]}`, where `f̄_n` is `rsFbar` at
  density `d + Δ`.

## Proof

This is Step 3 of the paper's proof of Lemma C.7, except that Hölder's inequality and the
power-mean Jensen inequality are replaced by one pointwise Young inequality (step 3 below).
Let `G ∼ 𝖯_d`, `G' ∼ 𝖯_Δ` be independent; `G + G' ∼ 𝖯_{d+Δ}` (`rs_hasSum_poisPi_superpose`,
`rsMean n d + rsMean n Δ = rsMean n (d+Δ)`) and `w_{G+G'} = w_G w_{G'}` (`rs_rsW_add`).
1. For `(σ,τ) ∈ 𝒞`: `rs_one_tilt` (density `Δ`, `Φ = e^{λ' S_τ}`) and `rs_test_lower` (with
   `λ' ≥ 0`, `‖R - αβᵀ‖_F² ≥ η²/4`) give `e^{κ_Δ(σ) + 2λ'ψ_x n} ≤ E_{G'}[w_{G'}(σ) e^{λ' S_τ(G')}]`.
2. Multiply by `q^{-2n} w_G(σ) w_G(τ)/F_G`, add the (nonnegative) pairs outside `𝒞`, and use
   `q^{-n} ∑_σ w_G(σ) w_{G'}(σ) = F_{G+G'}` (`hld_pair_identity`, `hld_rsF_add`):
   `e^{2λ'ψ_x n} Ξ ≤ E_{G,G'}[F_{G+G'} X]` with `X = ∑_τ μ_G(τ) e^{λ' S_τ(G')}`.
3. Young's inequality with exponents `1+h`, `(1+h)/h` and a free parameter `r` (`hld_young_exp`)
   gives, for every `τ`,
   `F_{G+G'} e^{λ' S_τ} ≤ e^{r(1+h)} F_{G+G'}^{1+h}/(1+h) + e^{λ S_τ - r(1+h)/h}/((1+h)/h)`;
   average against `μ_G(τ)` (`∑_τ μ_G(τ) = 1`).
4. `rs_test_upper` gives `E_{G'} e^{λ S_τ(G')} ≤ e^b` for every `τ`, with `b = C_t λ² n`.
5. `E F_{G+G'}^{1+h} = E_{𝖯_{d+Δ}} F^{1+h} ≤ e^a` with `a = h f̄_n + C'_⋆ h² ℓ² n` (`rs_frac`).
6. With `c = (a + h b)/(1+h)` and `r = (c - a)/(1+h)`, the two resulting terms are `e^c/(1+h)`
   and `e^c h/(1+h)`, which add up to `e^c`, the right-hand side of `eq:rs-J-id`.

## Implementation notes

Auxiliary lemmas are in `RSAnchorHolderAux`.  The `G'`-expectation is kept inside the sum over
the base graph `G` (`hld_fiber_bound` is steps 1–4 for a fixed `G`), and superposition is used in
fibred form (`HasSum.prod_fiberwise`).  Summability comes from `F ≤ (3/2)^m`
(`hld_summable_rpow_shift`) and from the one-tilt plus the Poisson generating function
(`hld_summable_tilt`).  If the `Ξ` family is not summable, its `tsum` is `0` and the bound is
trivial.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

namespace RSAnchorHolderAux

theorem hld_rsW_nonneg {q n : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (N : RSGraph n) (σ : Fin n → Fin q) : 0 ≤ rsW q (tRe q x) N σ :=
  Finset.prod_nonneg fun _ _ => pow_nonneg (hx0.trans (rs_rsM_mem hq hx0 hx1 _ _).1) _

theorem hld_rsF_pos {q n : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (N : RSGraph n) : 0 < rsF q (tRe q x) N :=
  lt_of_lt_of_le (pow_pos hx0 _) (rs_rsF_bounds hq hx0 hx1 N).1

theorem hld_rsMean_nonneg {n : ℕ} {s : ℝ} (hs : 0 ≤ s) (i : Fin n × Fin n) :
    0 ≤ rsMean n s i := by
  unfold rsMean; positivity

/-- `N' ↦ poisPi lamv N' · F(N₀ + N')^P` is summable for `P ≥ 0` (`F ≤ (3/2)^m`). -/
theorem hld_summable_rpow_shift {q n : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    {lamv : Fin n × Fin n → ℝ} (hlam : ∀ i, 0 ≤ lamv i) {P : ℝ} (hP : 0 ≤ P)
    (N₀ : RSGraph n) :
    Summable (fun N' : RSGraph n => poisPi lamv N' * rsF q (tRe q x) (N₀ + N') ^ P) := by
  refine rs_summable_poisPi_of_abs_le hlam (A := ((3 / 2 : ℝ) ^ P) ^ rsEdges N₀)
    (c := (3 / 2 : ℝ) ^ P) (by positivity) fun N' => ?_
  have hb := rs_rsF_bounds hq hx0 hx1 (N₀ + N')
  have hF0 : 0 ≤ rsF q (tRe q x) (N₀ + N') := (pow_nonneg hx0.le _).trans hb.1
  rw [abs_of_nonneg (Real.rpow_nonneg hF0 _)]
  have hedge : rsEdges (N₀ + N') = rsEdges N₀ + ∑ i, N' i := by
    simp only [rsEdges, Pi.add_apply, Finset.sum_add_distrib]
  calc rsF q (tRe q x) (N₀ + N') ^ P ≤ ((3 / 2 : ℝ) ^ rsEdges (N₀ + N')) ^ P :=
        Real.rpow_le_rpow hF0 hb.2 hP
    _ = ((3 / 2 : ℝ) ^ P) ^ rsEdges (N₀ + N') := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
          Real.rpow_mul (by norm_num), Real.rpow_natCast]
    _ = ((3 / 2 : ℝ) ^ P) ^ rsEdges N₀ * ((3 / 2 : ℝ) ^ P) ^ (∑ i, N' i) := by
        rw [hedge, pow_add]

/-- Exponential generating function of a product Poisson law:
`E exp(∑_i N_i y_i) = exp(∑_i lam_i (e^{y_i} - 1))`. -/
theorem hld_hasSum_exp_lin {ι : Type*} [Fintype ι] {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
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

/-- `c S_τ(N) = ∑_{(u,v)} N_{uv} (c t q ⟨e_{τ_u} - β, e_{τ_v} - β⟩)`. -/
theorem hld_mul_testStat {n q : ℕ} (t c : ℝ) (τ : Fin n → Fin q) (N : RSGraph n) :
    c * rsTestStat q t τ N =
      ∑ uv : Fin n × Fin n, (N uv : ℝ) * (c * t * q * rsTestCoef τ (τ uv.1) (τ uv.2)) := by
  unfold rsTestStat
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun uv _ => ?_
  ring

/-- `N' ↦ P_Δ(N') w_{N'}(σ) e^{c S_τ(N')}` is summable (one-tilt and the Poisson MGF). -/
theorem hld_summable_tilt {q n : ℕ} (hq : 3 ≤ q) {x Δ : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hΔ : 0 ≤ Δ) (σ τ : Fin n → Fin q) (c : ℝ) :
    Summable (fun N' : RSGraph n => poisPi (rsMean n Δ) N' *
      (rsW q (tRe q x) N' σ * Real.exp (c * rsTestStat q (tRe q x) τ N'))) := by
  have hmean : ∀ uv, 0 ≤ cpMean (fun a b => Δ * rsM q (tRe q x) a b) σ uv := by
    intro uv
    simp only [cpMean]
    have h1 := (rs_rsM_mem hq hx0 hx1 (σ uv.1) (σ uv.2)).1
    have h2 : 0 ≤ rsM q (tRe q x) (σ uv.1) (σ uv.2) := le_trans hx0 h1
    positivity
  have H := hld_hasSum_exp_lin hmean
    (fun uv => c * tRe q x * q * rsTestCoef τ (τ uv.1) (τ uv.2))
  have H2 := H.summable.mul_left (Real.exp (rsKappa q n Δ (tRe q x) σ))
  refine H2.congr fun N' => ?_
  have e1 := rs_one_tilt_pt (q := q) Δ (tRe q x) σ N'
  have e2 := hld_mul_testStat (tRe q x) c τ N'
  rw [e2]
  calc Real.exp (rsKappa q n Δ (tRe q x) σ) *
        (poisPi (cpMean (fun a b => Δ * rsM q (tRe q x) a b) σ) N' *
          Real.exp (∑ uv, (N' uv : ℝ) * (c * tRe q x * q * rsTestCoef τ (τ uv.1) (τ uv.2))))
      = (Real.exp (rsKappa q n Δ (tRe q x) σ) *
          poisPi (cpMean (fun a b => Δ * rsM q (tRe q x) a b) σ) N') *
          Real.exp (∑ uv, (N' uv : ℝ) *
            (c * tRe q x * q * rsTestCoef τ (τ uv.1) (τ uv.2))) := by
        ring
    _ = poisPi (rsMean n Δ) N' * (rsW q (tRe q x) N' σ *
          Real.exp (∑ uv, (N' uv : ℝ) *
            (c * tRe q x * q * rsTestCoef τ (τ uv.1) (τ uv.2)))) := by
        rw [← e1]; ring

/-- Young's inequality with a free parameter `r`, exponents `1+h` and `(1+h)/h`:
`F e^{λ' S} ≤ e^{r(1+h)} F^{1+h}/(1+h) + e^{λS - r(1+h)/h}/((1+h)/h)`, `λ' = λh/(1+h)`. -/
theorem hld_young_exp {F h lam r S : ℝ} (hF : 0 ≤ F) (hh : 0 < h) :
    F * Real.exp (lam * h / (1 + h) * S) ≤
      Real.exp (r * (1 + h)) * F ^ (1 + h) / (1 + h) +
        Real.exp (lam * S - r * ((1 + h) / h)) / ((1 + h) / h) := by
  have hpq : (1 + h).HolderConjugate ((1 + h) / h) := by
    rw [Real.holderConjugate_iff]
    refine ⟨by linarith, ?_⟩
    field_simp
  have Y := Real.young_inequality_of_nonneg (mul_nonneg (Real.exp_pos r).le hF)
    (Real.exp_pos (lam * h / (1 + h) * S - r)).le hpq
  have e1 : Real.exp r * F * Real.exp (lam * h / (1 + h) * S - r) =
      F * Real.exp (lam * h / (1 + h) * S) := by
    rw [Real.exp_sub]
    field_simp
  have e2 : (Real.exp r * F) ^ (1 + h) = Real.exp (r * (1 + h)) * F ^ (1 + h) := by
    rw [Real.mul_rpow (Real.exp_pos r).le hF, ← Real.exp_mul]
  have e3 : (Real.exp (lam * h / (1 + h) * S - r)) ^ ((1 + h) / h) =
      Real.exp (lam * S - r * ((1 + h) / h)) := by
    rw [← Real.exp_mul]
    congr 1
    field_simp
  rw [e1, e2, e3] at Y
  exact Y

/-- Step 1 of the proof: for `(σ,τ) ∈ 𝒞` and `λ' ≥ 0`,
`e^{κ_Δ(σ)} e^{2λ'ψ_x n} ≤ E_{𝖯_Δ}[w_{G'}(σ) e^{λ' S_τ(G')}]`. -/
theorem hld_tilt_lower {q n : ℕ} (hq : 3 ≤ q) {x Δ η lam' : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hΔ : 0 ≤ Δ) (hn : 0 < n) (hl : 0 ≤ lam') (σ τ : Fin n → Fin q)
    (hστ : η ^ 2 / 4 ≤ rsCorrDev σ τ) :
    Real.exp (rsKappa q n Δ (tRe q x) σ) *
        Real.exp (2 * lam' * (Δ * tRe q x ^ 2 * (q : ℝ) ^ 2 * η ^ 2 / 16) * n) ≤
      rsExp n Δ (fun N' => rsW q (tRe q x) N' σ *
        Real.exp (lam' * rsTestStat q (tRe q x) τ N')) := by
  rw [rs_one_tilt]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  refine le_trans ?_ (rs_test_lower hq hx0 hx1 hΔ hn σ τ lam')
  rw [Real.exp_le_exp]
  have hK : 0 ≤ Δ * n * tRe q x ^ 2 * (q : ℝ) ^ 2 / 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hστ hK
  calc 2 * lam' * (Δ * tRe q x ^ 2 * (q : ℝ) ^ 2 * η ^ 2 / 16) * n
      = lam' * (Δ * n * tRe q x ^ 2 * (q : ℝ) ^ 2 / 2 * (η ^ 2 / 4)) := by ring
    _ ≤ lam' * (Δ * n * tRe q x ^ 2 * (q : ℝ) ^ 2 / 2 * rsCorrDev σ τ) :=
        mul_le_mul_of_nonneg_left h1 hl

/-- The regrouping of step 2, before `q^{-n} ∑_σ w_G(σ) w_{G'}(σ) = F_{G+G'}` is applied:
`∑_{σ,τ} q^{-2n} (w(σ) w(τ)/F) p w'(σ) e(τ)
  = p ∑_τ (q^{-n} w(τ)/F) (q^{-n} ∑_σ w(σ) w'(σ)) e(τ)`. -/
theorem hld_pair_identity {ι : Type*} [Fintype ι] (Qi F p : ℝ) (w w' e : ι → ℝ) :
    ∑ st : ι × ι, Qi ^ 2 * (w st.1 * w st.2 / F) * (p * (w' st.1 * e st.2)) =
      p * ∑ τ, Qi * w τ / F * ((Qi * ∑ σ, w σ * w' σ) * e τ) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

/-- `F_{G+G'} = q^{-n} ∑_σ w_G(σ) w_{G'}(σ)`. -/
theorem hld_rsF_add {q n : ℕ} (t : ℝ) (N N' : RSGraph n) :
    rsF q t (N + N') =
      ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q, rsW q t N σ * rsW q t N' σ := by
  simp only [rsF, rs_rsW_add]

/-- `∑_τ μ_G(τ) = 1`. -/
theorem hld_sum_mu {q n : ℕ} (t : ℝ) (N : RSGraph n) (hF : rsF q t N ≠ 0) :
    ∑ τ : Fin n → Fin q, ((q : ℝ) ^ n)⁻¹ * rsW q t N τ / rsF q t N = 1 := by
  rw [← Finset.sum_div, ← Finset.mul_sum]
  exact div_self hF

/-- Steps 1–4 of the proof for a fixed base graph `G = N`: with `λ' = λh/(1+h)`, any `r` and
`F_s(N) = E_{G'∼𝖯_Δ} F_{N+G'}^{1+h}`,
`e^{2λ'ψ_x n} q^{-2n} ∑_{𝒞} w(σ)w(τ)e^{κ_Δ(σ)}/F ≤
  e^{r(1+h)}/(1+h) F_s(N) + e^{-r(1+h)/h}/((1+h)/h) e^{C_t λ² n}`. -/
theorem hld_fiber_bound {q : ℕ} (hq : 3 ≤ q) {x Δ η lam h r : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hΔ : 0 ≤ Δ) {n : ℕ} (hn : 0 < n) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1 / 3) (hh : 0 < h)
    (N : RSGraph n) :
    Real.exp (2 * (lam * h / (1 + h)) * (Δ * tRe q x ^ 2 * (q : ℝ) ^ 2 * η ^ 2 / 16) * n) *
        ((((q : ℝ) ^ n)⁻¹) ^ 2 *
          ∑ st ∈ Finset.univ.filter
              (fun st : (Fin n → Fin q) × (Fin n → Fin q) => η ^ 2 / 4 ≤ rsCorrDev st.1 st.2),
            rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 *
              Real.exp (rsKappa q n Δ (tRe q x) st.1) / rsF q (tRe q x) N) ≤
      Real.exp (r * (1 + h)) / (1 + h) *
          ∑' N' : RSGraph n, poisPi (rsMean n Δ) N' * rsF q (tRe q x) (N + N') ^ (1 + h) +
        Real.exp (-(r * ((1 + h) / h))) / ((1 + h) / h) *
          Real.exp (9 / 2 * Δ * lam ^ 2 * n) := by
  have hlam' : 0 ≤ lam * h / (1 + h) := by positivity
  have hFpos := hld_rsF_pos hq hx0 hx1 N
  have hmΔ : ∀ i, 0 ≤ rsMean n Δ i := hld_rsMean_nonneg hΔ
  have hQi0 : (0 : ℝ) ≤ ((q : ℝ) ^ n)⁻¹ := by positivity
  have hw0 : ∀ (M : RSGraph n) (σ : Fin n → Fin q), 0 ≤ rsW q (tRe q x) M σ :=
    fun M σ => hld_rsW_nonneg hq hx0.le hx1 M σ
  have hc0 : ∀ st : (Fin n → Fin q) × (Fin n → Fin q), 0 ≤ ((q : ℝ) ^ n)⁻¹ ^ 2 *
      (rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 / rsF q (tRe q x) N) := fun st => by
    have := hw0 N st.1; have := hw0 N st.2; positivity
  have hTs : ∀ st : (Fin n → Fin q) × (Fin n → Fin q),
      HasSum (fun N' => poisPi (rsMean n Δ) N' * (rsW q (tRe q x) N' st.1 *
        Real.exp (lam * h / (1 + h) * rsTestStat q (tRe q x) st.2 N')))
      (rsExp n Δ (fun N' => rsW q (tRe q x) N' st.1 *
        Real.exp (lam * h / (1 + h) * rsTestStat q (tRe q x) st.2 N'))) :=
    fun st => (hld_summable_tilt hq hx0.le hx1 hΔ st.1 st.2 _).hasSum
  have hT0 : ∀ st : (Fin n → Fin q) × (Fin n → Fin q), 0 ≤ rsExp n Δ (fun N' =>
      rsW q (tRe q x) N' st.1 * Real.exp (lam * h / (1 + h) * rsTestStat q (tRe q x) st.2 N')) :=
    fun st => (hTs st).nonneg fun N' => mul_nonneg (rs_poisPi_nonneg hmΔ N')
      (mul_nonneg (hw0 N' st.1) (Real.exp_pos _).le)
  -- Steps 1–2: the tilt bound on `𝒞`, then all pairs.
  have step1 :
      Real.exp (2 * (lam * h / (1 + h)) * (Δ * tRe q x ^ 2 * (q : ℝ) ^ 2 * η ^ 2 / 16) * n) *
        ((((q : ℝ) ^ n)⁻¹) ^ 2 *
          ∑ st ∈ Finset.univ.filter
              (fun st : (Fin n → Fin q) × (Fin n → Fin q) => η ^ 2 / 4 ≤ rsCorrDev st.1 st.2),
            rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 *
              Real.exp (rsKappa q n Δ (tRe q x) st.1) / rsF q (tRe q x) N) ≤
      ∑ st : (Fin n → Fin q) × (Fin n → Fin q), ((q : ℝ) ^ n)⁻¹ ^ 2 *
        (rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 / rsF q (tRe q x) N) *
        rsExp n Δ (fun N' => rsW q (tRe q x) N' st.1 *
          Real.exp (lam * h / (1 + h) * rsTestStat q (tRe q x) st.2 N')) := by
    calc _ = ∑ st ∈ Finset.univ.filter
              (fun st : (Fin n → Fin q) × (Fin n → Fin q) => η ^ 2 / 4 ≤ rsCorrDev st.1 st.2),
            ((q : ℝ) ^ n)⁻¹ ^ 2 *
              (rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 / rsF q (tRe q x) N) *
              (Real.exp (rsKappa q n Δ (tRe q x) st.1) * Real.exp (2 * (lam * h / (1 + h)) *
                (Δ * tRe q x ^ 2 * (q : ℝ) ^ 2 * η ^ 2 / 16) * n)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun st _ => ?_
          ring
      _ ≤ ∑ st ∈ Finset.univ.filter
              (fun st : (Fin n → Fin q) × (Fin n → Fin q) => η ^ 2 / 4 ≤ rsCorrDev st.1 st.2),
            ((q : ℝ) ^ n)⁻¹ ^ 2 *
              (rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 / rsF q (tRe q x) N) *
              rsExp n Δ (fun N' => rsW q (tRe q x) N' st.1 *
                Real.exp (lam * h / (1 + h) * rsTestStat q (tRe q x) st.2 N')) := by
          refine Finset.sum_le_sum fun st hst => mul_le_mul_of_nonneg_left ?_ (hc0 st)
          exact hld_tilt_lower hq hx0.le hx1 hΔ hn hlam' st.1 st.2 (Finset.mem_filter.mp hst).2
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun st _ _ => mul_nonneg (hc0 st) (hT0 st)
  -- Step 2: the pair sum as an expectation over `G'`.
  have hU := hasSum_sum (s := Finset.univ) fun st _ =>
    (hTs st).mul_left (((q : ℝ) ^ n)⁻¹ ^ 2 *
      (rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 / rsF q (tRe q x) N))
  -- Steps 3–4: the comparison function given by Young's inequality.
  have hFs := (hld_summable_rpow_shift hq hx0 hx1 hmΔ (P := 1 + h) (by linarith) N).hasSum
  have hEs : ∀ τ : Fin n → Fin q, HasSum
      (fun N' => poisPi (rsMean n Δ) N' * Real.exp (lam * rsTestStat q (tRe q x) τ N'))
      (rsExp n Δ (fun N' => Real.exp (lam * rsTestStat q (tRe q x) τ N'))) :=
    fun τ => (rs_test_upper hq hx0.le hx1 hΔ hn τ hl0 hl1).1.hasSum
  have hV := (hFs.mul_left (Real.exp (r * (1 + h)) / (1 + h))).add
    ((hasSum_sum (s := Finset.univ) fun τ _ => (hEs τ).mul_left
      (((q : ℝ) ^ n)⁻¹ * rsW q (tRe q x) N τ / rsF q (tRe q x) N)).mul_left
      (Real.exp (-(r * ((1 + h) / h))) / ((1 + h) / h)))
  have hμ0 : ∀ τ : Fin n → Fin q,
      0 ≤ ((q : ℝ) ^ n)⁻¹ * rsW q (tRe q x) N τ / rsF q (tRe q x) N :=
    fun τ => by have := hw0 N τ; positivity
  have hμ1 := hld_sum_mu (q := q) (tRe q x) N hFpos.ne'
  have hUV := hasSum_le (fun N' => ?_) hU hV
  · refine step1.trans (hUV.trans ?_)
    refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (by positivity))
    calc ∑ τ : Fin n → Fin q, ((q : ℝ) ^ n)⁻¹ * rsW q (tRe q x) N τ / rsF q (tRe q x) N *
          rsExp n Δ (fun N' => Real.exp (lam * rsTestStat q (tRe q x) τ N'))
        ≤ ∑ τ : Fin n → Fin q, ((q : ℝ) ^ n)⁻¹ * rsW q (tRe q x) N τ / rsF q (tRe q x) N *
          Real.exp (9 / 2 * Δ * lam ^ 2 * n) :=
          Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left
            (rs_test_upper hq hx0.le hx1 hΔ hn τ hl0 hl1).2 (hμ0 τ)
      _ = Real.exp (9 / 2 * Δ * lam ^ 2 * n) := by rw [← Finset.sum_mul, hμ1, one_mul]
  · -- pointwise comparison (Young's inequality for each `τ`)
    have hid := hld_pair_identity (((q : ℝ) ^ n)⁻¹) (rsF q (tRe q x) N)
      (poisPi (rsMean n Δ) N')
      (fun σ => rsW q (tRe q x) N σ) (fun σ => rsW q (tRe q x) N' σ)
      (fun τ => Real.exp (lam * h / (1 + h) * rsTestStat q (tRe q x) τ N'))
    beta_reduce at hid
    rw [← hld_rsF_add] at hid
    have hF'0 : 0 ≤ rsF q (tRe q x) (N + N') := (hld_rsF_pos hq hx0 hx1 (N + N')).le
    rw [hid]
    calc poisPi (rsMean n Δ) N' * ∑ τ : Fin n → Fin q,
          ((q : ℝ) ^ n)⁻¹ * rsW q (tRe q x) N τ / rsF q (tRe q x) N *
            (rsF q (tRe q x) (N + N') *
              Real.exp (lam * h / (1 + h) * rsTestStat q (tRe q x) τ N'))
        ≤ poisPi (rsMean n Δ) N' * ∑ τ : Fin n → Fin q,
          ((q : ℝ) ^ n)⁻¹ * rsW q (tRe q x) N τ / rsF q (tRe q x) N *
            (Real.exp (r * (1 + h)) * rsF q (tRe q x) (N + N') ^ (1 + h) / (1 + h) +
              Real.exp (lam * rsTestStat q (tRe q x) τ N' - r * ((1 + h) / h)) /
                ((1 + h) / h)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun τ _ =>
            mul_le_mul_of_nonneg_left (hld_young_exp hF'0 hh) (hμ0 τ))
            (rs_poisPi_nonneg hmΔ N')
      _ = ∑ τ : Fin n → Fin q,
          (Real.exp (r * (1 + h)) / (1 + h) *
              (poisPi (rsMean n Δ) N' * rsF q (tRe q x) (N + N') ^ (1 + h)) *
              (((q : ℝ) ^ n)⁻¹ * rsW q (tRe q x) N τ / rsF q (tRe q x) N) +
            Real.exp (-(r * ((1 + h) / h))) / ((1 + h) / h) *
              (((q : ℝ) ^ n)⁻¹ * rsW q (tRe q x) N τ / rsF q (tRe q x) N *
                (poisPi (rsMean n Δ) N' * Real.exp (lam * rsTestStat q (tRe q x) τ N')))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [Real.exp_sub, Real.exp_neg]
          ring
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hμ1, mul_one]

end RSAnchorHolderAux

open RSAnchorHolderAux

/-- **`eq:rs-J-id`.**  For `0 ≤ λ ≤ 1/3`, `0 < h`, `hℓ ≤ 1`, `n ≥ 1` and `λ' = λh/(1+h)`,
`e^{2λ'ψ_x n} Ξ ≤ exp{(h/(1+h)) [f̄_n + C'_⋆ h ℓ² n + C_t λ² n]}`, with `f̄_n` at density `d + Δ`
(notation as in the module docstring). -/
theorem rs_J_id {q : ℕ} (hq : 3 ≤ q) {x d Δ η lam h : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hd : 0 ≤ d) (hΔ : 0 ≤ Δ) {n : ℕ} (hn : 0 < n) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1 / 3)
    (hh : 0 < h) (hhl : h * rsEll x ≤ 1) :
    Real.exp (2 * (lam * h / (1 + h)) * (Δ * tRe q x ^ 2 * (q : ℝ) ^ 2 * η ^ 2 / 16) * n) *
        rsExp n d (fun N => (((q : ℝ) ^ n)⁻¹) ^ 2 *
          ∑ st ∈ Finset.univ.filter
              (fun st : (Fin n → Fin q) × (Fin n → Fin q) => η ^ 2 / 4 ≤ rsCorrDev st.1 st.2),
            rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 *
              Real.exp (rsKappa q n Δ (tRe q x) st.1) / rsF q (tRe q x) N) ≤
      Real.exp (h / (1 + h) * (rsFbar q n (d + Δ) (tRe q x) +
        (1 + 3 / 2 * (d + Δ) + 9 / 4 * (d + Δ) ^ 2) * h * rsEll x ^ 2 * n +
        9 / 2 * Δ * lam ^ 2 * n)) := by
  have hmd : ∀ i, 0 ≤ rsMean n d i := hld_rsMean_nonneg hd
  have hmΔ : ∀ i, 0 ≤ rsMean n Δ i := hld_rsMean_nonneg hΔ
  have hP0 : (0 : ℝ) ≤ 1 + h := by linarith
  have hab : rsMean n d + rsMean n Δ = rsMean n (d + Δ) := by
    funext i
    simp only [Pi.add_apply, rsMean]
    ring
  -- Superposition: `E_{G,G'} F_{G+G'}^{1+h} = E_{𝖯_{d+Δ}} F^{1+h}`, in fibred form.
  have hsum : Summable fun M : RSGraph n =>
      poisPi (rsMean n d + rsMean n Δ) M * rsF q (tRe q x) M ^ (1 + h) := by
    rw [hab]
    have := hld_summable_rpow_shift hq hx0 hx1 (hld_rsMean_nonneg (n := n) (add_nonneg hd hΔ))
      hP0 (0 : RSGraph n)
    simp only [zero_add] at this
    exact this
  have hsup := rs_hasSum_poisPi_superpose hmd hmΔ
    (Φ := fun M : RSGraph n => rsF q (tRe q x) M ^ (1 + h))
    (fun M => Real.rpow_nonneg (hld_rsF_pos hq hx0 hx1 M).le _) hsum
  rw [hab] at hsup
  have hfib : HasSum (fun N : RSGraph n => poisPi (rsMean n d) N *
      ∑' N' : RSGraph n, poisPi (rsMean n Δ) N' * rsF q (tRe q x) (N + N') ^ (1 + h))
      (rsExp n (d + Δ) fun N => rsF q (tRe q x) N ^ (1 + h)) := by
    refine hsup.prod_fiberwise fun N => ?_
    refine ((hld_summable_rpow_shift hq hx0 hx1 hmΔ hP0 N).hasSum.mul_left
      (poisPi (rsMean n d) N)).congr_fun fun N' => ?_
    ring
  -- The exponents: `a` (from `rs_frac`), `b` (from `rs_test_upper`), the target `c`, and the
  -- Young parameter `r`.
  set a := h * rsFbar q n (d + Δ) (tRe q x) +
    (1 + 3 / 2 * (d + Δ) + 9 / 4 * (d + Δ) ^ 2) * h ^ 2 * rsEll x ^ 2 * n with ha
  set b := 9 / 2 * Δ * lam ^ 2 * n with hb
  set c := h / (1 + h) * (rsFbar q n (d + Δ) (tRe q x) +
    (1 + 3 / 2 * (d + Δ) + 9 / 4 * (d + Δ) ^ 2) * h * rsEll x ^ 2 * n + b) with hc
  set r := (c - a) / (1 + h) with hr
  have hfrac : rsExp n (d + Δ) (fun N => rsF q (tRe q x) N ^ (1 + h)) ≤ Real.exp a :=
    rs_frac hq hx0 hx1 (add_nonneg hd hΔ) hn hh hhl
  -- The comparison function `g(N) = A₁ F_s(N) + B₀ e^b` and its expectation, with
  -- `A₁ = e^{r(1+h)}/(1+h)`, `B₀ = e^{-r(1+h)/h}/((1+h)/h)` and `F_s` as in `hld_fiber_bound`.
  have hG := (hfib.mul_left (Real.exp (r * (1 + h)) / (1 + h))).add
    ((rs_hasSum_poisPi hmd).mul_left
      (Real.exp (-(r * ((1 + h) / h))) / ((1 + h) / h) * Real.exp b))
  have hfinal : Real.exp (r * (1 + h)) / (1 + h) *
        rsExp n (d + Δ) (fun N => rsF q (tRe q x) N ^ (1 + h)) +
      Real.exp (-(r * ((1 + h) / h))) / ((1 + h) / h) * Real.exp b * 1 ≤ Real.exp c := by
    have h1 : r * (1 + h) + a = c := by
      rw [hr]; field_simp; ring
    have h2 : -(r * ((1 + h) / h)) + b = c := by
      rw [hr, hc, ha]; field_simp; ring
    calc Real.exp (r * (1 + h)) / (1 + h) *
          rsExp n (d + Δ) (fun N => rsF q (tRe q x) N ^ (1 + h)) +
        Real.exp (-(r * ((1 + h) / h))) / ((1 + h) / h) * Real.exp b * 1
        ≤ Real.exp (r * (1 + h)) / (1 + h) * Real.exp a +
          Real.exp (-(r * ((1 + h) / h))) / ((1 + h) / h) * Real.exp b * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hfrac (by positivity)) le_rfl
      _ = Real.exp (r * (1 + h) + a) / (1 + h) +
          Real.exp (-(r * ((1 + h) / h)) + b) / ((1 + h) / h) := by
          rw [Real.exp_add (r * (1 + h)) a, Real.exp_add (-(r * ((1 + h) / h))) b]
          ring
      _ = Real.exp c := by
          rw [h1, h2]
          field_simp
  -- Summation over the base graph.
  unfold rsExp poisPiExp
  by_cases hs : Summable fun N : RSGraph n => poisPi (rsMean n d) N *
      ((((q : ℝ) ^ n)⁻¹) ^ 2 *
          ∑ st ∈ Finset.univ.filter
              (fun st : (Fin n → Fin q) × (Fin n → Fin q) => η ^ 2 / 4 ≤ rsCorrDev st.1 st.2),
            rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 *
              Real.exp (rsKappa q n Δ (tRe q x) st.1) / rsF q (tRe q x) N)
  · refine le_trans ?_ hfinal
    refine hasSum_le (fun N => ?_) (hs.hasSum.mul_left _) hG
    have hfb := hld_fiber_bound (η := η) (r := r) hq hx0 hx1 hΔ hn hl0 hl1 hh N
    rw [← hb] at hfb
    convert mul_le_mul_of_nonneg_left hfb (rs_poisPi_nonneg hmd N) using 1 <;> ring
  · rw [tsum_eq_zero_of_not_summable hs, mul_zero]
    exact (Real.exp_pos _).le

end

end ERZeroFreeness
