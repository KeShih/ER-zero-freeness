/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSAnchorBad

/-!
# Appendix C: estimates at a real anchor (Lemma C.7, `lem:rs-anchor`)

* `rs_pair_tail` (**`eq:rs-pair-tail`**, Step 5): given `eq:rs-bad` with some rate `γ ∈ (0,1]` and
  the two conclusions of Lemma C.5 at the anchor, `E_{𝖯_d}[H 1_{F > e^{γn/4}}] ≤ C₁ e^{-c₂γ²n/ℓ²}`
  for large `n`, with `c₂ = (1 - 1/p)/(256 C_𝖰) ∈ (0,1]`, `C_𝖰 = 1 + (9/4)d + (81/16)d²`;
* `rs_anchor` (**Lemma C.7**), from `rs_bad`, `rs_bad_one` and `rs_pair_tail`.

**Form of Lemma C.7.**  The inputs that the paper takes from the surrounding text are hypotheses:
the upper half of `eq:rs-input` at density `d + Δ` (for `x < 1`), and Lemma C.5(i), (ii) at the
anchor, with the same constants `C₀`, `C₁` for every anchor.  The constants `c₁`, `c₂` are those
of `rs_bad` and `rs_pair_tail`, so they depend only on `q, d, Δ, η, p`, as in the paper; `γ_x`
and the threshold `n_x` depend on the anchor.  Anchors are real `x ∈ (0,1]`, `t = t(x)`,
`ℓ = log(e/x)`.

## Proof of `rs_pair_tail`

This is Step 5 of the paper's proof, in six steps, with AM–GM in place of Cauchy–Schwarz in
step 2.  Let `a̲ = e^{-d/2}/2` and `A₀ = 2C₀/a̲`.
1. `E[H/F] = E F - E Y ≥ e^{-d/2} - e^{-γn} ≥ a̲` for large `n` (`rs_poisson_first_moment`;
   `H/F = F - Y`).
2. `H/F ≤ √H ≤ (cH + 1/c)/2` with `c = 2/a̲` (as `H ≤ F²`), `H/F ≤ H/A₀` on `{F > A₀}` and
   `E H ≤ C₀` give `J = E[H 1_{F ≤ A₀}] ≥ a̲²/4`.
3. Lemma C.5(ii) with `ℰ = {F ≤ A₀}`: `Pr_𝖰[F ≤ A₀] ≥ c_𝖰 = (a̲²/(4C₁))^{p/(p-1)}`.
4. Under `𝖰` the labels `(σ_v, τ_v)` are uniform on `[q]²` and the kernel is
   `rsPairK q d t ≤ (9/4)d`; Lemma C.6 (`rs_cond_poisson_abs_le`) with `f = log F`, `B = ℓ`
   (`rs_edgeLip_log_rsF`) and the inequality `(f̄_𝖰 - log A₀) 1_{F ≤ A₀} ≤ |log F - f̄_𝖰|` give
   `f̄_𝖰 = E_𝖰 log F ≤ log A₀ + 2e^{C_𝖰} ℓ √n / c_𝖰 ≤ γn/8` for large `n`.
5. Chernoff (`rs_cond_poisson_tail_le`) with `h' = γ/(16 C_𝖰 ℓ²) ≤ 1/ℓ`:
   `Pr_𝖰[F > e^{γn/4}] ≤ Pr_𝖰[log F - f̄_𝖰 ≥ γn/8] ≤ e^{-γ²n/(256 C_𝖰 ℓ²)}`.
6. Lemma C.5(ii) with `ℰ = {F > e^{γn/4}}` and monotonicity of `y ↦ y^{1-1/p}`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

namespace RSAnchorTailAux

theorem rsEll_ge_one {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : 1 ≤ rsEll x := by
  unfold rsEll
  rw [Real.log_div (Real.exp_pos 1).ne' hx0.ne', Real.log_exp]
  have : Real.log x ≤ 0 := Real.log_nonpos hx0.le hx1
  linarith

theorem rsF_pos {q n : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (N : RSGraph n) :
    0 < rsF q (tRe q x) N :=
  lt_of_lt_of_le (pow_pos hx0 _) (rs_rsF_bounds hq hx0 hx1 N).1

theorem rsMean_nonneg {n : ℕ} {s : ℝ} (hs : 0 ≤ s) : ∀ i, 0 ≤ rsMean n s i := fun _ => by
  unfold rsMean; positivity

theorem indicator_one_nonneg {α : Type*} (s : Set α) (a : α) :
    0 ≤ s.indicator (fun _ => (1 : ℝ)) a := by
  by_cases h : a ∈ s
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]

theorem indicator_one_le {α : Type*} (s : Set α) (a : α) :
    s.indicator (fun _ => (1 : ℝ)) a ≤ 1 := by
  by_cases h : a ∈ s
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h]; norm_num

/-- Bounded functions are integrable against a product Poisson law. -/
theorem summable_of_abs_le_const {ι : Type*} [Fintype ι] {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    {f : (ι → ℕ) → ℝ} {A : ℝ} (hf : ∀ N, |f N| ≤ A) :
    Summable (fun N => poisPi lam N * f N) :=
  rs_summable_poisPi_of_abs_le hlam (A := A) (c := 1) zero_le_one
    (fun N => by rw [one_pow, mul_one]; exact hf N)

/-- `cpExp` is homogeneous. -/
theorem cpExp_const_mul {n : ℕ} {S : Type*} [Fintype S] (p : Fin n → S → ℝ) (K : S → S → ℝ)
    (c : ℝ) (G : (Fin n → S) → RSGraph n → ℝ) :
    cpExp p K (fun ξ N => c * G ξ N) = c * cpExp p K G := by
  unfold cpExp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [rs_poisPiExp_const_mul]
  ring

/-! ### The law `𝖰` -/

theorem pQ_nonneg {q n : ℕ} :
    ∀ (v : Fin n) (a : Fin q × Fin q),
      0 ≤ (fun (_ : Fin n) (_ : Fin q × Fin q) => ((q : ℝ) ^ 2)⁻¹) v a :=
  fun _ _ => by positivity

theorem pQ_sum {q n : ℕ} (hq : 3 ≤ q) :
    ∀ v : Fin n, ∑ a, (fun (_ : Fin n) (_ : Fin q × Fin q) => ((q : ℝ) ^ 2)⁻¹) v a = 1 := by
  intro v
  have hq0 : (q : ℝ) ≠ 0 := by
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq
    positivity
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  field_simp

theorem pairK_nonneg {q : ℕ} (hq : 3 ≤ q) {d x : ℝ} (hd : 0 ≤ d) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (a b : Fin q × Fin q) : 0 ≤ rsPairK q d (tRe q x) a b := by
  have h1 := rs_rsM_mem hq hx0 hx1 a.1 b.1
  have h2 := rs_rsM_mem hq hx0 hx1 a.2 b.2
  unfold rsPairK
  have : 0 ≤ rsM q (tRe q x) a.1 b.1 := hx0.trans h1.1
  have : 0 ≤ rsM q (tRe q x) a.2 b.2 := hx0.trans h2.1
  positivity

theorem pairK_le {q : ℕ} (hq : 3 ≤ q) {d x : ℝ} (hd : 0 ≤ d) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (a b : Fin q × Fin q) : rsPairK q d (tRe q x) a b ≤ 9 / 4 * d := by
  have h1 := rs_rsM_mem hq hx0 hx1 a.1 b.1
  have h2 := rs_rsM_mem hq hx0 hx1 a.2 b.2
  unfold rsPairK
  have e1 : 0 ≤ rsM q (tRe q x) a.1 b.1 := hx0.trans h1.1
  have e2 : 0 ≤ rsM q (tRe q x) a.2 b.2 := hx0.trans h2.1
  have h3 : rsM q (tRe q x) a.1 b.1 * rsM q (tRe q x) a.2 b.2 ≤ 3 / 2 * (3 / 2) :=
    mul_le_mul h1.2 h2.2 e2 (by norm_num)
  calc d * rsM q (tRe q x) a.1 b.1 * rsM q (tRe q x) a.2 b.2
      = d * (rsM q (tRe q x) a.1 b.1 * rsM q (tRe q x) a.2 b.2) := by ring
    _ ≤ d * (3 / 2 * (3 / 2)) := mul_le_mul_of_nonneg_left h3 hd
    _ = 9 / 4 * d := by ring

theorem cpMean_pairK_nonneg {q n : ℕ} (hq : 3 ≤ q) {d x : ℝ} (hd : 0 ≤ d) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) (ξ : Fin n → Fin q × Fin q) :
    ∀ e, 0 ≤ cpMean (rsPairK q d (tRe q x)) ξ e :=
  fun e => div_nonneg (pairK_nonneg hq hd hx0 hx1 _ _) (by positivity)

theorem rsQProb_nonneg {q n : ℕ} (hq : 3 ≤ q) {d x : ℝ} (hd : 0 ≤ d) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) (E : Set (RSGraph n)) : 0 ≤ rsQProb q n d (tRe q x) E := by
  unfold rsQProb cpExp
  refine Finset.sum_nonneg fun ξ _ => mul_nonneg (Finset.prod_nonneg fun v _ => by positivity) ?_
  unfold poisPiExp
  exact tsum_nonneg fun N => mul_nonneg
    (rs_poisPi_nonneg (cpMean_pairK_nonneg hq hd hx0 hx1 ξ) N) (indicator_one_nonneg _ _)

/-! ### Pointwise AM–GM -/

theorem pt_small {F H a : ℝ} (hF : 0 < F) (hH0 : 0 ≤ H) (hHF : H ≤ F ^ 2) (ha : 0 < a) :
    F ≤ (F ^ 2 - H) / F + a⁻¹ * H + a / 4 := by
  have hY : (F ^ 2 - H) / F = F - H / F := by field_simp
  rw [hY]
  have key : 0 ≤ F * ((4 * H + a ^ 2) * F - 4 * a * H) := by
    have : F * ((4 * H + a ^ 2) * F - 4 * a * H) =
        4 * H * (F ^ 2 - H) + (2 * H - a * F) ^ 2 := by
      ring
    rw [this]
    have : 0 ≤ F ^ 2 - H := by linarith
    positivity
  have key2 : 0 ≤ (4 * H + a ^ 2) * F - 4 * a * H := (mul_nonneg_iff_of_pos_left hF).1 key
  have h3 : H / F ≤ a⁻¹ * H + a / 4 := by
    rw [div_le_iff₀ hF]
    have : (a⁻¹ * H + a / 4) * F - H = ((4 * H + a ^ 2) * F - 4 * a * H) / (4 * a) := by
      field_simp
    have : 0 ≤ (a⁻¹ * H + a / 4) * F - H := by
      rw [this]; exact div_nonneg key2 (by positivity)
    linarith
  linarith

theorem pt_large {F H A : ℝ} (hF : A < F) (hH0 : 0 ≤ H) (hA : 0 < A) :
    F ≤ (F ^ 2 - H) / F + A⁻¹ * H := by
  have hF0 : 0 < F := hA.trans hF
  have hY : (F ^ 2 - H) / F = F - H / F := by field_simp
  rw [hY]
  have : H / F ≤ A⁻¹ * H := by
    rw [div_le_iff₀ hF0]
    have : A⁻¹ * H * F - H = H * (F - A) / A := by field_simp
    have : 0 ≤ A⁻¹ * H * F - H := by
      rw [this]
      exact div_nonneg (mul_nonneg hH0 (by linarith)) hA.le
    linarith
  linarith

/-- An `rpow` inversion: `b ≤ y^θ` with `y ≥ 0`, `θ > 0` gives `b^{1/θ} ≤ y`. -/
theorem rpow_inv_le_of_le_rpow {y b θ : ℝ} (hy : 0 ≤ y) (hb : 0 ≤ b) (hθ : 0 < θ)
    (h : b ≤ y ^ θ) : b ^ θ⁻¹ ≤ y := by
  have := Real.rpow_le_rpow hb h (inv_nonneg.2 hθ.le)
  rwa [← Real.rpow_mul hy, mul_inv_cancel₀ hθ.ne', Real.rpow_one] at this

/-! ### Steps 1–2: `E[H 1_{F ≤ A₀}] ≥ a̲²/4` -/

theorem summable_rsHR {q n : ℕ} (hq : 3 ≤ q) {d η x : ℝ} (hd : 0 ≤ d) (hx0 : 0 < x)
    (hx1 : x ≤ 1) :
    Summable (fun N => poisPi (rsMean n d) N * rsHR q η (tRe q x) N) := by
  refine rs_summable_poisPi_of_abs_le (rsMean_nonneg hd) (A := 1) (c := 9 / 4) (by norm_num)
    (fun N => ?_)
  have hH := rs_rsHR_bounds hq hx0.le hx1 η N
  have hF := rs_rsF_bounds hq hx0 hx1 N
  rw [abs_of_nonneg hH.1, one_mul]
  calc rsHR q η (tRe q x) N ≤ rsF q (tRe q x) N ^ 2 := hH.2
    _ ≤ ((3 / 2 : ℝ) ^ rsEdges N) ^ 2 := pow_le_pow_left₀ (rsF_pos hq hx0 hx1 N).le hF.2 2
    _ = (9 / 4 : ℝ) ^ (∑ i, N i) := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
      rfl

theorem J_ge {q n : ℕ} (hq : 3 ≤ q) {d η x C₀ : ℝ} (hd : 0 < d) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hC₀ : 0 < C₀)
    (hEY : rsExp n d (rsY q η (tRe q x)) ≤ Real.exp (-(d / 2)) / 2)
    (hEH : rsExp n d (rsHR q η (tRe q x)) ≤ C₀) :
    (Real.exp (-(d / 2)) / 2) ^ 2 / 4 ≤
      rsExp n d (fun N => rsHR q η (tRe q x) N *
        {N' : RSGraph n | rsF q (tRe q x) N' ≤ 2 * C₀ / (Real.exp (-(d / 2)) / 2)}.indicator
          (fun _ => (1 : ℝ)) N) := by
  set a := Real.exp (-(d / 2)) / 2 with ha_def
  set A₀ := 2 * C₀ / a with hA₀_def
  set t := tRe q x with ht
  have ha0 : 0 < a := by positivity
  have hA₀0 : 0 < A₀ := by positivity
  have hlam := rsMean_nonneg (n := n) hd.le
  obtain ⟨hFs, hEF, -⟩ := rs_poisson_first_moment (n := n) hq hd.le hx0.le hx1
  have hHs := summable_rsHR (n := n) (η := η) hq hd.le hx0 hx1
  have hYs : Summable (fun N => poisPi (rsMean n d) N * rsY q η t N) := by
    refine Summable.of_nonneg_of_le (fun N => mul_nonneg (rs_poisPi_nonneg hlam N)
      (rs_rsY_bounds hq hx0 hx1 η N).1) (fun N => mul_le_mul_of_nonneg_left
      (rs_rsY_bounds hq hx0 hx1 η N).2 (rs_poisPi_nonneg hlam N)) hFs
  set S : Set (RSGraph n) := {N' : RSGraph n | rsF q t N' ≤ A₀} with hS
  have hJs : Summable (fun N => poisPi (rsMean n d) N *
      (rsHR q η t N * S.indicator (fun _ => (1 : ℝ)) N)) := by
    refine Summable.of_nonneg_of_le (fun N => mul_nonneg (rs_poisPi_nonneg hlam N)
      (mul_nonneg (rs_rsHR_bounds hq hx0.le hx1 η N).1 (indicator_one_nonneg _ _)))
      (fun N => mul_le_mul_of_nonneg_left ?_ (rs_poisPi_nonneg hlam N)) hHs
    have h1 := (rs_rsHR_bounds hq hx0.le hx1 η N).1
    have h2 := indicator_one_le S N
    nlinarith
  have hsum := ((hYs.hasSum.add (hJs.hasSum.mul_left a⁻¹)).add
    ((rs_hasSum_poisPi hlam).mul_left (a / 4))).add (hHs.hasSum.mul_left A₀⁻¹)
  have hle := hasSum_le (fun N => ?_) hFs.hasSum hsum
  · change rsExp n d (rsF q t) ≤ rsExp n d (rsY q η t) +
      a⁻¹ * rsExp n d (fun N => rsHR q η t N * S.indicator (fun _ => (1 : ℝ)) N) +
      a / 4 * 1 + A₀⁻¹ * rsExp n d (rsHR q η t) at hle
    have hEF' : 2 * a ≤ rsExp n d (rsF q t) := by
      have : 2 * a = Real.exp (-(d / 2)) := by rw [ha_def]; ring
      rw [this]; exact hEF
    have hA : A₀⁻¹ * rsExp n d (rsHR q η t) ≤ a / 2 := by
      have : A₀⁻¹ * C₀ = a / 2 := by rw [hA₀_def]; field_simp
      calc A₀⁻¹ * rsExp n d (rsHR q η t) ≤ A₀⁻¹ * C₀ :=
            mul_le_mul_of_nonneg_left hEH (inv_nonneg.2 hA₀0.le)
        _ = a / 2 := this
    have hJ : a / 4 ≤
        a⁻¹ * rsExp n d (fun N => rsHR q η t N * S.indicator (fun _ => (1 : ℝ)) N) := by
      linarith
    have := mul_le_mul_of_nonneg_left hJ ha0.le
    rw [← mul_assoc, mul_inv_cancel₀ ha0.ne', one_mul] at this
    calc a ^ 2 / 4 = a * (a / 4) := by ring
      _ ≤ _ := this
  · -- pointwise inequality
    have hP := rs_poisPi_nonneg hlam N
    have hF := rsF_pos hq hx0 hx1 N (q := q)
    have hH := rs_rsHR_bounds hq hx0.le hx1 η N
    have hY : rsY q η t N = (rsF q t N ^ 2 - rsHR q η t N) / rsF q t N := rfl
    have key : rsF q t N ≤ rsY q η t N +
        a⁻¹ * (rsHR q η t N * S.indicator (fun _ => (1 : ℝ)) N) + a / 4 +
        A₀⁻¹ * rsHR q η t N := by
      rw [hY]
      by_cases hN : N ∈ S
      · rw [Set.indicator_of_mem hN, mul_one]
        have := pt_small hF hH.1 hH.2 ha0
        have : 0 ≤ A₀⁻¹ * rsHR q η t N := mul_nonneg (inv_nonneg.2 hA₀0.le) hH.1
        linarith
      · rw [Set.indicator_of_notMem hN, mul_zero, mul_zero]
        have hN' : A₀ < rsF q t N := lt_of_not_ge hN
        have := pt_large hN' hH.1 hA₀0
        linarith
    calc poisPi (rsMean n d) N * rsF q t N ≤ poisPi (rsMean n d) N * (rsY q η t N +
          a⁻¹ * (rsHR q η t N * S.indicator (fun _ => (1 : ℝ)) N) + a / 4 +
          A₀⁻¹ * rsHR q η t N) := mul_le_mul_of_nonneg_left key hP
      _ = _ := by ring

/-! ### Steps 4–5: concentration under `𝖰` -/

/-- Step 4: `f̄_𝖰 ≤ log A₀ + 2 e^{C_𝖰} ℓ √n / c_𝖰` when `Pr_𝖰[F ≤ A₀] ≥ c_𝖰 > 0`. -/
theorem fbarQ_le {q n : ℕ} (hq : 3 ≤ q) (hn : 0 < n) {d x A₀ cQ : ℝ} (hd : 0 < d)
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hcQ : 0 < cQ)
    (hP : cQ ≤ rsQProb q n d (tRe q x) {N' : RSGraph n | rsF q (tRe q x) N' ≤ A₀}) :
    cpExp (fun (_ : Fin n) (_ : Fin q × Fin q) => ((q : ℝ) ^ 2)⁻¹) (rsPairK q d (tRe q x))
        (fun _ N => Real.log (rsF q (tRe q x) N)) ≤
      Real.log A₀ +
        2 * Real.exp (1 + 9 / 4 * d + (9 / 4 * d) ^ 2) * rsEll x * Real.sqrt n / cQ := by
  set pQ := fun (_ : Fin n) (_ : Fin q × Fin q) => ((q : ℝ) ^ 2)⁻¹ with hpQ
  set K := rsPairK q d (tRe q x) with hK
  set f : RSGraph n → ℝ := fun N => Real.log (rsF q (tRe q x) N) with hf_def
  set fQ := cpExp pQ K (fun _ => f) with hfQ
  have hB : 0 < rsEll x := lt_of_lt_of_le one_pos (rsEll_ge_one hx0 hx1)
  have hconc := rs_cond_poisson_abs_le hn (pQ_nonneg (q := q)) (pQ_sum hq)
    (pairK_nonneg hq hd.le hx0.le hx1) (pairK_le hq hd.le hx0.le hx1) hB
    (rs_edgeLip_log_rsF (n := n) hq hx0 hx1)
  set S : Set (RSGraph n) := {N' : RSGraph n | rsF q (tRe q x) N' ≤ A₀} with hS
  have hmono : cpExp pQ K (fun _ N => (fQ - Real.log A₀) * S.indicator (fun _ => (1 : ℝ)) N) ≤
      cpExp pQ K (fun _ N => |f N - fQ|) := by
    refine rs_cpExp_mono (pQ_nonneg (q := q)) (pairK_nonneg hq hd.le hx0.le hx1)
      (fun ξ => ?_) (fun ξ => ?_) (fun ξ N => ?_)
    · refine summable_of_abs_le_const (cpMean_pairK_nonneg hq hd.le hx0.le hx1 ξ)
        (A := |fQ - Real.log A₀|) (fun N => ?_)
      rw [abs_mul, abs_of_nonneg (indicator_one_nonneg S N)]
      exact mul_le_of_le_one_right (abs_nonneg _) (indicator_one_le S N)
    · refine rs_edgeLip_summable (cpMean_pairK_nonneg hq hd.le hx0.le hx1 ξ)
        (rs_edgeLip_log_rsF (n := n) hq hx0 hx1) (φ := fun y => |y - fQ|) (A := 1 + |fQ|)
        (c := 1) (fun y => ?_)
      rw [abs_abs, one_mul]
      have h1 : |y| + 1 ≤ Real.exp |y| := Real.add_one_le_exp _
      have h2 : 1 ≤ Real.exp |y| := Real.one_le_exp (abs_nonneg y)
      have h3 : |y - fQ| ≤ |y| + |fQ| := abs_sub _ _
      nlinarith [abs_nonneg fQ]
    · by_cases hN : N ∈ S
      · rw [Set.indicator_of_mem hN, mul_one]
        have hlog : Real.log (rsF q (tRe q x) N) ≤ Real.log A₀ :=
          Real.log_le_log (rsF_pos hq hx0 hx1 N) hN
        have := neg_abs_le (f N - fQ)
        simp only [hf_def] at this ⊢
        linarith
      · rw [Set.indicator_of_notMem hN, mul_zero]
        exact abs_nonneg _
  rw [cpExp_const_mul] at hmono
  have hmono' : (fQ - Real.log A₀) * rsQProb q n d (tRe q x) S ≤
      2 * Real.exp (1 + 9 / 4 * d + (9 / 4 * d) ^ 2) * rsEll x * Real.sqrt n :=
    hmono.trans hconc
  have hM : 0 ≤ 2 * Real.exp (1 + 9 / 4 * d + (9 / 4 * d) ^ 2) * rsEll x * Real.sqrt n := by
    positivity
  rcases le_or_gt (fQ - Real.log A₀) 0 with hD | hD
  · have : 0 ≤ 2 * Real.exp (1 + 9 / 4 * d + (9 / 4 * d) ^ 2) * rsEll x * Real.sqrt n / cQ :=
      div_nonneg hM hcQ.le
    linarith
  · have h1 : (fQ - Real.log A₀) * cQ ≤ (fQ - Real.log A₀) * rsQProb q n d (tRe q x) S :=
      mul_le_mul_of_nonneg_left hP hD.le
    have h2 : fQ - Real.log A₀ ≤
        2 * Real.exp (1 + 9 / 4 * d + (9 / 4 * d) ^ 2) * rsEll x * Real.sqrt n / cQ := by
      rw [le_div_iff₀ hcQ]
      linarith
    linarith

/-- Step 5: the Chernoff tail under `𝖰`, once `f̄_𝖰 ≤ γn/8`. -/
theorem tailQ_le {q n : ℕ} (hq : 3 ≤ q) {d x γ : ℝ} (hd : 0 < d) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hfQ : cpExp (fun (_ : Fin n) (_ : Fin q × Fin q) => ((q : ℝ) ^ 2)⁻¹) (rsPairK q d (tRe q x))
        (fun _ N => Real.log (rsF q (tRe q x) N)) ≤ γ * n / 8) :
    rsQProb q n d (tRe q x) {N' : RSGraph n | Real.exp (γ * n / 4) < rsF q (tRe q x) N'} ≤
      Real.exp (-(γ ^ 2 * n / (256 * (1 + 9 / 4 * d + (9 / 4 * d) ^ 2) * rsEll x ^ 2))) := by
  set pQ := fun (_ : Fin n) (_ : Fin q × Fin q) => ((q : ℝ) ^ 2)⁻¹ with hpQ
  set K := rsPairK q d (tRe q x) with hK
  set f : RSGraph n → ℝ := fun N => Real.log (rsF q (tRe q x) N) with hf_def
  set fQ := cpExp pQ K (fun _ => f) with hfQ_def
  set CQ : ℝ := 1 + 9 / 4 * d + (9 / 4 * d) ^ 2 with hCQ
  set ℓ := rsEll x with hℓ
  have hℓ1 : 1 ≤ ℓ := rsEll_ge_one hx0 hx1
  have hB : 0 < ℓ := lt_of_lt_of_le one_pos hℓ1
  have hCQ1 : 1 ≤ CQ := by rw [hCQ]; nlinarith [sq_nonneg (9 / 4 * d)]
  set h' := γ / (16 * CQ * ℓ ^ 2) with hh'
  have hh0 : 0 ≤ h' := by positivity
  have hh1 : h' ≤ 1 / ℓ := by
    rw [hh', div_le_div_iff₀ (by positivity) hB]
    nlinarith [mul_le_mul hCQ1 hℓ1 zero_le_one (by linarith)]
  have htail := rs_cond_poisson_tail_le (pQ_nonneg (q := q)) (pQ_sum hq)
    (pairK_nonneg hq hd.le hx0.le hx1) (pairK_le hq hd.le hx0.le hx1) hB
    (rs_edgeLip_log_rsF (n := n) hq hx0 hx1) hh0 hh1 (γ * n / 8)
  have hmono : rsQProb q n d (tRe q x)
      {N' : RSGraph n | Real.exp (γ * n / 4) < rsF q (tRe q x) N'} ≤
      cpExp pQ K (fun _ N => if γ * n / 8 ≤ f N - fQ then 1 else 0) := by
    unfold rsQProb
    refine rs_cpExp_mono (pQ_nonneg (q := q)) (pairK_nonneg hq hd.le hx0.le hx1)
      (fun ξ => ?_) (fun ξ => ?_) (fun ξ N => ?_)
    · exact summable_of_abs_le_const (cpMean_pairK_nonneg hq hd.le hx0.le hx1 ξ) (A := 1)
        (fun N => by
          rw [abs_of_nonneg (indicator_one_nonneg _ N)]; exact indicator_one_le _ N)
    · exact summable_of_abs_le_const (cpMean_pairK_nonneg hq hd.le hx0.le hx1 ξ) (A := 1)
        (fun N => by split_ifs <;> norm_num)
    · by_cases hN : N ∈ {N' : RSGraph n | Real.exp (γ * n / 4) < rsF q (tRe q x) N'}
      · rw [Set.indicator_of_mem hN]
        have hlog : γ * n / 4 < Real.log (rsF q (tRe q x) N) :=
          (Real.lt_log_iff_exp_lt (rsF_pos hq hx0 hx1 N)).2 hN
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        rw [if_pos]
        simp only [hf_def]
        nlinarith
      · rw [Set.indicator_of_notMem hN]
        split_ifs <;> norm_num
  refine hmono.trans (htail.trans (le_of_eq ?_))
  congr 1
  rw [hh']
  field_simp
  ring

/-- Eventually `A + M √n ≤ γ n / 8` (applied with `A = log A₀`). -/
theorem eventually_log_add_sqrt_le {A M γ : ℝ} (hM : 0 ≤ M) (hγ : 0 < γ) :
    ∀ᶠ n : ℕ in atTop, A + M * Real.sqrt n ≤ γ * n / 8 := by
  set L := |A| + M with hL
  have hL0 : 0 ≤ L := by positivity
  refine Filter.eventually_atTop.2 ⟨max 1 ⌈(8 * L / γ) ^ 2⌉₊, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
  have hn2 : (8 * L / γ) ^ 2 ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_of_max_le_right hn)
  have hs1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.2 hn1
  have hs2 : 8 * L / γ ≤ Real.sqrt n := Real.le_sqrt_of_sq_le hn2
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  have h3 : A ≤ |A| * Real.sqrt n :=
    le_trans (le_abs_self _) (le_mul_of_one_le_right (abs_nonneg _) hs1)
  have h4 : 8 * L ≤ γ * Real.sqrt n := by
    rw [div_le_iff₀ hγ] at hs2; linarith
  have h5 := mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg (n : ℝ))
  nlinarith

end RSAnchorTailAux

open RSAnchorTailAux in
/-- **`eq:rs-pair-tail`** (Lemma C.7, Step 5), with `c₂` depending only on `d` and `p`. -/
theorem rs_pair_tail {q : ℕ} (hq : 3 ≤ q) {d p : ℝ} (hd : 0 < d) (hp : 1 < p) :
    ∃ c₂ > 0, c₂ ≤ 1 ∧ ∀ η C₀ C₁ γ x : ℝ, 0 < η → 0 < C₀ → 0 < C₁ → 0 < γ → γ ≤ 1 →
      0 < x → x ≤ 1 →
      (∀ᶠ n : ℕ in atTop, rsExp n d (rsY q η (tRe q x)) ≤ Real.exp (-(γ * n))) →
      (∀ n : ℕ, 0 < n → rsExp n d (rsHR q η (tRe q x)) ≤ C₀) →
      (∀ n : ℕ, 0 < n → ∀ E : Set (RSGraph n),
        rsExp n d (fun N => rsHR q η (tRe q x) N * E.indicator (fun _ => (1 : ℝ)) N) ≤
          C₁ * rsQProb q n d (tRe q x) E ^ (1 - p⁻¹)) →
      ∀ᶠ n : ℕ in atTop,
        rsExp n d (fun N => rsHR q η (tRe q x) N *
          {N' : RSGraph n | Real.exp (γ * n / 4) < rsF q (tRe q x) N'}.indicator
            (fun _ => (1 : ℝ)) N) ≤
          C₁ * Real.exp (-(c₂ * γ ^ 2 * n / rsEll x ^ 2)) := by
  have hθ : 0 < 1 - p⁻¹ := by
    have := inv_lt_one_of_one_lt₀ hp
    linarith
  have hθ1 : 1 - p⁻¹ ≤ 1 := by
    have := inv_pos.2 (zero_lt_one.trans hp)
    linarith
  set CQ : ℝ := 1 + 9 / 4 * d + (9 / 4 * d) ^ 2 with hCQ
  have hCQ1 : 1 ≤ CQ := by rw [hCQ]; nlinarith [sq_nonneg (9 / 4 * d)]
  refine ⟨(1 - p⁻¹) / (256 * CQ), by positivity, ?_, ?_⟩
  · rw [div_le_one (by positivity)]
    linarith
  intro η C₀ C₁ γ x hη hC₀ hC₁ hγ hγ1 hx0 hx1 hbad hloc1 hloc2
  set θ := 1 - p⁻¹ with hθ_def
  set a := Real.exp (-(d / 2)) / 2 with ha_def
  have ha0 : 0 < a := by positivity
  set A₀ := 2 * C₀ / a with hA₀_def
  have hA₀0 : 0 < A₀ := by positivity
  set cQ := (a ^ 2 / (4 * C₁)) ^ θ⁻¹ with hcQ_def
  have hcQ0 : 0 < cQ := Real.rpow_pos_of_pos (by positivity) _
  set ℓ := rsEll x with hℓ
  have hℓ1 : 1 ≤ ℓ := rsEll_ge_one hx0 hx1
  set M := 2 * Real.exp CQ * ℓ / cQ with hM_def
  have hM0 : 0 ≤ M := by positivity
  -- eventually `e^{-γn} ≤ a̲`
  have hev1 : ∀ᶠ n : ℕ in atTop, Real.exp (-(γ * n)) ≤ a := by
    have ht : Tendsto (fun n : ℕ => Real.exp (-(γ * n))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Tendsto.const_mul_atTop hγ tendsto_natCast_atTop_atTop)
    exact ht.eventually (eventually_le_nhds ha0)
  have hev2 := eventually_log_add_sqrt_le (A := Real.log A₀) hM0 hγ
  filter_upwards [hbad, hev1, hev2, eventually_gt_atTop 0] with n hYn h1 h2 hn
  -- Steps 1–2
  have hJ : a ^ 2 / 4 ≤ rsExp n d (fun N => rsHR q η (tRe q x) N *
      {N' : RSGraph n | rsF q (tRe q x) N' ≤ A₀}.indicator (fun _ => (1 : ℝ)) N) :=
    J_ge (n := n) hq hd hx0 hx1 hC₀ (hYn.trans h1) (hloc1 n hn)
  -- Step 3: `Pr_𝖰[F ≤ A₀] ≥ c_𝖰`
  have hP := hloc2 n hn {N' : RSGraph n | rsF q (tRe q x) N' ≤ A₀}
  have hP0 := rsQProb_nonneg (n := n) hq hd.le hx0.le hx1
    {N' : RSGraph n | rsF q (tRe q x) N' ≤ A₀}
  have hPθ : a ^ 2 / (4 * C₁) ≤
      rsQProb q n d (tRe q x) {N' : RSGraph n | rsF q (tRe q x) N' ≤ A₀} ^ θ := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hcQ : cQ ≤ rsQProb q n d (tRe q x) {N' : RSGraph n | rsF q (tRe q x) N' ≤ A₀} :=
    rpow_inv_le_of_le_rpow hP0 (by positivity) hθ hPθ
  -- Step 4: `f̄_𝖰 ≤ γ n / 8`
  have hfQ := fbarQ_le hq hn hd hx0 hx1 hcQ0 hcQ
  have hfQ' : cpExp (fun (_ : Fin n) (_ : Fin q × Fin q) => ((q : ℝ) ^ 2)⁻¹)
      (rsPairK q d (tRe q x)) (fun _ N => Real.log (rsF q (tRe q x) N)) ≤ γ * n / 8 := by
    refine hfQ.trans (le_of_eq_of_le ?_ h2)
    rw [hM_def]
    ring
  -- Step 5: the tail under `𝖰`
  have htail := tailQ_le hq hd hx0 hx1 hγ hγ1 hfQ'
  -- Step 6
  have hE := hloc2 n hn {N' : RSGraph n | Real.exp (γ * n / 4) < rsF q (tRe q x) N'}
  refine hE.trans (mul_le_mul_of_nonneg_left ?_ hC₁.le)
  refine (Real.rpow_le_rpow (rsQProb_nonneg hq hd.le hx0.le hx1 _) htail hθ.le).trans
    (le_of_eq ?_)
  rw [← Real.exp_mul]
  congr 1
  have hℓ0 : rsEll x ≠ 0 := by rw [← hℓ]; positivity
  simp only [hℓ, hCQ]
  field_simp

/-- **Lemma C.7 (`lem:rs-anchor`), estimates at a real anchor.**  There are `c₁ > 0` and
`c₂ ∈ (0,1]` such that for every real anchor `x ∈ (0,1]` satisfying the inputs below there is
`γ_x ∈ (0,1]`, with `γ_x ≥ c₁/log²(e/x)` when `x ≤ 1/2`, such that for all large `n`
`E_{𝖯_d} Y ≤ e^{-γ_x n}` (`eq:rs-bad`) and
`E_{𝖯_d}[H 1_{F > e^{γ_x n/4}}] ≤ C₁ exp(-c₂ γ_x² n / log²(e/x))` (`eq:rs-pair-tail`).
Inputs: (for `x < 1`) the upper half of `eq:rs-input` at density `d + Δ`; Lemma C.5(i) and (ii) at
the anchor with constants `C₀`, `C₁`. -/
theorem rs_anchor {q : ℕ} (hq : 3 ≤ q) {d Δ η p C₀ C₁ : ℝ} (hd : 0 < d) (hΔ : 0 < Δ)
    (hΔd : Δ < d) (hη0 : 0 < η) (hp : 1 < p) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) :
    ∃ c₁ > 0, ∃ c₂ > 0, c₂ ≤ 1 ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      (x < 1 → ∀ ε > 0, ∀ᶠ n : ℕ in atTop, rsExp n (d + Δ)
        (fun N => rsF q (tRe q x) N * Real.log (rsF q (tRe q x) N)) ≤ ε * n) →
      (∀ n : ℕ, 0 < n → rsExp n d (rsHR q η (tRe q x)) ≤ C₀) →
      (∀ n : ℕ, 0 < n → ∀ E : Set (RSGraph n),
        rsExp n d (fun N => rsHR q η (tRe q x) N * E.indicator (fun _ => (1 : ℝ)) N) ≤
          C₁ * rsQProb q n d (tRe q x) E ^ (1 - p⁻¹)) →
      ∃ γ > 0, γ ≤ 1 ∧ (x ≤ 1 / 2 → c₁ / rsEll x ^ 2 ≤ γ) ∧
        ∀ᶠ n : ℕ in atTop,
          rsExp n d (rsY q η (tRe q x)) ≤ Real.exp (-(γ * n)) ∧
          rsExp n d (fun N => rsHR q η (tRe q x) N *
            {N' : RSGraph n | Real.exp (γ * n / 4) < rsF q (tRe q x) N'}.indicator
              (fun _ => (1 : ℝ)) N) ≤
            C₁ * Real.exp (-(c₂ * γ ^ 2 * n / rsEll x ^ 2)) := by
  obtain ⟨c₁, hc₁, hbad⟩ := rs_bad hq hd hΔ hΔd.le hη0
  obtain ⟨c₂, hc₂, hc₂1, htail⟩ := rs_pair_tail hq hd hp
  obtain ⟨γ₁, hγ₁, hγ₁1, hbad1⟩ := rs_bad_one hq hd.le hη0
  refine ⟨c₁, hc₁, c₂, hc₂, hc₂1, fun x hx0 hx1 hfe hloc1 hloc2 => ?_⟩
  rcases hx1.lt_or_eq with hx1' | rfl
  · obtain ⟨γ, hγ, hγ1, hlow, hY⟩ := hbad x hx0 hx1' (hfe hx1')
    exact ⟨γ, hγ, hγ1, hlow,
      hY.and (htail η C₀ C₁ γ x hη0 hC₀ hC₁ hγ hγ1 hx0 hx1 hY hloc1 hloc2)⟩
  · refine ⟨γ₁, hγ₁, hγ₁1, fun h => absurd h (by norm_num), ?_⟩
    exact hbad1.and
      (htail η C₀ C₁ γ₁ 1 hη0 hC₀ hC₁ hγ₁ hγ₁1 one_pos le_rfl hbad1 hloc1 hloc2)

end

end ERZeroFreeness
