/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSConc
import ERZeroFreeness.RSTilt

/-!
# Appendix C, Lemma C.7, Step 1: free energy at density `s'` (`eq:rs-frac`)

At a real anchor `x ∈ (0,1]` (`t = t(x)`, `ℓ = log(e/x)`, `F = F_G(x)`) and density `s ≥ 0`
(used at `s = s' = d + Δ`), with `f̄_n = E_σ E_{𝖯^σ_s} log F` (`rsFbar`) and
`C'_⋆ = 1 + (3/2)s + (9/4)s²` (the constant of Lemma C.6 for the kernel `s M_x ≤ (3/2) s`):

* `rs_fbar_eventually_le`: if `E_{𝖯_s}[F log F] ≤ εn` eventually for every `ε > 0` (the upper half
  of `eq:rs-input`), then `f̄_n ≤ εn` eventually for every `ε > 0` (`limsup f̄_n/n ≤ 0`);
* `rs_frac` (**`eq:rs-frac`**): `E_{𝖯_s} F^{1+h} ≤ exp(h f̄_n + C'_⋆ h² ℓ² n)` for `0 < h ≤ 1/ℓ`
  and `n ≥ 1`.

## Proof

This is Step 1 of the paper's proof of Lemma C.7.  Lemma C.6 (`rs_cond_poisson_abs_le`,
`rs_cond_poisson_exp_mul_le`) applies to `f = log F` with uniform labels `σ`, kernel `s M_x`
(`0 ≤ s M_x ≤ (3/2)s`, `rs_rsM_mem`) and `B = ℓ` (`rs_edgeLip_log_rsF`).
* By the one-tilt summed over `σ` (`rsExp_rsF_mul`, from `rs_one_tilt_pt`) with `g = f̄_n - log F`,
  `E_{𝖯_s}[F] f̄_n - E_{𝖯_s}[F log F] = E_σ[e^{κ_s(σ)} (f̄_n - E_{𝖯^σ_s} log F)]`
  `≤ E_σ E_{𝖯^σ_s} |log F - f̄_n| ≤ 2 e^{C'_⋆} ℓ √n` (`0 < e^{κ_s} ≤ 1`).  Since
  `E_{𝖯_s} F ≥ e^{-s/2}` (`rs_poisson_first_moment`), if `f̄_n > 0` then
  `f̄_n ≤ e^{s/2}(E_{𝖯_s}[F log F] + 2e^{C'_⋆} ℓ √n)`, which is `≤ εn` eventually.
* `F^{1+h} = F · e^{h log F}`; the one-tilt with `Φ = F^h` and `e^{κ_s} ≤ 1` give
  `E_{𝖯_s} F^{1+h} ≤ E_σ E_{𝖯^σ_s} e^{h log F}`, and `rs_cond_poisson_exp_mul_le` with `|h| ≤ 1/ℓ`.
Summability of all integrands: `x^m ≤ F ≤ (3/2)^m` (`rs_rsF_bounds`), so `|log F| ≤ ℓ m`, and
`rs_summable_poisPi_of_abs_le`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

namespace RSAnchorFreeAux

/-- `ℓ = log(e/x) = 1 - log x`. -/
lemma rsEll_eq {x : ℝ} (hx0 : 0 < x) : rsEll x = 1 - Real.log x := by
  unfold rsEll
  rw [Real.log_div (Real.exp_pos 1).ne' hx0.ne', Real.log_exp]

/-- `ℓ ≥ 1` for `x ∈ (0,1]`. -/
lemma one_le_rsEll {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : 1 ≤ rsEll x := by
  rw [rsEll_eq hx0]
  have := Real.log_nonpos hx0.le hx1
  linarith

/-- `0 < F_G(x)`. -/
lemma rsF_pos {q n : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (N : RSGraph n) :
    0 < rsF q (tRe q x) N :=
  lt_of_lt_of_le (pow_pos hx0 _) (rs_rsF_bounds hq hx0 hx1 N).1

/-- `|log F_G(x)| ≤ ℓ m`. -/
lemma abs_log_rsF_le {q n : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (N : RSGraph n) : |Real.log (rsF q (tRe q x) N)| ≤ rsEll x * (rsEdges N : ℝ) := by
  obtain ⟨h1, h2⟩ := rs_rsF_bounds hq hx0 hx1 N
  have hF := rsF_pos hq hx0 hx1 N
  have hlo : (rsEdges N : ℝ) * Real.log x ≤ Real.log (rsF q (tRe q x) N) := by
    rw [← Real.log_pow]; exact Real.log_le_log (pow_pos hx0 _) h1
  have hhi : Real.log (rsF q (tRe q x) N) ≤ (rsEdges N : ℝ) * Real.log (3 / 2) := by
    rw [← Real.log_pow]; exact Real.log_le_log hF h2
  have hl32 : Real.log (3 / 2 : ℝ) ≤ 1 / 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num); linarith
  have hlx : Real.log x ≤ 0 := Real.log_nonpos hx0.le hx1
  have hm : (0 : ℝ) ≤ rsEdges N := Nat.cast_nonneg _
  rw [rsEll_eq hx0, abs_le]
  constructor <;> nlinarith

/-- The kernel `s M_x` is nonnegative. -/
lemma kernel_nonneg {q : ℕ} (hq : 3 ≤ q) {x s : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hs : 0 ≤ s)
    (a b : Fin q) : 0 ≤ s * rsM q (tRe q x) a b :=
  mul_nonneg hs (hx0.le.trans (rs_rsM_mem hq hx0.le hx1 a b).1)

/-- The kernel `s M_x` is at most `(3/2) s`. -/
lemma kernel_le {q : ℕ} (hq : 3 ≤ q) {x s : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hs : 0 ≤ s)
    (a b : Fin q) : s * rsM q (tRe q x) a b ≤ 3 / 2 * s := by
  have := (rs_rsM_mem hq hx0.le hx1 a b).2
  nlinarith

/-- `κ_s(σ) ≤ 0` at a real anchor. -/
lemma rsKappa_nonpos {q n : ℕ} (hq : 3 ≤ q) {x s : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hs : 0 ≤ s)
    (σ : Fin n → Fin q) : rsKappa q n s (tRe q x) σ ≤ 0 := by
  unfold rsKappa
  have ht : tRe q x ≤ 0 := rs_tRe_nonpos (by omega) hx0 hx1
  have hA : 0 ≤ ∑ u, ∑ v, ((rsA q (σ u) (σ v) : ℤ) : ℝ) := by
    simp_rw [rs_rsA_cast_eq_aa]
    exact TwoReplicaAux.sum_aa_nonneg (by omega) σ
  have hsn : 0 ≤ s / (2 * n) := by positivity
  exact mul_nonpos_of_nonneg_of_nonpos hsn (mul_nonpos_of_nonpos_of_nonneg ht hA)

/-- Domination by `A + B m` gives summability. -/
lemma summable_of_abs_le_lin {n : ℕ} {lam : Fin n × Fin n → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    {g : RSGraph n → ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hg : ∀ N, |g N| ≤ A + B * (rsEdges N : ℝ)) :
    Summable (fun N => poisPi lam N * g N) := by
  refine rs_summable_poisPi_of_abs_le hlam (A := A + B) (c := 2) (by norm_num) fun N => ?_
  change |g N| ≤ (A + B) * 2 ^ rsEdges N
  have h1 : (rsEdges N : ℝ) ≤ (2 : ℝ) ^ rsEdges N := by
    have : rsEdges N < 2 ^ rsEdges N := Nat.lt_two_pow_self
    exact_mod_cast this.le
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ rsEdges N := one_le_pow₀ (by norm_num)
  calc |g N| ≤ A + B * (rsEdges N : ℝ) := hg N
    _ ≤ A * 2 ^ rsEdges N + B * 2 ^ rsEdges N := by nlinarith
    _ = (A + B) * 2 ^ rsEdges N := by ring

/-- Pointwise one-tilt of `F`: `𝖯_s(N) F(N) g(N) = q^{-n} ∑_σ e^{κ_s(σ)} 𝖯^σ_s(N) g(N)`. -/
lemma poisPi_mul_rsF_mul {q n : ℕ} (s t : ℝ) (g : RSGraph n → ℝ) (N : RSGraph n) :
    poisPi (rsMean n s) N * (rsF q t N * g N) =
      ∑ σ : Fin n → Fin q, (∏ _v : Fin n, (q : ℝ)⁻¹) *
        (Real.exp (rsKappa q n s t σ) *
          (poisPi (cpMean (fun a b => s * rsM q t a b) σ) N * g N)) := by
  have hprod : (∏ _v : Fin n, (q : ℝ)⁻¹) = ((q : ℝ) ^ n)⁻¹ := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
  rw [hprod]
  unfold rsF
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have := rs_one_tilt_pt (q := q) s t σ N
  linear_combination ((q : ℝ) ^ n)⁻¹ * g N * this

/-- `E_{𝖯_s}[F g] = E_σ[e^{κ_s(σ)} E_{𝖯^σ_s} g]` (one-tilt, summed over `σ`). -/
lemma rsExp_rsF_mul {q n : ℕ} (s t : ℝ) (g : RSGraph n → ℝ)
    (hg : ∀ σ : Fin n → Fin q,
      Summable fun N => poisPi (cpMean (fun a b => s * rsM q t a b) σ) N * g N) :
    rsExp n s (fun N => rsF q t N * g N) =
      ∑ σ : Fin n → Fin q, (∏ _v : Fin n, (q : ℝ)⁻¹) *
        (Real.exp (rsKappa q n s t σ) *
          poisPiExp (cpMean (fun a b => s * rsM q t a b) σ) g) := by
  unfold rsExp poisPiExp
  rw [tsum_congr (poisPi_mul_rsF_mul s t g),
    Summable.tsum_finsetSum (fun σ _ => ((hg σ).mul_left _).mul_left _)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [tsum_mul_left, tsum_mul_left]

/-- Summability of `𝖯_s F g` from summability of every `𝖯^σ_s g`. -/
lemma summable_rsF_mul {q n : ℕ} (s t : ℝ) (g : RSGraph n → ℝ)
    (hg : ∀ σ : Fin n → Fin q,
      Summable fun N => poisPi (cpMean (fun a b => s * rsM q t a b) σ) N * g N) :
    Summable fun N => poisPi (rsMean n s) N * (rsF q t N * g N) := by
  have H := summable_sum (s := (Finset.univ : Finset (Fin n → Fin q)))
    (f := fun σ N => (∏ _v : Fin n, (q : ℝ)⁻¹) *
        (Real.exp (rsKappa q n s t σ) *
          (poisPi (cpMean (fun a b => s * rsM q t a b) σ) N * g N)))
    (fun σ _ => ((hg σ).mul_left _).mul_left _)
  exact H.congr fun N => (poisPi_mul_rsF_mul s t g N).symm

end RSAnchorFreeAux

open RSAnchorFreeAux

/-- The key inequality of Step 1 (`E_{𝖯_s}[F] f̄_n - E_{𝖯_s}[F log F] ≤ 2 e^{C'_⋆} ℓ √n`). -/
lemma rsAnchorFree_fbar_key {q : ℕ} (hq : 3 ≤ q) {x s : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hs : 0 ≤ s) {n : ℕ} (hn : 0 < n) :
    rsExp n s (rsF q (tRe q x)) * rsFbar q n s (tRe q x) ≤
      rsExp n s (fun N => rsF q (tRe q x) N * Real.log (rsF q (tRe q x) N)) +
        2 * Real.exp (1 + 3 / 2 * s + (3 / 2 * s) ^ 2) * rsEll x * Real.sqrt n := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hℓ : 0 < rsEll x := by linarith [one_le_rsEll hx0 hx1]
  have hK0 : ∀ a b : Fin q, 0 ≤ s * rsM q (tRe q x) a b := kernel_nonneg hq hx0 hx1 hs
  have hK1 : ∀ a b : Fin q, s * rsM q (tRe q x) a b ≤ 3 / 2 * s := kernel_le hq hx0 hx1 hs
  have hp0 : ∀ (_ : Fin n) (_ : Fin q), (0 : ℝ) ≤ (q : ℝ)⁻¹ := fun _ _ => by positivity
  have hp1 : ∀ _ : Fin n, ∑ _a : Fin q, (q : ℝ)⁻¹ = 1 := by
    intro _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hq0.ne']
  have hm : ∀ (σ : Fin n → Fin q) e, 0 ≤ cpMean (fun a b => s * rsM q (tRe q x) a b) σ e :=
    fun σ e => div_nonneg (hK0 _ _) (by positivity)
  set fb := rsFbar q n s (tRe q x) with hfb
  have hlog : ∀ σ : Fin n → Fin q, Summable fun N =>
      poisPi (cpMean (fun a b => s * rsM q (tRe q x) a b) σ) N * Real.log (rsF q (tRe q x) N) :=
    fun σ => summable_of_abs_le_lin (hm σ) le_rfl hℓ.le fun N => by
      rw [zero_add]; exact abs_log_rsF_le hq hx0 hx1 N
  have hg : ∀ σ : Fin n → Fin q, Summable fun N =>
      poisPi (cpMean (fun a b => s * rsM q (tRe q x) a b) σ) N *
        (fb - Real.log (rsF q (tRe q x) N)) :=
    fun σ => summable_of_abs_le_lin (hm σ) (abs_nonneg fb) hℓ.le fun N =>
      (abs_sub _ _).trans (add_le_add le_rfl (abs_log_rsF_le hq hx0 hx1 N))
  have habs : ∀ σ : Fin n → Fin q, Summable fun N =>
      poisPi (cpMean (fun a b => s * rsM q (tRe q x) a b) σ) N *
        |Real.log (rsF q (tRe q x) N) - fb| :=
    fun σ => summable_of_abs_le_lin (hm σ) (abs_nonneg fb) hℓ.le fun N => by
      rw [abs_abs, add_comm]
      exact (abs_sub _ _).trans (add_le_add (abs_log_rsF_le hq hx0 hx1 N) le_rfl)
  have hsum1 : Summable fun N => poisPi (rsMean n s) N * rsF q (tRe q x) N :=
    (rs_poisson_first_moment hq hs hx0.le hx1).1
  have hsum2 : Summable fun N => poisPi (rsMean n s) N *
      (rsF q (tRe q x) N * Real.log (rsF q (tRe q x) N)) :=
    summable_rsF_mul s (tRe q x) _ hlog
  have hid : rsExp n s (fun N => rsF q (tRe q x) N * (fb - Real.log (rsF q (tRe q x) N))) =
      fb * rsExp n s (rsF q (tRe q x)) -
        rsExp n s (fun N => rsF q (tRe q x) N * Real.log (rsF q (tRe q x) N)) := by
    unfold rsExp poisPiExp
    rw [← tsum_mul_left, ← Summable.tsum_sub (hsum1.mul_left fb) hsum2]
    exact tsum_congr fun N => by ring
  have hle : rsExp n s (fun N => rsF q (tRe q x) N * (fb - Real.log (rsF q (tRe q x) N))) ≤
      cpExp (fun (_ : Fin n) (_ : Fin q) => (q : ℝ)⁻¹) (fun a b => s * rsM q (tRe q x) a b)
        (fun _ N => |Real.log (rsF q (tRe q x) N) - fb|) := by
    rw [rsExp_rsF_mul s (tRe q x) _ hg]
    unfold cpExp
    refine Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : poisPiExp (cpMean (fun a b => s * rsM q (tRe q x) a b) σ)
          (fun N => fb - Real.log (rsF q (tRe q x) N)) ≤
        poisPiExp (cpMean (fun a b => s * rsM q (tRe q x) a b) σ)
          (fun N => |Real.log (rsF q (tRe q x) N) - fb|) :=
      rs_poisPiExp_mono (hm σ) (hg σ) (habs σ) fun N => by
        rw [abs_sub_comm]; exact le_abs_self _
    have h2 : 0 ≤ poisPiExp (cpMean (fun a b => s * rsM q (tRe q x) a b) σ)
          (fun N => |Real.log (rsF q (tRe q x) N) - fb|) :=
      tsum_nonneg fun N => mul_nonneg (rs_poisPi_nonneg (hm σ) N) (abs_nonneg _)
    have he0 : 0 ≤ Real.exp (rsKappa q n s (tRe q x) σ) := (Real.exp_pos _).le
    have he1 : Real.exp (rsKappa q n s (tRe q x) σ) ≤ 1 :=
      Real.exp_le_one_iff.mpr (rsKappa_nonpos hq hx0.le hx1 hs σ)
    calc Real.exp (rsKappa q n s (tRe q x) σ) *
          poisPiExp (cpMean (fun a b => s * rsM q (tRe q x) a b) σ)
            (fun N => fb - Real.log (rsF q (tRe q x) N))
        ≤ Real.exp (rsKappa q n s (tRe q x) σ) *
          poisPiExp (cpMean (fun a b => s * rsM q (tRe q x) a b) σ)
            (fun N => |Real.log (rsF q (tRe q x) N) - fb|) :=
          mul_le_mul_of_nonneg_left h1 he0
      _ ≤ 1 * poisPiExp (cpMean (fun a b => s * rsM q (tRe q x) a b) σ)
            (fun N => |Real.log (rsF q (tRe q x) N) - fb|) :=
          mul_le_mul_of_nonneg_right he1 h2
      _ = _ := one_mul _
  have hconc := rs_cond_poisson_abs_le hn (p := fun (_ : Fin n) (_ : Fin q) => (q : ℝ)⁻¹)
    hp0 hp1 hK0 hK1 hℓ (rs_edgeLip_log_rsF (n := n) hq hx0 hx1)
  have key := hle.trans hconc
  rw [hid] at key
  linarith [mul_comm fb (rsExp n s (rsF q (tRe q x)))]

/-- **Lemma C.7, Step 1.** The upper half of `eq:rs-input` at density `s` gives
`limsup_n f̄_n / n ≤ 0`, in the form `∀ ε > 0, ∀ᶠ n, f̄_n ≤ ε n`. -/
theorem rs_fbar_eventually_le {q : ℕ} (hq : 3 ≤ q) {x s : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hs : 0 ≤ s)
    (hfe : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      rsExp n s (fun N => rsF q (tRe q x) N * Real.log (rsF q (tRe q x) N)) ≤ ε * n) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, rsFbar q n s (tRe q x) ≤ ε * n := by
  intro ε hε
  have hℓ : 0 < rsEll x := by linarith [one_le_rsEll hx0 hx1]
  set C := 2 * Real.exp (1 + 3 / 2 * s + (3 / 2 * s) ^ 2) * rsEll x with hC
  have hC0 : 0 ≤ C := by positivity
  set ε' := ε * Real.exp (-(s / 2)) / 2 with hε'
  have hε'0 : 0 < ε' := by positivity
  have hsqrt : ∀ᶠ n : ℕ in atTop, C * Real.sqrt n ≤ ε' * n := by
    filter_upwards [eventually_ge_atTop ⌈(C / ε') ^ 2⌉₊] with n hn
    have hn' : (C / ε') ^ 2 ≤ (n : ℝ) := Nat.ceil_le.mp hn
    have h1 : C / ε' ≤ Real.sqrt n := (le_abs_self _).trans (Real.abs_le_sqrt hn')
    have h2 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
    have h3 : C ≤ ε' * Real.sqrt n := by rwa [div_le_iff₀ hε'0, mul_comm] at h1
    calc C * Real.sqrt n ≤ ε' * Real.sqrt n * Real.sqrt n :=
          mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
      _ = ε' * n := by rw [mul_assoc, h2]
  filter_upwards [hfe ε' hε'0, hsqrt, eventually_ge_atTop 1] with n hn1 hn2 hn3
  by_cases hf : rsFbar q n s (tRe q x) ≤ 0
  · exact hf.trans (by positivity)
  · replace hf := not_le.mp hf
    have hfm := (rs_poisson_first_moment (n := n) hq hs hx0.le hx1).2.1
    have hk := rsAnchorFree_fbar_key hq hx0 hx1 hs (n := n) (by omega)
    have : Real.exp (-(s / 2)) * rsFbar q n s (tRe q x) ≤ Real.exp (-(s / 2)) * (ε * n) := by
      calc Real.exp (-(s / 2)) * rsFbar q n s (tRe q x)
          ≤ rsExp n s (rsF q (tRe q x)) * rsFbar q n s (tRe q x) :=
            mul_le_mul_of_nonneg_right hfm hf.le
        _ ≤ _ := hk
        _ ≤ ε' * n + ε' * n := add_le_add hn1 hn2
        _ = Real.exp (-(s / 2)) * (ε * n) := by rw [hε']; ring
    exact le_of_mul_le_mul_left this (Real.exp_pos _)

/-- **`eq:rs-frac`.** `E_{𝖯_s} F^{1+h} ≤ exp(h f̄_n + C'_⋆ h² ℓ² n)` for `0 < h`, `h ℓ ≤ 1`,
`n ≥ 1`, with `C'_⋆ = 1 + (3/2)s + (9/4)s²`. -/
theorem rs_frac {q : ℕ} (hq : 3 ≤ q) {x s h : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hs : 0 ≤ s)
    {n : ℕ} (hn : 0 < n) (hh : 0 < h) (hhl : h * rsEll x ≤ 1) :
    rsExp n s (fun N => rsF q (tRe q x) N ^ (1 + h)) ≤
      Real.exp (h * rsFbar q n s (tRe q x) +
        (1 + 3 / 2 * s + 9 / 4 * s ^ 2) * h ^ 2 * rsEll x ^ 2 * n) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hℓ : 0 < rsEll x := by linarith [one_le_rsEll hx0 hx1]
  have hK0 : ∀ a b : Fin q, 0 ≤ s * rsM q (tRe q x) a b := kernel_nonneg hq hx0 hx1 hs
  have hK1 : ∀ a b : Fin q, s * rsM q (tRe q x) a b ≤ 3 / 2 * s := kernel_le hq hx0 hx1 hs
  have hp0 : ∀ (_ : Fin n) (_ : Fin q), (0 : ℝ) ≤ (q : ℝ)⁻¹ := fun _ _ => by positivity
  have hp1 : ∀ _ : Fin n, ∑ _a : Fin q, (q : ℝ)⁻¹ = 1 := by
    intro _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hq0.ne']
  have hm : ∀ (σ : Fin n → Fin q) e, 0 ≤ cpMean (fun a b => s * rsM q (tRe q x) a b) σ e :=
    fun σ e => div_nonneg (hK0 _ _) (by positivity)
  have habs : |h| ≤ 1 / rsEll x := by
    rw [abs_of_pos hh, le_div_iff₀ hℓ]; exact hhl
  have hFg : (fun N : RSGraph n => rsF q (tRe q x) N ^ (1 + h)) =
      fun N => rsF q (tRe q x) N * Real.exp (h * Real.log (rsF q (tRe q x) N)) := by
    funext N
    have hF := rsF_pos hq hx0 hx1 N
    rw [Real.rpow_add hF, Real.rpow_one, Real.rpow_def_of_pos hF, mul_comm (Real.log _) h]
  have hgσ : ∀ σ : Fin n → Fin q, Summable fun N =>
      poisPi (cpMean (fun a b => s * rsM q (tRe q x) a b) σ) N *
        Real.exp (h * Real.log (rsF q (tRe q x) N)) := by
    intro σ
    refine rs_summable_poisPi_of_abs_le (hm σ) (A := 1) (c := Real.exp 1) (Real.exp_pos 1).le
      fun N => ?_
    change |Real.exp (h * Real.log (rsF q (tRe q x) N))| ≤ 1 * Real.exp 1 ^ rsEdges N
    rw [abs_of_pos (Real.exp_pos _), one_mul, ← Real.exp_nat_mul, mul_one]
    apply Real.exp_le_exp.mpr
    have hlog := abs_log_rsF_le hq hx0 hx1 N
    calc h * Real.log (rsF q (tRe q x) N) ≤ h * |Real.log (rsF q (tRe q x) N)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hh.le
      _ ≤ h * (rsEll x * rsEdges N) := mul_le_mul_of_nonneg_left hlog hh.le
      _ = (h * rsEll x) * rsEdges N := by ring
      _ ≤ 1 * rsEdges N := mul_le_mul_of_nonneg_right hhl (Nat.cast_nonneg _)
      _ = rsEdges N := one_mul _
  rw [hFg, rsExp_rsF_mul s (tRe q x) _ hgσ]
  calc ∑ σ : Fin n → Fin q, (∏ _v : Fin n, (q : ℝ)⁻¹) *
        (Real.exp (rsKappa q n s (tRe q x) σ) *
          poisPiExp (cpMean (fun a b => s * rsM q (tRe q x) a b) σ)
            (fun N => Real.exp (h * Real.log (rsF q (tRe q x) N))))
      ≤ ∑ σ : Fin n → Fin q, (∏ _v : Fin n, (q : ℝ)⁻¹) *
          poisPiExp (cpMean (fun a b => s * rsM q (tRe q x) a b) σ)
            (fun N => Real.exp (h * Real.log (rsF q (tRe q x) N))) := by
        refine Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h0 : 0 ≤ poisPiExp (cpMean (fun a b => s * rsM q (tRe q x) a b) σ)
            (fun N => Real.exp (h * Real.log (rsF q (tRe q x) N))) :=
          tsum_nonneg fun N => mul_nonneg (rs_poisPi_nonneg (hm σ) N) (Real.exp_pos _).le
        have he1 : Real.exp (rsKappa q n s (tRe q x) σ) ≤ 1 :=
          Real.exp_le_one_iff.mpr (rsKappa_nonpos hq hx0.le hx1 hs σ)
        calc Real.exp (rsKappa q n s (tRe q x) σ) *
              poisPiExp (cpMean (fun a b => s * rsM q (tRe q x) a b) σ)
                (fun N => Real.exp (h * Real.log (rsF q (tRe q x) N)))
            ≤ 1 * poisPiExp (cpMean (fun a b => s * rsM q (tRe q x) a b) σ)
                (fun N => Real.exp (h * Real.log (rsF q (tRe q x) N))) :=
              mul_le_mul_of_nonneg_right he1 h0
          _ = _ := one_mul _
    _ = cpExp (fun (_ : Fin n) (_ : Fin q) => (q : ℝ)⁻¹) (fun a b => s * rsM q (tRe q x) a b)
          (fun _ N => Real.exp (h * Real.log (rsF q (tRe q x) N))) := rfl
    _ ≤ Real.exp (h * rsFbar q n s (tRe q x) +
          (1 + 3 / 2 * s + (3 / 2 * s) ^ 2) * h ^ 2 * rsEll x ^ 2 * n) :=
        rs_cond_poisson_exp_mul_le (p := fun (_ : Fin n) (_ : Fin q) => (q : ℝ)⁻¹)
          (f := fun N => Real.log (rsF q (tRe q x) N)) hp0 hp1 hK0 hK1 hℓ
          (rs_edgeLip_log_rsF hq hx0 hx1) habs
    _ = Real.exp (h * rsFbar q n s (tRe q x) +
          (1 + 3 / 2 * s + 9 / 4 * s ^ 2) * h ^ 2 * rsEll x ^ 2 * n) := by
        congr 1; ring

end

end ERZeroFreeness
