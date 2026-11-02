/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.CKDefs
import ERZeroFreeness.CKMatrix
import ERZeroFreeness.CKAnalysis
import ERZeroFreeness.CKInfo
import ERZeroFreeness.CKBern
import ERZeroFreeness.CKBethe
import ERZeroFreeness.RSPoisPi
import ERZeroFreeness.RSModel
import ERZeroFreeness.RSBetheBasic
import ERZeroFreeness.RSPoisSplit
import ERZeroFreeness.Poisson

/-!
# Stage B of Appendix C: Lemma 7.3 of the self-contained proof of [CKPZ, Prop. 3.6]

Proof of `CKPZProp36 q` (the Potts specialization of Coja-Oghlan–Krzakala–Perkins–Zdeborová,
Proposition 3.6) from first principles.  The mathematics, with every lemma, constant and limit
order, is in `docs/appendixC/ckpz-proof.md` (Lemma 7.3; its §12 is the Lean plan these frozen
statements come from).  Frozen statements must not be changed; provers add helpers freely.

## Proof outline (as formalized)

* `X_μ(D, N₀) = κ(N₀) X̃(D)` with `κ(N₀) = e^{ϱ(1-m₋)} m₋^{N₀}` (`ckvKap`, `ckvXt`).
  Ranges: `X ∈ [e^{-Γ}, e^{Γ}]`, `Γ = 2ϱn + ϱ + ℓ₀(|D| + N₀)`, so `|Λ(X)| ≤ e^{2Γ}`, a product
  weight with finite Poisson mean; this gives `ck_vert_bdd` and all summability.
* Step 0 (deviation from the paper, simpler): `N₀` is integrated out exactly.  Since
  `log κ ≤ ϱ(1-m₋)` and `E κ(N₀) = 1`, `Vert(μ) ≤ E_D[Λ(X̃) + ϱ(1-m₋)X̃]` (`ckv_vert_le`).
* `BV_r` at the marginals is `E_D Λ(Y(D))` (`ck_BV_emp`, rate `r/n = s/(n+1) = 2ϱ`).
* Pointwise (`ckv_pt`): `|Λ(X̃) - Λ(Y)| ≤ c₂(1+|D|)(|X̃ - X₁| + |X₁ - Y|)` (`ck_lam_lip`), with
  `|X̃ - X₁| ≤ e^s (s|t|q) m₊^{|D|} dev(μ)` (compensators) and `|X₁ - Y| ≤ 2 m₊^{|D|} g(D)`,
  `g = 1_{D ∉ S₁} + ∑_{w ∈ W} √I(τ_w; τ_{W∖w})` (`ck_prod_decorr` on `S₁`).
* One Cauchy–Schwarz (`ckv_cs`) with factors `(1+|D|)^{3/2} m₊^{|D|}` and `g/(1+|D|)^{1/2}`:
  `g²/(1+|D|) ≤ 2·1_{D ∉ S₁} + 2𝒥_μ(W | ∅)`, `P(D ∉ S₁) ≤ nλ²/2` (`ck_pois_tail_two`),
  `E 𝒥_μ(W | ∅) = 𝒥̄_p(μ)` (`ck_poisPi_support`); moments by `(1+k)^j ≤ 2^{jk}`.
-/

open Filter Topology MeasureTheory

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-! ### Elementary ranges -/

private lemma ckv_rsM_pos {q : ℕ} {t : ℝ} (hp : CKPar q t) (a b : Fin q) : 0 < rsM q t a b :=
  lt_of_lt_of_le (ck_const_bounds hp).1 (ck_rsM_mem hp a b).1

private lemma ckv_abs_rsM_sub_one {q : ℕ} {t : ℝ} (hp : CKPar q t) (a b : Fin q) :
    |rsM q t a b - 1| ≤ 1 := by
  obtain ⟨h1, -, -, h4, -⟩ := ck_const_bounds hp
  obtain ⟨l, u⟩ := ck_rsM_mem hp a b
  rw [abs_le]; constructor <;> linarith

private lemma ckv_delta_abs {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (τ : Fin n → Fin q) (c : Fin q) :
    |-(2 * ϱ) * ∑ v, (rsM q t (τ v) c - 1)| ≤ 2 * ϱ * n := by
  rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * ϱ)]
  have h : |∑ v, (rsM q t (τ v) c - 1)| ≤ n := by
    calc |∑ v, (rsM q t (τ v) c - 1)| ≤ ∑ v, |rsM q t (τ v) c - 1| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v : Fin n, (1 : ℝ) := Finset.sum_le_sum fun v _ => ckv_abs_rsM_sub_one hp _ _
      _ = n := by simp
  exact mul_le_mul_of_nonneg_left h (by positivity)

private lemma ckv_prod_pow_mem {n : ℕ} {L U : ℝ} (hL : 0 ≤ L) (x : Fin n → ℝ)
    (hx : ∀ v, L ≤ x v ∧ x v ≤ U) (D : Fin n → ℕ) :
    L ^ (∑ v, D v) ≤ ∏ v, x v ^ D v ∧ ∏ v, x v ^ D v ≤ U ^ (∑ v, D v) := by
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
  constructor
  · exact Finset.prod_le_prod (fun v _ => pow_nonneg hL _)
      fun v _ => pow_le_pow_left₀ hL (hx v).1 _
  · exact Finset.prod_le_prod (fun v _ => pow_nonneg (hL.trans (hx v).1) _)
      fun v _ => pow_le_pow_left₀ (hL.trans (hx v).1) (hx v).2 _

private lemma ckv_avgq_mem {q : ℕ} (hq : q ≠ 0) (y : Fin q → ℝ) {L U : ℝ}
    (hy : ∀ c, L ≤ y c ∧ y c ≤ U) :
    L ≤ (q : ℝ)⁻¹ * ∑ c, y c ∧ (q : ℝ)⁻¹ * ∑ c, y c ≤ U := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have h1 : ∑ _c : Fin q, L ≤ ∑ c, y c := Finset.sum_le_sum fun c _ => (hy c).1
  have h2 : ∑ c, y c ≤ ∑ _c : Fin q, U := Finset.sum_le_sum fun c _ => (hy c).2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1 h2
  exact ⟨(le_inv_mul_iff₀ hq').mpr h1, (inv_mul_le_iff₀ hq').mpr h2⟩

private lemma ckv_avgμ_mem {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (h : (Fin n → Fin q) → ℝ) {L U : ℝ} (hh : ∀ τ, L ≤ h τ ∧ h τ ≤ U) :
    L ≤ ∑ τ, μ τ * h τ ∧ ∑ τ, μ τ * h τ ≤ U := by
  constructor
  · calc L = ∑ τ, μ τ * L := by rw [← Finset.sum_mul, hμ.2, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (hh τ).1 (hμ.1 τ)
  · calc ∑ τ, μ τ * h τ ≤ ∑ τ, μ τ * U :=
          Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (hh τ).2 (hμ.1 τ)
      _ = U := by rw [← Finset.sum_mul, hμ.2, one_mul]

/-! ### The pieces of `X_μ(D, N₀)` -/

/-- `X̃(D) = q⁻¹ ∑_c ⟨e^{δ_c} ∏_v M(τ_v, c)^{D_v}⟩_μ`, so that `X_μ(D, N₀) = κ(N₀) X̃(D)`. -/
private def ckvXt (q : ℕ) (t ϱ : ℝ) {n : ℕ} (μ : (Fin n → Fin q) → ℝ) (D : Fin n → ℕ) : ℝ :=
  (q : ℝ)⁻¹ * ∑ c : Fin q, ∑ τ, μ τ *
    (Real.exp (-(2 * ϱ) * ∑ v, (rsM q t (τ v) c - 1)) * ∏ v, rsM q t (τ v) c ^ D v)

/-- The loop factor `κ(N₀) = e^{ϱ(1 - m₋)} m₋^{N₀}`. -/
private def ckvKap (q : ℕ) (t ϱ : ℝ) (N0 : ℕ) : ℝ :=
  Real.exp (ϱ * (1 - ckMm q t)) * ckMm q t ^ N0

private lemma ckv_X_eq {q n : ℕ} (t ϱ : ℝ) (μ : (Fin n → Fin q) → ℝ) (D : Fin n → ℕ)
    (N0 : ℕ) : ckX q t ϱ μ D N0 = ckvKap q t ϱ N0 * ckvXt q t ϱ μ D := rfl

private lemma ckv_Xt_mem {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (D : Fin n → ℕ) :
    Real.exp (-(2 * ϱ * n)) * ckMm q t ^ (∑ v, D v) ≤ ckvXt q t ϱ μ D ∧
      ckvXt q t ϱ μ D ≤ Real.exp (2 * ϱ * n) * ckMp t ^ (∑ v, D v) := by
  have hq : q ≠ 0 := by have := hp.two_le; omega
  have hm0 := (ck_const_bounds hp).1
  unfold ckvXt
  refine ckv_avgq_mem hq _ fun c => ckv_avgμ_mem hμ _ fun τ => ?_
  have hd := ckv_delta_abs hp hϱ τ c
  have hPi := ckv_prod_pow_mem hm0.le (fun v => rsM q t (τ v) c) (fun v => ck_rsM_mem hp _ _) D
  have he1 : Real.exp (-(2 * ϱ * n)) ≤ Real.exp (-(2 * ϱ) * ∑ v, (rsM q t (τ v) c - 1)) :=
    Real.exp_le_exp.mpr (by have := (abs_le.mp hd).1; linarith)
  have he2 : Real.exp (-(2 * ϱ) * ∑ v, (rsM q t (τ v) c - 1)) ≤ Real.exp (2 * ϱ * n) :=
    Real.exp_le_exp.mpr (abs_le.mp hd).2
  constructor
  · exact mul_le_mul he1 hPi.1 (pow_nonneg hm0.le _) (Real.exp_pos _).le
  · exact mul_le_mul he2 hPi.2 ((pow_nonneg hm0.le _).trans hPi.1) (Real.exp_pos _).le

private lemma ckv_kap_mem {q : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (N0 : ℕ) :
    ckMm q t ^ N0 ≤ ckvKap q t ϱ N0 ∧ ckvKap q t ϱ N0 ≤ Real.exp ϱ := by
  obtain ⟨h1, h2, -⟩ := ck_const_bounds hp
  unfold ckvKap
  have e1 : 1 ≤ Real.exp (ϱ * (1 - ckMm q t)) := Real.one_le_exp (by nlinarith)
  have e2 : Real.exp (ϱ * (1 - ckMm q t)) ≤ Real.exp ϱ := Real.exp_le_exp.mpr (by nlinarith)
  have p1 : ckMm q t ^ N0 ≤ 1 := pow_le_one₀ h1.le h2.le
  have p0 : 0 ≤ ckMm q t ^ N0 := pow_nonneg h1.le _
  constructor
  · calc ckMm q t ^ N0 = 1 * ckMm q t ^ N0 := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right e1 p0
  · calc _ ≤ Real.exp ϱ * 1 := mul_le_mul e2 p1 p0 (Real.exp_pos _).le
      _ = _ := mul_one _

private lemma ckv_kap_pos {q : ℕ} {t : ℝ} (hp : CKPar q t) (ϱ : ℝ) (N0 : ℕ) :
    0 < ckvKap q t ϱ N0 := by
  have h1 := (ck_const_bounds hp).1
  unfold ckvKap; positivity

private lemma ckv_mm_pow {q : ℕ} {t : ℝ} (hp : CKPar q t) (k : ℕ) :
    ckMm q t ^ k = Real.exp (-(ckEll q t * k)) := by
  have h1 := (ck_const_bounds hp).1
  unfold ckEll
  rw [neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log h1]

private lemma ckv_mp_pow_le {q : ℕ} {t : ℝ} (hp : CKPar q t) (k : ℕ) :
    ckMp t ^ k ≤ Real.exp (ckEll q t * k) := by
  obtain ⟨-, -, h3, -, -, -, h7⟩ := ck_const_bounds hp
  rw [mul_comm, Real.exp_nat_mul]
  calc ckMp t ^ k = Real.exp (Real.log (ckMp t)) ^ k := by rw [Real.exp_log (by linarith)]
    _ ≤ Real.exp (ckEll q t) ^ k :=
        pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr h7.le) _

/-- `|Λ(x)| ≤ e^{2a}` on `[e^{-a}, e^a]`. -/
private lemma ckv_lam_abs_le_exp {a x : ℝ}
    (hx : x ∈ Set.Icc (Real.exp (-a)) (Real.exp a)) : |ckLam x| ≤ Real.exp (2 * a) := by
  obtain ⟨h1, h2⟩ := hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) h1
  have hlog : |Real.log x| ≤ a := by
    rw [abs_le]; constructor
    · have := Real.log_le_log (Real.exp_pos _) h1; rwa [Real.log_exp] at this
    · have := Real.log_le_log hx0 h2; rwa [Real.log_exp] at this
  unfold ckLam
  rw [abs_mul, abs_of_pos hx0]
  have : a ≤ Real.exp a := by linarith [Real.add_one_le_exp a]
  calc x * |Real.log x| ≤ Real.exp a * a := mul_le_mul h2 hlog (abs_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp a * Real.exp a := mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    _ = Real.exp (2 * a) := by rw [← Real.exp_add]; ring_nf

/-- `X_μ(D, N₀) ∈ [e^{-Γ}, e^{Γ}]` with `Γ = 2ϱn + ϱ + ℓ₀(|D| + N₀)`. -/
private lemma ckv_X_mem_exp {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (D : Fin n → ℕ) (N0 : ℕ) :
    ckX q t ϱ μ D N0 ∈ Set.Icc
      (Real.exp (-(2 * ϱ * n + ϱ + ckEll q t * (((∑ v, D v : ℕ) : ℝ) + N0))))
      (Real.exp (2 * ϱ * n + ϱ + ckEll q t * (((∑ v, D v : ℕ) : ℝ) + N0))) := by
  rw [ckv_X_eq]
  obtain ⟨k1, k2⟩ := ckv_kap_mem hp hϱ N0
  obtain ⟨x1, x2⟩ := ckv_Xt_mem hp hϱ hμ D
  have hm0 := (ck_const_bounds hp).1
  have hℓ : 0 < ckEll q t := (ck_const_bounds hp).2.2.2.2.2.1
  have hX0 : 0 ≤ ckvXt q t ϱ μ D := (by positivity : (0:ℝ) ≤ _).trans x1
  constructor
  · have hlow : ckMm q t ^ N0 * (Real.exp (-(2 * ϱ * n)) * ckMm q t ^ (∑ v, D v)) ≤
        ckvKap q t ϱ N0 * ckvXt q t ϱ μ D :=
      mul_le_mul k1 x1 (by positivity) (ckv_kap_pos hp ϱ N0).le
    refine le_trans ?_ hlow
    rw [ckv_mm_pow hp, ckv_mm_pow hp, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : (0 : ℝ) ≤ ckEll q t * N0 := by positivity
    nlinarith
  · have hup : ckvKap q t ϱ N0 * ckvXt q t ϱ μ D ≤
        Real.exp ϱ * (Real.exp (2 * ϱ * n) * Real.exp (ckEll q t * ((∑ v, D v : ℕ) : ℝ))) :=
      mul_le_mul k2 (x2.trans (mul_le_mul_of_nonneg_left (ckv_mp_pow_le hp _)
        (Real.exp_pos _).le)) hX0 (Real.exp_pos _).le
    refine hup.trans ?_
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : (0 : ℝ) ≤ ckEll q t * N0 := by positivity
    nlinarith

/-! ### Product Poisson sums -/

private lemma ckv_hasSum_pow {n : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) {c : ℝ} (hc : 0 ≤ c) :
    HasSum (fun D : Fin n → ℕ => poisPi (fun _ => lam) D * c ^ (∑ v, D v))
      (Real.exp (n * (lam * (c - 1)))) := by
  have H := rs_hasSum_poisPi_mul_prod (lam := fun _ : Fin n => lam) (fun _ => hlam)
    (fun _ k => c ^ k) (fun _ k => pow_nonneg hc k) (fun _ => Real.exp (lam * (c - 1)))
    (fun _ => RSPoisPiAux.hasSum_poisPMF_mul_pow c)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul] at H
  refine H.congr_fun fun D => ?_
  rw [Finset.prod_pow_eq_pow_sum]

private lemma ckv_hasSum_prod {n : ℕ} {lam ϱ : ℝ} (hlam : 0 ≤ lam) (hϱ : 0 ≤ ϱ) {c : ℝ}
    (hc : 0 ≤ c) :
    HasSum (fun z : (Fin n → ℕ) × ℕ =>
        (poisPi (fun _ => lam) z.1 * c ^ (∑ v, z.1 v)) * (poisPMF ϱ z.2 * c ^ z.2))
      (Real.exp (n * (lam * (c - 1))) * Real.exp (ϱ * (c - 1))) := by
  have h1 : HasSum (fun D : Fin n → ℕ => poisPi (fun _ => lam) D * c ^ (∑ v, D v))
      (Real.exp (n * (lam * (c - 1)))) := ckv_hasSum_pow hlam hc
  have h2 : HasSum (fun k : ℕ => poisPMF ϱ k * c ^ k) (Real.exp (ϱ * (c - 1))) :=
    RSPoisPiAux.hasSum_poisPMF_mul_pow c
  have hf0 : 0 ≤ fun D : Fin n → ℕ => poisPi (fun _ => lam) D * c ^ (∑ v, D v) := fun D =>
    mul_nonneg (rs_poisPi_nonneg (fun _ => hlam) D) (pow_nonneg hc _)
  have hg0 : 0 ≤ fun k : ℕ => poisPMF ϱ k * c ^ k := fun k =>
    mul_nonneg (poisPMF_nonneg hϱ k) (pow_nonneg hc _)
  have hs := Summable.mul_of_nonneg h1.summable h2.summable hf0 hg0
  have H := HasSum.mul h1 h2 hs
  exact H

private lemma ckv_exp_split (a b : ℝ) (k m : ℕ) :
    Real.exp (2 * (a + b * ((k : ℝ) + m))) =
      Real.exp (2 * a) * (Real.exp (2 * b) ^ k * Real.exp (2 * b) ^ m) := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; ring_nf

/-- The summand of `Vert` is dominated by a product weight. -/
private lemma ckv_term_abs_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (z : (Fin n → ℕ) × ℕ) :
    |poisPi (fun _ => 2 * ϱ) z.1 * poisPMF ϱ z.2 * ckLam (ckX q t ϱ μ z.1 z.2)| ≤
      Real.exp (2 * (2 * ϱ * n + ϱ)) *
        ((poisPi (fun _ => 2 * ϱ) z.1 * Real.exp (2 * ckEll q t) ^ (∑ v, z.1 v)) *
          (poisPMF ϱ z.2 * Real.exp (2 * ckEll q t) ^ z.2)) := by
  have hℓ : 0 < ckEll q t := (ck_const_bounds hp).2.2.2.2.2.1
  have hP1 : 0 ≤ poisPi (fun _ => 2 * ϱ) z.1 := rs_poisPi_nonneg (fun _ => by positivity) _
  have hP2 : 0 ≤ poisPMF ϱ z.2 := poisPMF_nonneg hϱ _
  have hL := ckv_lam_abs_le_exp (ckv_X_mem_exp hp hϱ hμ z.1 z.2)
  rw [ckv_exp_split] at hL
  rw [abs_mul, abs_mul, abs_of_nonneg hP1, abs_of_nonneg hP2]
  calc poisPi (fun _ => 2 * ϱ) z.1 * poisPMF ϱ z.2 * |ckLam (ckX q t ϱ μ z.1 z.2)| ≤
      poisPi (fun _ => 2 * ϱ) z.1 * poisPMF ϱ z.2 *
        (Real.exp (2 * (2 * ϱ * n + ϱ)) * (Real.exp (2 * ckEll q t) ^ (∑ v, z.1 v) *
          Real.exp (2 * ckEll q t) ^ z.2)) :=
        mul_le_mul_of_nonneg_left hL (mul_nonneg hP1 hP2)
    _ = _ := by ring

-- |Λ(X_μ)| ≤ Γ e^Γ (Lemma 7.1, Integrability)
theorem ck_vert_bdd {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) :
    ∃ B : ℝ, ∀ μ : (Fin n → Fin q) → ℝ, IsPMF μ → |ckVert q t ϱ μ| ≤ B := by
  have hc : (0 : ℝ) ≤ Real.exp (2 * ckEll q t) := (Real.exp_pos _).le
  obtain ⟨B, H⟩ : ∃ B, HasSum (fun z : (Fin n → ℕ) × ℕ => Real.exp (2 * (2 * ϱ * n + ϱ)) *
        ((poisPi (fun _ => 2 * ϱ) z.1 * Real.exp (2 * ckEll q t) ^ (∑ v, z.1 v)) *
          (poisPMF ϱ z.2 * Real.exp (2 * ckEll q t) ^ z.2))) B :=
    ⟨_, (ckv_hasSum_prod (n := n) (by positivity : (0:ℝ) ≤ 2 * ϱ) hϱ hc).mul_left _⟩
  refine ⟨B, fun μ hμ => ?_⟩
  have h := tsum_of_norm_bounded H
    (fun z => (Real.norm_eq_abs _).trans_le (ckv_term_abs_le hp hϱ hμ z))
  rw [Real.norm_eq_abs] at h
  exact h

/-! ### Moments of `|D|` under the product Poisson law -/

private lemma ckv_one_add_le_two_pow (k : ℕ) : 1 + (k : ℝ) ≤ 2 ^ k := by
  have h := one_add_mul_le_pow (a := (1 : ℝ)) (by norm_num) k
  rw [mul_one, one_add_one_eq_two] at h
  exact h

/-- `E (1 + |D|)^j y^{|D|} ≤ exp(n λ (2^j y - 1))`. -/
private lemma ckv_moment {n : ℕ} {lam y : ℝ} (hlam : 0 ≤ lam) (hy : 0 ≤ y) (j : ℕ) :
    Summable (fun D : Fin n → ℕ => poisPi (fun _ => lam) D *
      ((1 + ((∑ v, D v : ℕ) : ℝ)) ^ j * y ^ (∑ v, D v))) ∧
    ∑' D : Fin n → ℕ, poisPi (fun _ => lam) D *
        ((1 + ((∑ v, D v : ℕ) : ℝ)) ^ j * y ^ (∑ v, D v)) ≤
      Real.exp (n * (lam * (2 ^ j * y - 1))) := by
  have H := ckv_hasSum_pow (n := n) hlam (by positivity : (0:ℝ) ≤ 2 ^ j * y)
  have hle : ∀ D : Fin n → ℕ, poisPi (fun _ => lam) D *
      ((1 + ((∑ v, D v : ℕ) : ℝ)) ^ j * y ^ (∑ v, D v)) ≤
        poisPi (fun _ => lam) D * (2 ^ j * y) ^ (∑ v, D v) := by
    intro D
    refine mul_le_mul_of_nonneg_left ?_ (rs_poisPi_nonneg (fun _ => hlam) D)
    rw [mul_pow, ← pow_mul, mul_comm j, pow_mul]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (ckv_one_add_le_two_pow _) j) (pow_nonneg hy _)
  have h0 : ∀ D : Fin n → ℕ, 0 ≤ poisPi (fun _ => lam) D *
      ((1 + ((∑ v, D v : ℕ) : ℝ)) ^ j * y ^ (∑ v, D v)) :=
    fun D => mul_nonneg (rs_poisPi_nonneg (fun _ => hlam) D) (by positivity)
  have hs := Summable.of_nonneg_of_le h0 hle H.summable
  exact ⟨hs, (Summable.tsum_le_tsum hle hs H.summable).trans H.tsum_eq.le⟩

/-! ### Step 0: eliminating the loop count `N₀` -/

private lemma ckv_lam_kap_le {q : ℕ} {t : ℝ} (hp : CKPar q t) (ϱ : ℝ) (N0 : ℕ) {x : ℝ}
    (hx : 0 ≤ x) :
    ckLam (ckvKap q t ϱ N0 * x) ≤ ckvKap q t ϱ N0 * (ckLam x + ϱ * (1 - ckMm q t) * x) := by
  obtain ⟨h1, h2, -⟩ := ck_const_bounds hp
  have hk := ckv_kap_pos hp ϱ N0
  rcases hx.eq_or_lt with rfl | hx'
  · simp [ckLam]
  unfold ckLam
  rw [Real.log_mul hk.ne' hx'.ne']
  have hlogk : Real.log (ckvKap q t ϱ N0) ≤ ϱ * (1 - ckMm q t) := by
    unfold ckvKap
    rw [Real.log_mul (Real.exp_pos _).ne' (pow_pos h1 _).ne', Real.log_exp, Real.log_pow]
    have h3 : Real.log (ckMm q t) < 0 := Real.log_neg h1 h2
    have h4 : (N0 : ℝ) * Real.log (ckMm q t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) h3.le
    linarith
  have h5 := mul_le_mul_of_nonneg_left hlogk (mul_nonneg hk.le hx)
  linarith

private lemma ckv_Xt_mem_exp {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (D : Fin n → ℕ) {a : ℝ} (ha : 2 * ϱ * n ≤ a) :
    ckvXt q t ϱ μ D ∈ Set.Icc (Real.exp (-(a + ckEll q t * ((∑ v, D v : ℕ) : ℝ))))
      (Real.exp (a + ckEll q t * ((∑ v, D v : ℕ) : ℝ))) := by
  obtain ⟨x1, x2⟩ := ckv_Xt_mem hp hϱ hμ D
  constructor
  · refine le_trans ?_ x1
    rw [ckv_mm_pow hp, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  · refine x2.trans ?_
    calc Real.exp (2 * ϱ * n) * ckMp t ^ (∑ v, D v) ≤
        Real.exp (2 * ϱ * n) * Real.exp (ckEll q t * ((∑ v, D v : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (ckv_mp_pow_le hp _) (Real.exp_pos _).le
      _ ≤ _ := by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)

/-- Summability of the integrand of Step 0. -/
private lemma ckv_summable_F {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) :
    Summable fun D : Fin n → ℕ => poisPi (fun _ => 2 * ϱ) D *
      (ckLam (ckvXt q t ϱ μ D) + ϱ * (1 - ckMm q t) * ckvXt q t ϱ μ D) := by
  have h2ϱ : (0:ℝ) ≤ 2 * ϱ := by positivity
  obtain ⟨hm0, hm1, -⟩ := ck_const_bounds hp
  have hℓ : 0 < ckEll q t := (ck_const_bounds hp).2.2.2.2.2.1
  have H := rs_summable_poisPi_of_abs_le (lam := fun _ : Fin n => 2 * ϱ) (fun _ => h2ϱ)
    (f := fun D => ckLam (ckvXt q t ϱ μ D) + ϱ * (1 - ckMm q t) * ckvXt q t ϱ μ D)
    (A := (1 + ϱ) * Real.exp (2 * (2 * ϱ * n))) (c := Real.exp (2 * ckEll q t))
    (Real.exp_pos _).le (fun D => ?_)
  · exact H
  have hX := ckv_Xt_mem_exp hp hϱ hμ D (le_refl (2 * ϱ * n))
  have hX0 : 0 ≤ ckvXt q t ϱ μ D := (Real.exp_pos _).le.trans hX.1
  have hΛ := ckv_lam_abs_le_exp hX
  have hk : (0:ℝ) ≤ ((∑ v, D v : ℕ) : ℝ) := Nat.cast_nonneg _
  have hE : Real.exp (2 * ϱ * n + ckEll q t * ((∑ v, D v : ℕ) : ℝ)) ≤
      Real.exp (2 * (2 * ϱ * n + ckEll q t * ((∑ v, D v : ℕ) : ℝ))) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hsplit : Real.exp (2 * (2 * ϱ * n + ckEll q t * ((∑ v, D v : ℕ) : ℝ))) =
      Real.exp (2 * (2 * ϱ * n)) * Real.exp (2 * ckEll q t) ^ (∑ v, D v) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
  have h1m : 0 ≤ 1 - ckMm q t := by linarith
  have h1m' : 1 - ckMm q t ≤ 1 := by linarith
  calc |ckLam (ckvXt q t ϱ μ D) + ϱ * (1 - ckMm q t) * ckvXt q t ϱ μ D|
      ≤ |ckLam (ckvXt q t ϱ μ D)| + |ϱ * (1 - ckMm q t) * ckvXt q t ϱ μ D| := abs_add_le _ _
    _ ≤ Real.exp (2 * (2 * ϱ * n + ckEll q t * ((∑ v, D v : ℕ) : ℝ))) +
        ϱ * Real.exp (2 * (2 * ϱ * n + ckEll q t * ((∑ v, D v : ℕ) : ℝ))) := by
      refine add_le_add hΛ ?_
      rw [abs_of_nonneg (by positivity)]
      calc ϱ * (1 - ckMm q t) * ckvXt q t ϱ μ D ≤ ϱ * 1 * ckvXt q t ϱ μ D := by
            gcongr
        _ ≤ ϱ * 1 * Real.exp (2 * (2 * ϱ * n + ckEll q t * ((∑ v, D v : ℕ) : ℝ))) := by
            gcongr; exact hX.2.trans hE
        _ = _ := by ring
    _ = (1 + ϱ) * Real.exp (2 * (2 * ϱ * n)) * Real.exp (2 * ckEll q t) ^ (∑ v, D v) := by
      rw [hsplit]; ring

/-- `Vert(μ) ≤ E_D [Λ(X̃) + ϱ(1 - m₋) X̃]`: the loop count is integrated out exactly
(`E κ(N₀) = 1`) and `log κ ≤ ϱ(1 - m₋)`. -/
private lemma ckv_vert_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) :
    ckVert q t ϱ μ ≤ ∑' D, poisPi (fun _ => 2 * ϱ) D *
      (ckLam (ckvXt q t ϱ μ D) + ϱ * (1 - ckMm q t) * ckvXt q t ϱ μ D) := by
  have h2ϱ : (0:ℝ) ≤ 2 * ϱ := by positivity
  have hP : ∀ D : Fin n → ℕ, 0 ≤ poisPi (fun _ => 2 * ϱ) D := rs_poisPi_nonneg (fun _ => h2ϱ)
  obtain ⟨hm0, hm1, -⟩ := ck_const_bounds hp
  have hℓ : 0 < ckEll q t := (ck_const_bounds hp).2.2.2.2.2.1
  set F : (Fin n → ℕ) → ℝ := fun D => poisPi (fun _ => 2 * ϱ) D *
      (ckLam (ckvXt q t ϱ μ D) + ϱ * (1 - ckMm q t) * ckvXt q t ϱ μ D) with hFdef
  set G : ℕ → ℝ := fun k => poisPMF ϱ k * ckvKap q t ϱ k with hGdef
  have hG0 : ∀ k, 0 ≤ G k := fun k => mul_nonneg (poisPMF_nonneg hϱ k) (ckv_kap_pos hp ϱ k).le
  have hG : HasSum G 1 := by
    have h := (RSPoisPiAux.hasSum_poisPMF_mul_pow (lam := ϱ) (ckMm q t)).mul_left
      (Real.exp (ϱ * (1 - ckMm q t)))
    rw [← Real.exp_add, (by ring : ϱ * (1 - ckMm q t) + ϱ * (ckMm q t - 1) = 0),
      Real.exp_zero] at h
    refine h.congr_fun fun k => ?_
    simp only [hGdef, ckvKap]; ring
  have hF : Summable F := ckv_summable_F hp hϱ hμ
  have hFn : Summable fun D => ‖F D‖ := by simpa only [Real.norm_eq_abs] using hF.abs
  have hGn : Summable fun k => ‖G k‖ := by
    refine hG.summable.congr fun k => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hG0 k)]
  have hRHS := summable_mul_of_summable_norm hFn hGn
  have hLHS : Summable fun z : (Fin n → ℕ) × ℕ =>
      poisPi (fun _ => 2 * ϱ) z.1 * poisPMF ϱ z.2 * ckLam (ckX q t ϱ μ z.1 z.2) := by
    have H := (ckv_hasSum_prod (n := n) h2ϱ hϱ (Real.exp_pos (2 * ckEll q t)).le).mul_left
      (Real.exp (2 * (2 * ϱ * n + ϱ)))
    exact Summable.of_norm_bounded H.summable fun z =>
      (Real.norm_eq_abs _).trans_le (ckv_term_abs_le hp hϱ hμ z)
  have hpt : ∀ z : (Fin n → ℕ) × ℕ, poisPi (fun _ => 2 * ϱ) z.1 * poisPMF ϱ z.2 *
      ckLam (ckX q t ϱ μ z.1 z.2) ≤ F z.1 * G z.2 := by
    intro z
    rw [ckv_X_eq]
    have hX0 : 0 ≤ ckvXt q t ϱ μ z.1 :=
      (Real.exp_pos _).le.trans (ckv_Xt_mem_exp hp hϱ hμ z.1 (le_refl (2 * ϱ * n))).1
    have h := ckv_lam_kap_le hp ϱ z.2 hX0
    calc _ ≤ poisPi (fun _ => 2 * ϱ) z.1 * poisPMF ϱ z.2 * (ckvKap q t ϱ z.2 *
          (ckLam (ckvXt q t ϱ μ z.1) + ϱ * (1 - ckMm q t) * ckvXt q t ϱ μ z.1)) :=
          mul_le_mul_of_nonneg_left h (mul_nonneg (hP _) (poisPMF_nonneg hϱ _))
      _ = F z.1 * G z.2 := by simp only [hFdef, hGdef]; ring
  have hprod := tsum_mul_tsum_of_summable_norm hFn hGn
  calc ckVert q t ϱ μ = ∑' z : (Fin n → ℕ) × ℕ,
        poisPi (fun _ => 2 * ϱ) z.1 * poisPMF ϱ z.2 * ckLam (ckX q t ϱ μ z.1 z.2) := rfl
    _ ≤ ∑' z : (Fin n → ℕ) × ℕ, F z.1 * G z.2 := Summable.tsum_le_tsum hpt hLHS hRHS
    _ = (∑' D, F D) * ∑' k, G k := hprod.symm
    _ = ∑' D, F D := by rw [hG.tsum_eq, mul_one]

/-! ### The comparison quantities `X₁` and `Y` -/

/-- `Y(D) = q⁻¹ ∑_c ∏_v (M μ_v)_c^{D_v}` (the Bethe vertex variable at the marginals). -/
private def ckvY (q : ℕ) (t : ℝ) {n : ℕ} (μ : (Fin n → Fin q) → ℝ) (D : Fin n → ℕ) : ℝ :=
  (q : ℝ)⁻¹ * ∑ c, ∏ v, betheMvec q t (ckMarg μ v) c ^ D v

/-- `X₁(D) = q⁻¹ ∑_c ⟨∏_v M(τ_v, c)^{D_v}⟩_μ` (no compensator). -/
private def ckvX1 (q : ℕ) (t : ℝ) {n : ℕ} (μ : (Fin n → Fin q) → ℝ) (D : Fin n → ℕ) : ℝ :=
  (q : ℝ)⁻¹ * ∑ c : Fin q, ∑ τ, μ τ * ∏ v, rsM q t (τ v) c ^ D v

private lemma ckv_Y_mem {q n : ℕ} {t : ℝ} (hp : CKPar q t) {μ : (Fin n → Fin q) → ℝ}
    (hμ : IsPMF μ) (D : Fin n → ℕ) :
    ckMm q t ^ (∑ v, D v) ≤ ckvY q t μ D ∧ ckvY q t μ D ≤ ckMp t ^ (∑ v, D v) := by
  have hq : q ≠ 0 := by have := hp.two_le; omega
  have hm0 := (ck_const_bounds hp).1
  unfold ckvY
  exact ckv_avgq_mem hq _ fun c => ckv_prod_pow_mem hm0.le _
    (fun v => ck_betheMvec_mem hp (ck_marg_mem hμ v) c) D

private lemma ckv_X1_mem {q n : ℕ} {t : ℝ} (hp : CKPar q t) {μ : (Fin n → Fin q) → ℝ}
    (hμ : IsPMF μ) (D : Fin n → ℕ) :
    ckMm q t ^ (∑ v, D v) ≤ ckvX1 q t μ D ∧ ckvX1 q t μ D ≤ ckMp t ^ (∑ v, D v) := by
  have hq : q ≠ 0 := by have := hp.two_le; omega
  have hm0 := (ck_const_bounds hp).1
  unfold ckvX1
  exact ckv_avgq_mem hq _ fun c => ckv_avgμ_mem hμ _ fun τ => ckv_prod_pow_mem hm0.le _
    (fun v => ck_rsM_mem hp _ _) D

private lemma ckv_Y_mem_exp {q n : ℕ} {t : ℝ} (hp : CKPar q t) {μ : (Fin n → Fin q) → ℝ}
    (hμ : IsPMF μ) (D : Fin n → ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ckvY q t μ D ∈ Set.Icc (Real.exp (-(a + ckEll q t * ((∑ v, D v : ℕ) : ℝ))))
      (Real.exp (a + ckEll q t * ((∑ v, D v : ℕ) : ℝ))) := by
  obtain ⟨y1, y2⟩ := ckv_Y_mem hp hμ D
  constructor
  · refine le_trans ?_ y1
    rw [ckv_mm_pow hp]
    exact Real.exp_le_exp.mpr (by linarith)
  · refine y2.trans ((ckv_mp_pow_le hp _).trans ?_)
    exact Real.exp_le_exp.mpr (by linarith)

/-! ### Step 1: the compensators `e^{δ_c}` -/

private lemma ckv_abs_exp_sub_one_le (x : ℝ) : |Real.exp x - 1| ≤ |x| * Real.exp |x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_of_nonneg (by linarith [Real.add_one_le_exp x])]
    have h := Real.add_one_le_exp (-x)
    have he : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [mul_le_mul_of_nonneg_left h (Real.exp_pos x).le, Real.exp_pos x]
  · rw [abs_of_nonpos hx, abs_of_nonpos (by linarith [Real.exp_le_one_iff.mpr hx])]
    have h1 := Real.add_one_le_exp x
    have h2 : 1 ≤ Real.exp (-x) := Real.one_le_exp (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h2 (neg_nonneg.mpr hx)]

private lemma ckv_abs_avg_le {q n : ℕ} (hq : q ≠ 0) {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (h : Fin q → (Fin n → Fin q) → ℝ) (B : (Fin n → Fin q) → ℝ)
    (hh : ∀ c τ, |h c τ| ≤ B τ) :
    |(q : ℝ)⁻¹ * ∑ c, ∑ τ, μ τ * h c τ| ≤ ∑ τ, μ τ * B τ := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  rw [abs_mul, abs_of_pos (inv_pos.mpr hq')]
  have h1 : |∑ c, ∑ τ, μ τ * h c τ| ≤ ∑ _c : Fin q, ∑ τ, μ τ * B τ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
    rw [abs_mul, abs_of_nonneg (hμ.1 τ)]
    exact mul_le_mul_of_nonneg_left (hh c τ) (hμ.1 τ)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  calc (q : ℝ)⁻¹ * |∑ c, ∑ τ, μ τ * h c τ| ≤ (q : ℝ)⁻¹ * (q * ∑ τ, μ τ * B τ) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hq'.le)
    _ = ∑ τ, μ τ * B τ := by field_simp

/-- `|δ_c(τ)| ≤ s |t| q ‖λ_τ - u‖₂` when `2ϱn ≤ s`. -/
private lemma ckv_delta_dev {q n : ℕ} {t : ℝ} (hp : CKPar q t) {s ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (hϱn : 2 * ϱ * n ≤ s) (τ : Fin n → Fin q) (c : Fin q) :
    |-(2 * ϱ) * ∑ v, (rsM q t (τ v) c - 1)| ≤ s * |t| * q * Real.sqrt (rsDevSq τ) := by
  have hq : q ≠ 0 := by have := hp.two_le; omega
  rw [ck_sum_rsM_sub_one hq t τ c]
  have hdev : |colorFrac τ c - (q : ℝ)⁻¹| ≤ Real.sqrt (rsDevSq τ) := by
    apply Real.abs_le_sqrt
    unfold rsDevSq
    rw [← one_div]
    exact Finset.single_le_sum (f := fun a => (colorFrac τ a - 1 / (q : ℝ)) ^ 2)
      (fun a _ => sq_nonneg _) (Finset.mem_univ c)
  have e : |-(2 * ϱ) * (t * q * n * (colorFrac τ c - (q : ℝ)⁻¹))| =
      (2 * ϱ * n) * (|t| * q * |colorFrac τ c - (q : ℝ)⁻¹|) := by
    rw [show -(2 * ϱ) * (t * q * n * (colorFrac τ c - (q : ℝ)⁻¹)) =
        -((2 * ϱ * n) * ((q : ℝ) * (t * (colorFrac τ c - (q : ℝ)⁻¹)))) by ring]
    rw [abs_neg, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * ϱ * n), abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ q), abs_mul]
    ring
  rw [e]
  calc (2 * ϱ * n) * (|t| * q * |colorFrac τ c - (q : ℝ)⁻¹|) ≤
      s * (|t| * q * Real.sqrt (rsDevSq τ)) :=
        mul_le_mul hϱn (mul_le_mul_of_nonneg_left hdev (by positivity)) (by positivity)
          (le_trans (by positivity) hϱn)
    _ = s * |t| * q * Real.sqrt (rsDevSq τ) := by ring

/-- Step 1: `|X̃ - X₁| ≤ e^s (s|t|q) m₊^{|D|} dev(μ)`. -/
private lemma ckv_Xt_X1_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) {s ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (hϱn : 2 * ϱ * n ≤ s) {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (D : Fin n → ℕ) :
    |ckvXt q t ϱ μ D - ckvX1 q t μ D| ≤
      Real.exp s * (s * |t| * q) * ckMp t ^ (∑ v, D v) * ckDev μ := by
  have hq : q ≠ 0 := by have := hp.two_le; omega
  have hm0 := (ck_const_bounds hp).1
  have hs : 0 ≤ s := le_trans (by positivity) hϱn
  have e : ckvXt q t ϱ μ D - ckvX1 q t μ D = (q : ℝ)⁻¹ * ∑ c, ∑ τ, μ τ *
      ((Real.exp (-(2 * ϱ) * ∑ v, (rsM q t (τ v) c - 1)) - 1) * ∏ v, rsM q t (τ v) c ^ D v) := by
    unfold ckvXt ckvX1
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [e]
  refine (ckv_abs_avg_le hq hμ _ (fun τ => Real.exp s * (s * |t| * q) * ckMp t ^ (∑ v, D v) *
    Real.sqrt (rsDevSq τ)) fun c τ => ?_).trans_eq ?_
  · have hd := ckv_delta_abs hp hϱ τ c
    have hdd := ckv_delta_dev hp hϱ hϱn τ c
    have hPi := ckv_prod_pow_mem hm0.le (fun v => rsM q t (τ v) c) (fun v => ck_rsM_mem hp _ _) D
    have hPi0 : 0 ≤ ∏ v, rsM q t (τ v) c ^ D v := (pow_nonneg hm0.le _).trans hPi.1
    rw [abs_mul, abs_of_nonneg hPi0]
    have h1 := ckv_abs_exp_sub_one_le (-(2 * ϱ) * ∑ v, (rsM q t (τ v) c - 1))
    have h2 : |Real.exp (-(2 * ϱ) * ∑ v, (rsM q t (τ v) c - 1)) - 1| ≤
        s * |t| * q * Real.sqrt (rsDevSq τ) * Real.exp s :=
      h1.trans (mul_le_mul hdd (Real.exp_le_exp.mpr (hd.trans hϱn)) (Real.exp_pos _).le
        (by positivity))
    calc |Real.exp (-(2 * ϱ) * ∑ v, (rsM q t (τ v) c - 1)) - 1| * ∏ v, rsM q t (τ v) c ^ D v
        ≤ (s * |t| * q * Real.sqrt (rsDevSq τ) * Real.exp s) * ckMp t ^ (∑ v, D v) :=
          mul_le_mul h2 hPi.2 hPi0 (by positivity)
      _ = _ := by ring
  · unfold ckDev
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by ring

/-! ### Step 2/3: decorrelation of `X₁` against the product of marginals -/

/-- The support `W = {v : D_v ≥ 1}`. -/
private def ckvW {n : ℕ} (D : Fin n → ℕ) : Finset (Fin n) := Finset.univ.filter fun v => D v ≠ 0

/-- `g(D) = 1_{D ∉ S₁} + ∑_{w ∈ W} √I(τ_w; τ_{W∖w})`. -/
private def ckvG {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) (D : Fin n → ℕ) : ℝ :=
  (if ∀ v, D v ≤ 1 then 0 else 1) +
    ∑ w ∈ ckvW D, Real.sqrt (ckMI μ {w} ((ckvW D).erase w) ∅)

private lemma ckv_rsM_symm (q : ℕ) (t : ℝ) (a b : Fin q) : rsM q t a b = rsM q t b a := by
  by_cases h : a = b
  · rw [h]
  · simp only [rsM, rsA, h, Ne.symm h, if_false]

private lemma ckv_betheMvec_marg {n q : ℕ} (t : ℝ) (μ : (Fin n → Fin q) → ℝ) (w : Fin n)
    (c : Fin q) : betheMvec q t (ckMarg μ w) c = ∑ τ, μ τ * rsM q t (τ w) c := by
  unfold betheMvec ckMarg
  calc ∑ b, rsM q t c b * ∑ τ with τ w = b, μ τ =
      ∑ b, ∑ τ with τ w = b, μ τ * rsM q t (τ w) c := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ hτ => ?_
        rw [(Finset.mem_filter.mp hτ).2, ckv_rsM_symm]; ring
    _ = ∑ τ, μ τ * rsM q t (τ w) c := Finset.sum_fiberwise _ _ _

private lemma ckv_prod_pow_of_le_one {n : ℕ} (x : Fin n → ℝ) (D : Fin n → ℕ)
    (hD : ∀ v, D v ≤ 1) : ∏ v, x v ^ D v = ∏ w ∈ ckvW D, x w := by
  unfold ckvW
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun v _ => ?_
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hD v) with h | h <;> simp [h]

private lemma ckv_card_W_le {n : ℕ} (D : Fin n → ℕ) : (ckvW D).card ≤ ∑ v, D v := by
  unfold ckvW
  calc (Finset.univ.filter fun v => D v ≠ 0).card =
      ∑ v ∈ Finset.univ.filter (fun v => D v ≠ 0), 1 := Finset.card_eq_sum_ones _
    _ ≤ ∑ v ∈ Finset.univ.filter (fun v => D v ≠ 0), D v :=
        Finset.sum_le_sum fun v hv => Nat.one_le_iff_ne_zero.mpr (Finset.mem_filter.mp hv).2
    _ ≤ ∑ v, D v := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

private lemma ckv_G_nonneg {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) (D : Fin n → ℕ) :
    0 ≤ ckvG μ D := by
  unfold ckvG
  refine add_nonneg (by split_ifs <;> norm_num) (Finset.sum_nonneg fun w _ => Real.sqrt_nonneg _)

/-- Steps 2 and 3: `|X₁ - Y| ≤ 2 m₊^{|D|} g(D)`. -/
private lemma ckv_X1_Y_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) {μ : (Fin n → Fin q) → ℝ}
    (hμ : IsPMF μ) (D : Fin n → ℕ) :
    |ckvX1 q t μ D - ckvY q t μ D| ≤ 2 * ckMp t ^ (∑ v, D v) * ckvG μ D := by
  have hq : q ≠ 0 := by have := hp.two_le; omega
  have hq' : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  obtain ⟨hm0, -, hm1, -⟩ := ck_const_bounds hp
  have hSig : 0 ≤ ∑ w ∈ ckvW D, Real.sqrt (ckMI μ {w} ((ckvW D).erase w) ∅) :=
    Finset.sum_nonneg fun w _ => Real.sqrt_nonneg _
  have hP0 : 0 ≤ ckMp t ^ (∑ v, D v) := pow_nonneg (by linarith) _
  by_cases hS : ∀ v, D v ≤ 1
  · have hG : ckvG μ D = ∑ w ∈ ckvW D, Real.sqrt (ckMI μ {w} ((ckvW D).erase w) ∅) := by
      unfold ckvG; rw [if_pos hS, zero_add]
    rw [hG]
    set B := 2 * ckMp t ^ (ckvW D).card *
      ∑ w ∈ ckvW D, Real.sqrt (ckMI μ {w} ((ckvW D).erase w) ∅) with hB
    have key : ∀ c : Fin q, |∑ τ, μ τ * ∏ v, rsM q t (τ v) c ^ D v -
        ∏ v, betheMvec q t (ckMarg μ v) c ^ D v| ≤ B := by
      intro c
      have e1 : ∀ τ : Fin n → Fin q, ∏ v, rsM q t (τ v) c ^ D v = ∏ w ∈ ckvW D, rsM q t (τ w) c :=
        fun τ => ckv_prod_pow_of_le_one (fun v => rsM q t (τ v) c) D hS
      have e2 : ∏ v, betheMvec q t (ckMarg μ v) c ^ D v =
          ∏ w ∈ ckvW D, ∑ τ, μ τ * rsM q t (τ w) c := by
        rw [ckv_prod_pow_of_le_one (fun v => betheMvec q t (ckMarg μ v) c) D hS]
        exact Finset.prod_congr rfl fun w _ => ckv_betheMvec_marg t μ w c
      simp_rw [e1]
      rw [e2]
      exact ck_prod_decorr hμ (ckvW D) (fun _ a => rsM q t a c)
        (fun _ a => ⟨(ckv_rsM_pos hp a c).le, (ck_rsM_mem hp a c).2⟩)
    have hBle : B ≤ 2 * ckMp t ^ (∑ v, D v) *
        ∑ w ∈ ckvW D, Real.sqrt (ckMI μ {w} ((ckvW D).erase w) ∅) := by
      rw [hB]
      gcongr
      · linarith
      · exact ckv_card_W_le D
    refine le_trans ?_ hBle
    unfold ckvX1 ckvY
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (inv_pos.mpr hq')]
    calc (q : ℝ)⁻¹ * |∑ c, (∑ τ, μ τ * ∏ v, rsM q t (τ v) c ^ D v -
          ∏ v, betheMvec q t (ckMarg μ v) c ^ D v)| ≤ (q : ℝ)⁻¹ * ∑ _c : Fin q, B :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun c _ => key c)) (inv_nonneg.mpr hq'.le)
      _ = B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  · have hG : ckvG μ D = 1 + ∑ w ∈ ckvW D, Real.sqrt (ckMI μ {w} ((ckvW D).erase w) ∅) := by
      unfold ckvG; rw [if_neg hS]
    rw [hG]
    obtain ⟨x1, x2⟩ := ckv_X1_mem hp hμ D
    obtain ⟨y1, y2⟩ := ckv_Y_mem hp hμ D
    have hL0 : 0 ≤ ckMm q t ^ (∑ v, D v) := pow_nonneg hm0.le _
    have hd : |ckvX1 q t μ D - ckvY q t μ D| ≤ ckMp t ^ (∑ v, D v) := by
      rw [abs_le]; constructor <;> linarith
    refine hd.trans ?_
    nlinarith

/-- The `Λ`-Lipschitz step: `|Λ(X̃) - Λ(Y)| ≤ c₂ (1 + |D|) |X̃ - Y|`. -/
private lemma ckv_lam_diff_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) {s ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (hϱn : 2 * ϱ * n ≤ s) {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (D : Fin n → ℕ) :
    |ckLam (ckvXt q t ϱ μ D) - ckLam (ckvY q t μ D)| ≤
      (1 + s + ckEll q t) * (1 + ((∑ v, D v : ℕ) : ℝ)) *
        |ckvXt q t ϱ μ D - ckvY q t μ D| := by
  have hs : 0 ≤ s := le_trans (by positivity) hϱn
  have hℓ : 0 < ckEll q t := (ck_const_bounds hp).2.2.2.2.2.1
  have hk : (0:ℝ) ≤ ((∑ v, D v : ℕ) : ℝ) := Nat.cast_nonneg _
  have hΓ : 0 ≤ s + ckEll q t * ((∑ v, D v : ℕ) : ℝ) := by positivity
  have hX := ckv_Xt_mem_exp hp hϱ hμ D hϱn
  have hY := ckv_Y_mem_exp hp hμ D hs
  have h := ck_lam_lip hΓ hX hY
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  nlinarith

/-- Pointwise comparison: `Λ(X̃) + ϱ(1 - m₋)X̃ ≤ Λ(Y) + H(D)`. -/
private lemma ckv_pt {q n : ℕ} {t : ℝ} (hp : CKPar q t) {s ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (hϱn : 2 * ϱ * n ≤ s) {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (D : Fin n → ℕ) :
    ckLam (ckvXt q t ϱ μ D) + ϱ * (1 - ckMm q t) * ckvXt q t ϱ μ D ≤
      ckLam (ckvY q t μ D) +
        ((1 + ((∑ v, D v : ℕ) : ℝ)) * ckMp t ^ (∑ v, D v) *
            (ϱ * Real.exp s + (1 + s + ckEll q t) * Real.exp s * (s * |t| * q) * ckDev μ) +
          2 * (1 + s + ckEll q t) *
            ((1 + ((∑ v, D v : ℕ) : ℝ)) * ckMp t ^ (∑ v, D v) * ckvG μ D)) := by
  have hs : 0 ≤ s := le_trans (by positivity) hϱn
  obtain ⟨hm0, hm1, hp1, -⟩ := ck_const_bounds hp
  have hℓ : 0 < ckEll q t := (ck_const_bounds hp).2.2.2.2.2.1
  set k : ℝ := ((∑ v, D v : ℕ) : ℝ) with hkdef
  have hk : 0 ≤ k := Nat.cast_nonneg _
  set P := ckMp t ^ (∑ v, D v) with hPdef
  have hP : 0 ≤ P := pow_nonneg (by linarith) _
  set c₂ := 1 + s + ckEll q t with hc₂
  have hc₂0 : 0 ≤ c₂ := by positivity
  set K := s * |t| * q with hK
  have hK0 : 0 ≤ K := by positivity
  have hdev : 0 ≤ ckDev μ := Finset.sum_nonneg fun τ _ => mul_nonneg (hμ.1 τ) (Real.sqrt_nonneg _)
  have hA := ckv_lam_diff_le hp hϱ hϱn hμ D
  have h1 := ckv_Xt_X1_le hp hϱ hϱn hμ D
  have h2 := ckv_X1_Y_le hp hμ D
  have htri : |ckvXt q t ϱ μ D - ckvY q t μ D| ≤
      |ckvXt q t ϱ μ D - ckvX1 q t μ D| + |ckvX1 q t μ D - ckvY q t μ D| := abs_sub_le _ _ _
  have hB : c₂ * (1 + k) * |ckvXt q t ϱ μ D - ckvY q t μ D| ≤
      c₂ * (1 + k) * (Real.exp s * K * P * ckDev μ + 2 * P * ckvG μ D) :=
    mul_le_mul_of_nonneg_left (htri.trans (add_le_add h1 h2)) (by positivity)
  have hX := ckv_Xt_mem hp hϱ hμ D
  have hX0 : 0 ≤ ckvXt q t ϱ μ D := (by positivity : (0:ℝ) ≤ _).trans hX.1
  have hXup : ckvXt q t ϱ μ D ≤ Real.exp s * P :=
    hX.2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hϱn) hP)
  have hC : ϱ * (1 - ckMm q t) * ckvXt q t ϱ μ D ≤ ϱ * Real.exp s * P * (1 + k) := by
    have e1 : ϱ * (1 - ckMm q t) * ckvXt q t ϱ μ D ≤ ϱ * 1 * ckvXt q t ϱ μ D := by
      gcongr; linarith
    have e2 : ϱ * 1 * ckvXt q t ϱ μ D ≤ ϱ * 1 * (Real.exp s * P) := by gcongr
    have e3 : ϱ * 1 * (Real.exp s * P) ≤ ϱ * Real.exp s * P * (1 + k) := by
      have : 0 ≤ ϱ * Real.exp s * P := by positivity
      nlinarith
    linarith
  have hD := le_abs_self (ckLam (ckvXt q t ϱ μ D) - ckLam (ckvY q t μ D))
  calc ckLam (ckvXt q t ϱ μ D) + ϱ * (1 - ckMm q t) * ckvXt q t ϱ μ D ≤
      ckLam (ckvY q t μ D) + (c₂ * (1 + k) * (Real.exp s * K * P * ckDev μ + 2 * P * ckvG μ D) +
        ϱ * Real.exp s * P * (1 + k)) := by linarith
    _ = _ := by ring

/-! ### Expectations of the decorrelation error -/

/-- Cauchy–Schwarz for nonnegative weighted `tsum`s (as `rs_tsum_mul_le_sqrt`). -/
private lemma ckv_tsum_mul_le_sqrt {α : Type*} {w f g : α → ℝ} (hw : ∀ a, 0 ≤ w a)
    (hf : ∀ a, 0 ≤ f a) (hg : ∀ a, 0 ≤ g a) (hf2 : Summable fun a => w a * f a ^ 2)
    (hg2 : Summable fun a => w a * g a ^ 2) :
    ∑' a, w a * (f a * g a) ≤
      Real.sqrt (∑' a, w a * f a ^ 2) * Real.sqrt (∑' a, w a * g a ^ 2) := by
  have e1 : ∀ a, (Real.sqrt (w a) * f a) ^ (2 : ℝ) = w a * f a ^ 2 := fun a => by
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (hw a)]
  have e2 : ∀ a, (Real.sqrt (w a) * g a) ^ (2 : ℝ) = w a * g a ^ 2 := fun a => by
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (hw a)]
  have e3 : ∀ a, Real.sqrt (w a) * f a * (Real.sqrt (w a) * g a) = w a * (f a * g a) :=
    fun a => by
      have := Real.mul_self_sqrt (hw a)
      calc Real.sqrt (w a) * f a * (Real.sqrt (w a) * g a)
          = (Real.sqrt (w a) * Real.sqrt (w a)) * (f a * g a) := by ring
        _ = w a * (f a * g a) := by rw [this]
  have key := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (f := fun a => Real.sqrt (w a) * f a) (g := fun a => Real.sqrt (w a) * g a)
    (fun a => mul_nonneg (Real.sqrt_nonneg _) (hf a))
    (fun a => mul_nonneg (Real.sqrt_nonneg _) (hg a))
    (by simpa only [e1] using hf2) (by simpa only [e2] using hg2)
  simp only [e1, e2, e3] at key
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  convert key using 3

/-- One coordinate of the product Poisson law. -/
private lemma ckv_marg_hasSum {n : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) (v : Fin n) (φ : ℕ → ℝ)
    (hφ : ∀ k, 0 ≤ φ k) {a : ℝ} (ha : HasSum (fun k => poisPMF lam k * φ k) a) :
    HasSum (fun D : Fin n → ℕ => poisPi (fun _ => lam) D * φ (D v)) a := by
  have H := rs_hasSum_poisPi_mul_prod (lam := fun _ : Fin n => lam) (fun _ => hlam)
    (fun u k => if u = v then φ k else 1)
    (fun u k => by by_cases h : u = v <;> simp [h, hφ k])
    (fun u => if u = v then a else 1)
    (fun u => by
      by_cases h : u = v
      · simp only [if_pos h]; exact ha
      · simp only [if_neg h, mul_one]; exact hasSum_poisPMF hlam)
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true] at H
  exact H

private lemma ckv_tail {lam : ℝ} (hlam : 0 ≤ lam) :
    HasSum (fun k => poisPMF lam k * (if 2 ≤ k then (1 : ℝ) else 0))
      (∑' k : ℕ, (if 2 ≤ k then poisPMF lam k else 0)) ∧
    ∑' k : ℕ, (if 2 ≤ k then poisPMF lam k else 0) ≤ lam ^ 2 / 2 := by
  have hs : Summable fun k : ℕ => if 2 ≤ k then poisPMF lam k else 0 := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (hasSum_poisPMF hlam).summable
    · split_ifs
      · exact poisPMF_nonneg hlam k
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact poisPMF_nonneg hlam k
  refine ⟨hs.hasSum.congr_fun fun k => ?_, ck_pois_tail_two hlam⟩
  split_ifs <;> simp

private lemma ckv_e_le {n : ℕ} (D : Fin n → ℕ) :
    (if ∀ v, D v ≤ 1 then (0:ℝ) else 1) ≤ ∑ v, (if 2 ≤ D v then (1:ℝ) else 0) := by
  have h0 : ∀ v, (0:ℝ) ≤ if 2 ≤ D v then (1:ℝ) else 0 := fun v => by split_ifs <;> norm_num
  split_ifs with h
  · exact Finset.sum_nonneg fun v _ => h0 v
  · simp only [not_forall, not_le] at h
    obtain ⟨v, hv⟩ := h
    have h1 : (if 2 ≤ D v then (1:ℝ) else 0) = 1 := if_pos (by omega)
    calc (1:ℝ) = if 2 ≤ D v then (1:ℝ) else 0 := h1.symm
      _ ≤ ∑ v, (if 2 ≤ D v then (1:ℝ) else 0) :=
        Finset.single_le_sum (f := fun v => if 2 ≤ D v then (1:ℝ) else 0) (fun v _ => h0 v)
          (Finset.mem_univ v)

/-- `P(D ∉ S₁) ≤ n λ²/2`. -/
private lemma ckv_E_e {n : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) :
    Summable (fun D : Fin n → ℕ =>
      poisPi (fun _ => lam) D * (if ∀ v, D v ≤ 1 then (0:ℝ) else 1)) ∧
    ∑' D : Fin n → ℕ, poisPi (fun _ => lam) D * (if ∀ v, D v ≤ 1 then (0:ℝ) else 1) ≤
      n * (lam ^ 2 / 2) := by
  obtain ⟨hT, hT2⟩ := ckv_tail hlam
  have H : HasSum (fun D : Fin n → ℕ =>
      ∑ v, poisPi (fun _ => lam) D * (if 2 ≤ D v then (1:ℝ) else 0))
      (∑ _v : Fin n, ∑' k : ℕ, (if 2 ≤ k then poisPMF lam k else 0)) :=
    hasSum_sum fun v _ => ckv_marg_hasSum hlam v (fun k => if 2 ≤ k then (1:ℝ) else 0)
      (fun k => by split_ifs <;> norm_num) hT
  have hle : ∀ D : Fin n → ℕ, poisPi (fun _ => lam) D * (if ∀ v, D v ≤ 1 then (0:ℝ) else 1) ≤
      ∑ v, poisPi (fun _ => lam) D * (if 2 ≤ D v then (1:ℝ) else 0) := by
    intro D
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (ckv_e_le D) (rs_poisPi_nonneg (fun _ => hlam) D)
  have h0 : ∀ D : Fin n → ℕ,
      0 ≤ poisPi (fun _ => lam) D * (if ∀ v, D v ≤ 1 then (0:ℝ) else 1) :=
    fun D => mul_nonneg (rs_poisPi_nonneg (fun _ => hlam) D) (by split_ifs <;> norm_num)
  have hs := Summable.of_nonneg_of_le h0 hle H.summable
  refine ⟨hs, (Summable.tsum_le_tsum hle hs H.summable).trans ?_⟩
  rw [H.tsum_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left hT2 (Nat.cast_nonneg _)

private lemma ckv_J_mem {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (W : Finset (Fin n)) : 0 ≤ ckJ μ W ∅ ∧ ckJ μ W ∅ ≤ n * Real.log q := by
  unfold ckJ
  constructor
  · exact Finset.sum_nonneg fun w _ => ck_MI_nonneg hμ _ _ _
  · calc ∑ w ∈ W, ckMI μ {w} (W.erase w) ∅ ≤ ∑ _w ∈ W, Real.log q :=
          Finset.sum_le_sum fun w _ => ck_MI_single_le hμ w _ _
      _ = W.card * Real.log q := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n * Real.log q := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg q)
          have := Finset.card_le_univ W
          rw [Fintype.card_fin] at this
          exact_mod_cast this

/-- `E 𝒥_μ(W | ∅) = 𝒥̄_p(μ)` with `W = {v : D_v ≥ 1} ∼ Bern(1 - e^{-λ})`. -/
private lemma ckv_E_J {n q : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) {μ : (Fin n → Fin q) → ℝ}
    (hμ : IsPMF μ) :
    Summable (fun D : Fin n → ℕ => poisPi (fun _ => lam) D * ckJ μ (ckvW D) ∅) ∧
    ∑' D : Fin n → ℕ, poisPi (fun _ => lam) D * ckJ μ (ckvW D) ∅ =
      ckJbar (1 - Real.exp (-lam)) μ := by
  constructor
  · refine rs_summable_poisPi_of_abs_le (fun _ => hlam) (A := n * Real.log q) (c := 1)
      zero_le_one fun D => ?_
    rw [one_pow, mul_one, abs_of_nonneg (ckv_J_mem hμ _).1]
    exact (ckv_J_mem hμ _).2
  · exact ck_poisPi_support hlam (fun W => ckJ μ W ∅)

/-- The Cauchy–Schwarz factors `f = (1+|D|)^{3/2} m₊^{|D|}`, `g̃ = g/(1+|D|)^{1/2}`. -/
private def ckvF (t : ℝ) {n : ℕ} (D : Fin n → ℕ) : ℝ :=
  (1 + ((∑ v, D v : ℕ) : ℝ)) * ckMp t ^ (∑ v, D v) * Real.sqrt (1 + ((∑ v, D v : ℕ) : ℝ))

private def ckvGt {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) (D : Fin n → ℕ) : ℝ :=
  ckvG μ D / Real.sqrt (1 + ((∑ v, D v : ℕ) : ℝ))

private lemma ckv_G_sq_le {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (D : Fin n → ℕ) :
    ckvGt μ D ^ 2 ≤ 2 * (if ∀ v, D v ≤ 1 then (0:ℝ) else 1) + 2 * ckJ μ (ckvW D) ∅ := by
  set k : ℝ := ((∑ v, D v : ℕ) : ℝ) with hkdef
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hk1 : 0 < 1 + k := by positivity
  set e : ℝ := if ∀ v, D v ≤ 1 then (0:ℝ) else 1 with hedef
  have he0 : 0 ≤ e := by rw [hedef]; split_ifs <;> norm_num
  have he2 : e ^ 2 = e := by rw [hedef]; split_ifs <;> norm_num
  set Sig := ∑ w ∈ ckvW D, Real.sqrt (ckMI μ {w} ((ckvW D).erase w) ∅) with hSigdef
  have hJ0 := (ckv_J_mem hμ (ckvW D)).1
  have hSig2 : Sig ^ 2 ≤ (ckvW D).card * ckJ μ (ckvW D) ∅ := by
    have h := sq_sum_le_card_mul_sum_sq (s := ckvW D)
      (f := fun w => Real.sqrt (ckMI μ {w} ((ckvW D).erase w) ∅))
    have e' : ∑ w ∈ ckvW D, Real.sqrt (ckMI μ {w} ((ckvW D).erase w) ∅) ^ 2 =
        ckJ μ (ckvW D) ∅ := by
      unfold ckJ
      exact Finset.sum_congr rfl fun w _ => Real.sq_sqrt (ck_MI_nonneg hμ _ _ _)
    rw [e'] at h
    exact h
  have hW : ((ckvW D).card : ℝ) ≤ k := by
    rw [hkdef]; exact_mod_cast ckv_card_W_le D
  have hG : ckvG μ D = e + Sig := rfl
  have hGsq : ckvG μ D ^ 2 ≤ (2 * e + 2 * ckJ μ (ckvW D) ∅) * (1 + k) := by
    rw [hG]
    have h1 : (e + Sig) ^ 2 ≤ 2 * e ^ 2 + 2 * Sig ^ 2 := by nlinarith [sq_nonneg (e - Sig)]
    have h2 : (ckvW D).card * ckJ μ (ckvW D) ∅ ≤ (1 + k) * ckJ μ (ckvW D) ∅ :=
      mul_le_mul_of_nonneg_right (by linarith) hJ0
    nlinarith
  unfold ckvGt
  rw [div_pow, Real.sq_sqrt hk1.le, div_le_iff₀ hk1]
  exact hGsq

private lemma ckv_F_sq {t : ℝ} {n : ℕ} (D : Fin n → ℕ) :
    ckvF t D ^ 2 = (1 + ((∑ v, D v : ℕ) : ℝ)) ^ 3 * (ckMp t ^ 2) ^ (∑ v, D v) := by
  have hk1 : (0:ℝ) ≤ 1 + ((∑ v, D v : ℕ) : ℝ) := by positivity
  unfold ckvF
  rw [mul_pow, mul_pow, Real.sq_sqrt hk1, ← pow_mul, mul_comm (∑ v, D v) 2, pow_mul]
  ring

private lemma ckv_FG {t : ℝ} {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) (D : Fin n → ℕ) :
    ckvF t D * ckvGt μ D = (1 + ((∑ v, D v : ℕ) : ℝ)) * ckMp t ^ (∑ v, D v) * ckvG μ D := by
  have hk1 : (0:ℝ) < 1 + ((∑ v, D v : ℕ) : ℝ) := by positivity
  have hs : Real.sqrt (1 + ((∑ v, D v : ℕ) : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hk1).ne'
  unfold ckvF ckvGt
  field_simp

/-- `E[(1+|D|) m₊^{|D|} g(D)] ≤ √(E (1+|D|)³ m₊^{2|D|}) √(n λ² + 2 𝒥̄)`. -/
private lemma ckv_cs {q n : ℕ} {t : ℝ} (hp : CKPar q t) {lam : ℝ} (hlam : 0 ≤ lam)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) :
    Summable (fun D : Fin n → ℕ => poisPi (fun _ => lam) D *
      ((1 + ((∑ v, D v : ℕ) : ℝ)) * ckMp t ^ (∑ v, D v) * ckvG μ D)) ∧
    ∑' D : Fin n → ℕ, poisPi (fun _ => lam) D *
        ((1 + ((∑ v, D v : ℕ) : ℝ)) * ckMp t ^ (∑ v, D v) * ckvG μ D) ≤
      Real.sqrt (Real.exp (n * (lam * (2 ^ 3 * ckMp t ^ 2 - 1)))) *
        Real.sqrt (n * lam ^ 2 + 2 * ckJbar (1 - Real.exp (-lam)) μ) := by
  obtain ⟨hm0, -, hm1, -⟩ := ck_const_bounds hp
  have hP : ∀ D : Fin n → ℕ, 0 ≤ poisPi (fun _ => lam) D := rs_poisPi_nonneg (fun _ => hlam)
  have hF0 : ∀ D : Fin n → ℕ, 0 ≤ ckvF t D := fun D => by
    unfold ckvF; exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (by linarith) _))
      (Real.sqrt_nonneg _)
  have hGt0 : ∀ D : Fin n → ℕ, 0 ≤ ckvGt μ D := fun D =>
    div_nonneg (ckv_G_nonneg μ D) (Real.sqrt_nonneg _)
  obtain ⟨hSf, hBf⟩ := ckv_moment (n := n) hlam (by positivity : (0:ℝ) ≤ ckMp t ^ 2) 3
  have hSf2 : Summable fun D : Fin n → ℕ => poisPi (fun _ => lam) D * ckvF t D ^ 2 :=
    hSf.congr fun D => by rw [ckv_F_sq]
  have hBf2 : ∑' D : Fin n → ℕ, poisPi (fun _ => lam) D * ckvF t D ^ 2 ≤
      Real.exp (n * (lam * (2 ^ 3 * ckMp t ^ 2 - 1))) := by
    refine le_trans (le_of_eq ?_) hBf
    exact tsum_congr fun D => by rw [ckv_F_sq]
  obtain ⟨hSe, hBe⟩ := ckv_E_e (n := n) hlam
  obtain ⟨hSJ, hEJ⟩ := ckv_E_J (n := n) hlam hμ
  have hSeJ := (hSe.mul_left 2).add (hSJ.mul_left 2)
  have hle2 : ∀ D : Fin n → ℕ, poisPi (fun _ => lam) D * ckvGt μ D ^ 2 ≤
      2 * (poisPi (fun _ => lam) D * (if ∀ v, D v ≤ 1 then (0:ℝ) else 1)) +
        2 * (poisPi (fun _ => lam) D * ckJ μ (ckvW D) ∅) := by
    intro D
    have := mul_le_mul_of_nonneg_left (ckv_G_sq_le hμ D) (hP D)
    linarith
  have hSg2 : Summable fun D : Fin n → ℕ => poisPi (fun _ => lam) D * ckvGt μ D ^ 2 :=
    Summable.of_nonneg_of_le (fun D => mul_nonneg (hP D) (sq_nonneg _)) hle2 hSeJ
  have hBg2 : ∑' D : Fin n → ℕ, poisPi (fun _ => lam) D * ckvGt μ D ^ 2 ≤
      n * lam ^ 2 + 2 * ckJbar (1 - Real.exp (-lam)) μ := by
    refine (Summable.tsum_le_tsum hle2 hSg2 hSeJ).trans ?_
    rw [Summable.tsum_add (hSe.mul_left 2) (hSJ.mul_left 2), tsum_mul_left, tsum_mul_left, hEJ]
    linarith
  have hCS := ckv_tsum_mul_le_sqrt (w := poisPi (fun _ : Fin n => lam)) (f := ckvF t)
    (g := ckvGt μ) hP hF0 hGt0 hSf2 hSg2
  have hFG : ∀ D : Fin n → ℕ, poisPi (fun _ => lam) D *
      ((1 + ((∑ v, D v : ℕ) : ℝ)) * ckMp t ^ (∑ v, D v) * ckvG μ D) =
        poisPi (fun _ => lam) D * (ckvF t D * ckvGt μ D) := fun D => by
    rw [ckv_FG μ D]
  have hle3 : ∀ D : Fin n → ℕ, poisPi (fun _ => lam) D * (ckvF t D * ckvGt μ D) ≤
      (poisPi (fun _ => lam) D * ckvF t D ^ 2 + poisPi (fun _ => lam) D * ckvGt μ D ^ 2) / 2 := by
    intro D
    have := mul_le_mul_of_nonneg_left (two_mul_le_add_sq (ckvF t D) (ckvGt μ D)) (hP D)
    linarith
  have hSfg : Summable fun D : Fin n → ℕ => poisPi (fun _ => lam) D * (ckvF t D * ckvGt μ D) :=
    Summable.of_nonneg_of_le (fun D => mul_nonneg (hP D) (mul_nonneg (hF0 D) (hGt0 D))) hle3
      ((hSf2.add hSg2).div_const 2)
  refine ⟨hSfg.congr fun D => (hFG D).symm, ?_⟩
  rw [tsum_congr hFG]
  refine hCS.trans (mul_le_mul (Real.sqrt_le_sqrt hBf2) (Real.sqrt_le_sqrt hBg2)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-! ### Assembly -/

private lemma ckv_sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rcases le_or_gt 0 b with hb | hb
  · rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, mul_nonneg (Real.sqrt_nonneg a)
      (Real.sqrt_nonneg b)]
  · calc Real.sqrt (a + b) ≤ Real.sqrt a := Real.sqrt_le_sqrt (by linarith)
      _ ≤ Real.sqrt a + Real.sqrt b := le_add_of_nonneg_right (Real.sqrt_nonneg _)

/-- Lemma 7.3 with explicit constants, for one `n`. -/
private lemma ckv_main {q n : ℕ} {t : ℝ} (hp : CKPar q t) {s : ℝ} (hs : 0 < s) (hn : 2 ≤ n)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) :
    ckVert q t (s / (2 * ((n : ℝ) + 1))) μ ≤
      ckBV q t (s * n / ((n : ℝ) + 1)) (fun _ => (n : ℝ)⁻¹) (ckMarg μ) +
        ((s / (2 * ((n : ℝ) + 1)) * Real.exp s +
            (1 + s + ckEll q t) * Real.exp s * (s * |t| * q) * ckDev μ) *
              Real.exp (s * (2 ^ 1 * ckMp t - 1)) +
          2 * (1 + s + ckEll q t) * (Real.sqrt (Real.exp (s * (2 ^ 3 * ckMp t ^ 2 - 1))) *
            Real.sqrt (n * (s / ((n : ℝ) + 1)) ^ 2 +
              2 * ckJbar (1 - Real.exp (-(s / ((n : ℝ) + 1)))) μ))) := by
  set ϱ := s / (2 * ((n : ℝ) + 1)) with hϱdef
  set lam := s / ((n : ℝ) + 1) with hlamdef
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hϱ : 0 ≤ ϱ := by positivity
  have hlam : 0 ≤ lam := by positivity
  have h2ϱ : 2 * ϱ = lam := by rw [hϱdef, hlamdef]; field_simp
  have hnlam : n * lam ≤ s := by
    rw [hlamdef, mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  have hϱn : 2 * ϱ * n ≤ s := by rw [h2ϱ, mul_comm]; exact hnlam
  obtain ⟨hm0, hm1, hp1, -⟩ := ck_const_bounds hp
  have hℓ : 0 < ckEll q t := (ck_const_bounds hp).2.2.2.2.2.1
  have hP : ∀ D : Fin n → ℕ, 0 ≤ poisPi (fun _ => lam) D := rs_poisPi_nonneg (fun _ => hlam)
  -- Step 0: the loop count
  have hV1 := ckv_vert_le hp hϱ hμ
  rw [h2ϱ] at hV1
  have hSF := ckv_summable_F hp hϱ hμ
  rw [h2ϱ] at hSF
  -- `BV_r` at the empirical law of the marginals as a Poisson sum
  have hBV : ckBV q t (s * n / ((n : ℝ) + 1)) (fun _ => (n : ℝ)⁻¹) (ckMarg μ) =
      ∑' D, poisPi (fun _ => lam) D * ckLam (ckvY q t μ D) := by
    rw [ck_BV_emp hp (by omega) (by positivity) (fun v => ck_marg_mem hμ v)]
    have e : s * n / ((n : ℝ) + 1) / n = lam := by rw [hlamdef]; field_simp
    rw [e]; rfl
  have hSY : Summable fun D : Fin n → ℕ => poisPi (fun _ => lam) D * ckLam (ckvY q t μ D) := by
    refine rs_summable_poisPi_of_abs_le (fun _ => hlam) (A := 1) (c := Real.exp (2 * ckEll q t))
      (Real.exp_pos _).le fun D => ?_
    have h := ckv_lam_abs_le_exp (ckv_Y_mem_exp hp hμ D (le_refl (0:ℝ)))
    refine h.trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul]; ring_nf
  -- the error term `H`
  set c₂ := 1 + s + ckEll q t with hc₂
  set A0 := ϱ * Real.exp s + c₂ * Real.exp s * (s * |t| * q) * ckDev μ with hA0
  obtain ⟨hS1, hB1⟩ := ckv_moment (n := n) hlam (by linarith : (0:ℝ) ≤ ckMp t) 1
  obtain ⟨hScs, hBcs⟩ := ckv_cs hp hlam hμ
  set H : (Fin n → ℕ) → ℝ := fun D => (1 + ((∑ v, D v : ℕ) : ℝ)) * ckMp t ^ (∑ v, D v) * A0 +
      2 * c₂ * ((1 + ((∑ v, D v : ℕ) : ℝ)) * ckMp t ^ (∑ v, D v) * ckvG μ D) with hHdef
  have hSH1 : Summable fun D : Fin n → ℕ =>
      poisPi (fun _ => lam) D * ((1 + ((∑ v, D v : ℕ) : ℝ)) * ckMp t ^ (∑ v, D v)) :=
    hS1.congr fun D => by rw [pow_one]
  have hEH : HasSum (fun D : Fin n → ℕ => poisPi (fun _ => lam) D * H D)
      (A0 * ∑' D : Fin n → ℕ, poisPi (fun _ => lam) D *
          ((1 + ((∑ v, D v : ℕ) : ℝ)) * ckMp t ^ (∑ v, D v)) +
        2 * c₂ * ∑' D : Fin n → ℕ, poisPi (fun _ => lam) D *
          ((1 + ((∑ v, D v : ℕ) : ℝ)) * ckMp t ^ (∑ v, D v) * ckvG μ D)) := by
    have h := (hSH1.hasSum.mul_left A0).add (hScs.hasSum.mul_left (2 * c₂))
    refine h.congr_fun fun D => ?_
    simp only [hHdef]; ring
  have hpt : ∀ D : Fin n → ℕ, poisPi (fun _ => lam) D *
      (ckLam (ckvXt q t ϱ μ D) + ϱ * (1 - ckMm q t) * ckvXt q t ϱ μ D) ≤
        poisPi (fun _ => lam) D * ckLam (ckvY q t μ D) + poisPi (fun _ => lam) D * H D := by
    intro D
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (ckv_pt hp hϱ hϱn hμ D) (hP D)
  have hstep : ∑' D : Fin n → ℕ, poisPi (fun _ => lam) D *
      (ckLam (ckvXt q t ϱ μ D) + ϱ * (1 - ckMm q t) * ckvXt q t ϱ μ D) ≤
        ∑' D : Fin n → ℕ, poisPi (fun _ => lam) D * ckLam (ckvY q t μ D) +
          ∑' D : Fin n → ℕ, poisPi (fun _ => lam) D * H D := by
    rw [← Summable.tsum_add hSY hEH.summable]
    exact Summable.tsum_le_tsum hpt hSF (hSY.add hEH.summable)
  -- bounds on the two moments
  have hE1 : ∑' D : Fin n → ℕ, poisPi (fun _ => lam) D *
      ((1 + ((∑ v, D v : ℕ) : ℝ)) * ckMp t ^ (∑ v, D v)) ≤
        Real.exp (s * (2 ^ 1 * ckMp t - 1)) := by
    refine le_trans (le_of_eq (tsum_congr fun D => by rw [pow_one])) (hB1.trans ?_)
    apply Real.exp_le_exp.mpr
    have h1 : 0 ≤ 2 ^ 1 * ckMp t - 1 := by linarith
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hnlam h1
  have hE3 : Real.sqrt (Real.exp (n * (lam * (2 ^ 3 * ckMp t ^ 2 - 1)))) ≤
      Real.sqrt (Real.exp (s * (2 ^ 3 * ckMp t ^ 2 - 1))) := by
    apply Real.sqrt_le_sqrt
    apply Real.exp_le_exp.mpr
    have h1 : 0 ≤ 2 ^ 3 * ckMp t ^ 2 - 1 := by nlinarith
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hnlam h1
  have hA00 : 0 ≤ A0 := by
    have hdev : 0 ≤ ckDev μ :=
      Finset.sum_nonneg fun τ _ => mul_nonneg (hμ.1 τ) (Real.sqrt_nonneg _)
    positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  rw [hBV]
  calc ckVert q t ϱ μ ≤ _ := hV1
    _ ≤ _ := hstep
    _ = ∑' D : Fin n → ℕ, poisPi (fun _ => lam) D * ckLam (ckvY q t μ D) +
        (A0 * ∑' D : Fin n → ℕ, poisPi (fun _ => lam) D *
            ((1 + ((∑ v, D v : ℕ) : ℝ)) * ckMp t ^ (∑ v, D v)) +
          2 * c₂ * ∑' D : Fin n → ℕ, poisPi (fun _ => lam) D *
            ((1 + ((∑ v, D v : ℕ) : ℝ)) * ckMp t ^ (∑ v, D v) * ckvG μ D)) := by
        rw [hEH.tsum_eq]
    _ ≤ _ := by
        gcongr
        exact hBcs.trans (mul_le_mul_of_nonneg_right hE3 (Real.sqrt_nonneg _))

-- Lemma 7.3 (1/n ≤ 1/√n absorbed)
theorem ck_vertex {q : ℕ} {t : ℝ} (hp : CKPar q t) {s : ℝ} (hs : 0 < s) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ μ : (Fin n → Fin q) → ℝ, IsPMF μ →
      ckVert q t (s / (2 * ((n : ℝ) + 1))) μ ≤
        ckBV q t (s * n / ((n : ℝ) + 1)) (fun _ => (n : ℝ)⁻¹) (ckMarg μ) +
          C * (1 / Real.sqrt n + ckDev μ +
            Real.sqrt (ckJbar (1 - Real.exp (-(s / ((n : ℝ) + 1)))) μ)) := by
  obtain ⟨hm0, hm1, hp1, -⟩ := ck_const_bounds hp
  have hℓ : 0 < ckEll q t := (ck_const_bounds hp).2.2.2.2.2.1
  set c₂ := 1 + s + ckEll q t with hc₂
  set K := s * |t| * q with hK
  set E1 := Real.exp (s * (2 ^ 1 * ckMp t - 1)) with hE1
  set E3 := Real.exp (s * (2 ^ 3 * ckMp t ^ 2 - 1)) with hE3
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hK0 : 0 ≤ K := by positivity
  have hE10 : 0 ≤ E1 := (Real.exp_pos _).le
  have hE30 : 0 ≤ Real.sqrt E3 := Real.sqrt_nonneg _
  have hes : 0 ≤ Real.exp s := (Real.exp_pos _).le
  refine ⟨s * Real.exp s * E1 + c₂ * Real.exp s * K * E1 +
    2 * c₂ * Real.sqrt E3 * (s + Real.sqrt 2), fun n hn μ hμ => ?_⟩
  refine (ckv_main hp hs hn hμ).trans ((add_le_add_iff_left _).mpr ?_)
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  set a := 1 / Real.sqrt n with ha
  have ha0 : 0 ≤ a := by positivity
  set d := ckDev μ with hd
  have hd0 : 0 ≤ d := Finset.sum_nonneg fun τ _ => mul_nonneg (hμ.1 τ) (Real.sqrt_nonneg _)
  set J := ckJbar (1 - Real.exp (-(s / ((n : ℝ) + 1)))) μ with hJ
  set j := Real.sqrt J with hj
  have hj0 : 0 ≤ j := Real.sqrt_nonneg _
  -- `ϱ ≤ s / √n`
  have hϱa : s / (2 * ((n : ℝ) + 1)) ≤ s * a := by
    have h1 : Real.sqrt n ≤ 2 * ((n : ℝ) + 1) := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith
    rw [ha, mul_one_div]
    exact div_le_div_of_nonneg_left hs.le hsn h1
  -- `√(n λ² + 2 𝒥̄) ≤ s/√n + √2 √𝒥̄`
  have hroot : Real.sqrt (n * (s / ((n : ℝ) + 1)) ^ 2 + 2 * J) ≤ s * a + Real.sqrt 2 * j := by
    have h1 : 0 ≤ n * (s / ((n : ℝ) + 1)) ^ 2 := by positivity
    refine (ckv_sqrt_add_le h1).trans (add_le_add ?_ (le_of_eq (Real.sqrt_mul (by norm_num) J)))
    have ha2 : a ^ 2 = 1 / n := by rw [ha, div_pow, one_pow, Real.sq_sqrt hn0.le]
    rw [Real.sqrt_le_left (by positivity), mul_pow, ha2, div_pow, mul_one_div, mul_div_assoc',
      div_le_div_iff₀ (by positivity) hn0]
    nlinarith [mul_nonneg (sq_nonneg s) (by positivity : (0:ℝ) ≤ 2 * n + 1)]
  have h2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hbig : (s / (2 * ((n : ℝ) + 1)) * Real.exp s + c₂ * Real.exp s * K * d) * E1 +
      2 * c₂ * (Real.sqrt E3 * Real.sqrt (n * (s / ((n : ℝ) + 1)) ^ 2 + 2 * J)) ≤
        (s * Real.exp s * E1 + 2 * c₂ * Real.sqrt E3 * s) * a + (c₂ * Real.exp s * K * E1) * d +
          (2 * c₂ * Real.sqrt E3 * Real.sqrt 2) * j := by
    have t1 : s / (2 * ((n : ℝ) + 1)) * Real.exp s * E1 ≤ s * a * Real.exp s * E1 := by gcongr
    have t2 : 2 * c₂ * (Real.sqrt E3 * Real.sqrt (n * (s / ((n : ℝ) + 1)) ^ 2 + 2 * J)) ≤
        2 * c₂ * (Real.sqrt E3 * (s * a + Real.sqrt 2 * j)) := by gcongr
    linarith [t1, t2]
  refine hbig.trans ?_
  set C := s * Real.exp s * E1 + c₂ * Real.exp s * K * E1 +
    2 * c₂ * Real.sqrt E3 * (s + Real.sqrt 2) with hC
  have p1 : 0 ≤ c₂ * Real.exp s * K * E1 := by positivity
  have p2 : 0 ≤ c₂ * Real.sqrt E3 * Real.sqrt 2 := by positivity
  have p3 : 0 ≤ s * Real.exp s * E1 := by positivity
  have p4 : 0 ≤ c₂ * Real.sqrt E3 * s := by positivity
  have hC1 : s * Real.exp s * E1 + 2 * c₂ * Real.sqrt E3 * s ≤ C := by rw [hC]; linarith
  have hC2 : c₂ * Real.exp s * K * E1 ≤ C := by rw [hC]; linarith
  have hC3 : 2 * c₂ * Real.sqrt E3 * Real.sqrt 2 ≤ C := by rw [hC]; linarith
  have q1 := mul_le_mul_of_nonneg_right hC1 ha0
  have q2 := mul_le_mul_of_nonneg_right hC2 hd0
  have q3 := mul_le_mul_of_nonneg_right hC3 hj0
  linarith

end

end ERZeroFreeness
