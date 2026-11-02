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
import ERZeroFreeness.CKBetheFin
import ERZeroFreeness.CKBethe
import ERZeroFreeness.CKBridge
import ERZeroFreeness.CKPlanted
import ERZeroFreeness.CKEdge
import ERZeroFreeness.CKPinPost
import ERZeroFreeness.CKCavity
import ERZeroFreeness.CKVertex
import ERZeroFreeness.RSPoisPi
import ERZeroFreeness.RSModel
import ERZeroFreeness.RSBetheBasic
import ERZeroFreeness.RSPoisSplit
import ERZeroFreeness.Poisson

/-!
# Stage B of Appendix C: Propositions 8.1, 8.2, (H3) and Theorem 0.1 of the self-contained proof of [CKPZ, Prop. 3.6]

Proof of `CKPZProp36 q` (the Potts specialization of Coja-Oghlan–Krzakala–Perkins–Zdeborová,
Proposition 3.6) from first principles.  The mathematics, with every lemma, constant and limit
order, is in `docs/appendixC/ckpz-proof.md` (Propositions 8.1, 8.2, (H3) and Theorem 0.1; its §12 is the Lean plan these frozen
statements come from).  Frozen statements must not be changed; provers add helpers freely.
-/

open Filter Topology MeasureTheory

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-! ### Elementary real analysis used by the assembly -/

/-- `2√(x-1) + 1/√x ≤ 2√x` for `x ≥ 1` (telescoping `∑ n^{-1/2} ≤ 2√N`). -/
private lemma ckM_sqrt_step {x : ℝ} (hx : 1 ≤ x) :
    2 * Real.sqrt (x - 1) + 1 / Real.sqrt x ≤ 2 * Real.sqrt x := by
  have ha : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hb : 0 ≤ Real.sqrt (x - 1) := Real.sqrt_nonneg _
  have ha2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have hb2 : Real.sqrt (x - 1) ^ 2 = x - 1 := Real.sq_sqrt (by linarith)
  have key : 1 ≤ (2 * Real.sqrt x - 2 * Real.sqrt (x - 1)) * Real.sqrt x := by
    nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt (x - 1))]
  have : 1 / Real.sqrt x ≤ 2 * Real.sqrt x - 2 * Real.sqrt (x - 1) := by
    rw [div_le_iff₀ ha]; exact key
  linarith

/-- `log x + 1/(x+1) ≤ log (x+1)` for `x > 0` (telescoping `∑ 1/(n+1) ≤ log N`). -/
private lemma ckM_log_step {x : ℝ} (hx : 0 < x) :
    Real.log x + 1 / (x + 1) ≤ Real.log (x + 1) := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have h1 := Real.log_le_sub_one_of_pos (div_pos hx hx1)
  rw [Real.log_div hx.ne' hx1.ne'] at h1
  have h2 : x / (x + 1) - 1 = -(1 / (x + 1)) := by field_simp; ring
  linarith

/-- `log x ≤ 2√x` for `x > 0`. -/
private lemma ckM_log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  rw [Real.log_sqrt hx.le] at h1
  linarith

/-- Eventually `K √N ≤ ε N`. -/
private lemma ckM_ev_sqrt_le (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, K * Real.sqrt N ≤ ε * N := by
  filter_upwards [eventually_ge_atTop ⌈(K / ε) ^ 2⌉₊] with N hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hN' : (K / ε) ^ 2 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0
  have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  rcases le_or_gt K 0 with hK | hK
  · nlinarith
  · have h1 : K / ε ≤ Real.sqrt N :=
      (Real.le_sqrt (div_nonneg hK.le hε.le) hN0).mpr hN'
    have h2 : K ≤ ε * Real.sqrt N := by
      rw [div_le_iff₀ hε] at h1; linarith
    calc K * Real.sqrt N ≤ ε * Real.sqrt N * Real.sqrt N :=
          mul_le_mul_of_nonneg_right h2 hs0
      _ = ε * N := by rw [mul_assoc, hsq]

/-- Averages over `k < T` are monotone. -/
private lemma ckM_avg_mono {T : ℕ} {f g : ℕ → ℝ} (h : ∀ k ∈ Finset.range T, f k ≤ g k) :
    (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, f k ≤ (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, g k :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum h) (by positivity)

/-- The average of a constant. -/
private lemma ckM_avg_const {T : ℕ} (hT : 1 ≤ T) (c : ℝ) :
    (T : ℝ)⁻¹ * ∑ _k ∈ Finset.range T, c = c := by
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hT0,
    one_mul]

/-- Jensen for `√` on a finite average (Cauchy–Schwarz). -/
private lemma ckM_avg_sqrt_le {T : ℕ} (hT : 1 ≤ T) {x : ℕ → ℝ}
    (hx : ∀ k ∈ Finset.range T, 0 ≤ x k) :
    (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, Real.sqrt (x k) ≤
      Real.sqrt ((T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, x k) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range T) (fun _ => (1 : ℝ))
    (fun k => Real.sqrt (x k))
  have hsq : ∑ k ∈ Finset.range T, Real.sqrt (x k) ^ 2 = ∑ k ∈ Finset.range T, x k :=
    Finset.sum_congr rfl (fun k hk => Real.sq_sqrt (hx k hk))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    hsq] at hCS
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow]
  calc ((T : ℝ)⁻¹) ^ 2 * (∑ k ∈ Finset.range T, Real.sqrt (x k)) ^ 2
      ≤ ((T : ℝ)⁻¹) ^ 2 * ((T : ℝ) * ∑ k ∈ Finset.range T, x k) :=
        mul_le_mul_of_nonneg_left hCS (by positivity)
    _ = (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, x k := by
        field_simp

/-! ### Bounded functions under `𝖰` -/

/-- A bounded function is dominated (`c = 1`). -/
private lemma ckM_dom {q n : ℕ} {f : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ} {B : ℝ}
    (h : ∀ σ G U, |f σ G U| ≤ B) : CKDom f :=
  ⟨B, 1, zero_le_one, fun σ G U => by simpa using h σ G U⟩

/-- Bounds for `a + (b f₁ + (c f₂ + d f₃))`. -/
private lemma ckM_bdd_lin {q n : ℕ} {f₁ f₂ f₃ : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ}
    {B₁ B₂ B₃ : ℝ} (a b c d : ℝ) (h₁ : ∀ σ G U, |f₁ σ G U| ≤ B₁)
    (h₂ : ∀ σ G U, |f₂ σ G U| ≤ B₂) (h₃ : ∀ σ G U, |f₃ σ G U| ≤ B₃) :
    ∀ σ G U, |a + (b * f₁ σ G U + (c * f₂ σ G U + d * f₃ σ G U))| ≤
      |a| + (|b| * B₁ + (|c| * B₂ + |d| * B₃)) := by
  intro σ G U
  have e1 : |b * f₁ σ G U| ≤ |b| * B₁ := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h₁ σ G U) (abs_nonneg b)
  have e2 : |c * f₂ σ G U| ≤ |c| * B₂ := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h₂ σ G U) (abs_nonneg c)
  have e3 : |d * f₃ σ G U| ≤ |d| * B₃ := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h₃ σ G U) (abs_nonneg d)
  calc |a + (b * f₁ σ G U + (c * f₂ σ G U + d * f₃ σ G U))|
      ≤ |a| + |b * f₁ σ G U + (c * f₂ σ G U + d * f₃ σ G U)| := abs_add_le _ _
    _ ≤ |a| + (|b * f₁ σ G U| + |c * f₂ σ G U + d * f₃ σ G U|) := by
        gcongr; exact abs_add_le _ _
    _ ≤ |a| + (|b * f₁ σ G U| + (|c * f₂ σ G U| + |d * f₃ σ G U|)) := by
        gcongr; exact abs_add_le _ _
    _ ≤ |a| + (|b| * B₁ + (|c| * B₂ + |d| * B₃)) := by gcongr

/-- Linearity of `E_𝖰` on `a + (b f₁ + (c f₂ + d f₃))` for bounded `fᵢ`. -/
private lemma ckM_QExp_lin {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (π a b c d : ℝ) {f₁ f₂ f₃ : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ}
    {B₁ B₂ B₃ : ℝ} (h₁ : ∀ σ G U, |f₁ σ G U| ≤ B₁) (h₂ : ∀ σ G U, |f₂ σ G U| ≤ B₂)
    (h₃ : ∀ σ G U, |f₃ σ G U| ≤ B₃) :
    ckQExp q t ϱ π n (fun σ G U => a + (b * f₁ σ G U + (c * f₂ σ G U + d * f₃ σ G U))) =
      a + (b * ckQExp q t ϱ π n f₁ +
        (c * ckQExp q t ϱ π n f₂ + d * ckQExp q t ϱ π n f₃)) := by
  have hb1 : CKDom (fun σ G U => b * f₁ σ G U) := ckM_dom (B := |b| * B₁) (fun σ G U => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h₁ σ G U) (abs_nonneg b))
  have hc2 : CKDom (fun σ G U => c * f₂ σ G U) := ckM_dom (B := |c| * B₂) (fun σ G U => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h₂ σ G U) (abs_nonneg c))
  have hd3 : CKDom (fun σ G U => d * f₃ σ G U) := ckM_dom (B := |d| * B₃) (fun σ G U => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h₃ σ G U) (abs_nonneg d))
  have h23 : CKDom (fun σ G U => c * f₂ σ G U + d * f₃ σ G U) :=
    ckM_dom (B := |c| * B₂ + |d| * B₃) (fun σ G U => by
      have := ckM_bdd_lin 0 0 c d h₁ h₂ h₃ σ G U
      simpa using this)
  have h123 : CKDom (fun σ G U => b * f₁ σ G U + (c * f₂ σ G U + d * f₃ σ G U)) :=
    ckM_dom (B := |b| * B₁ + (|c| * B₂ + |d| * B₃)) (fun σ G U => by
      have := ckM_bdd_lin 0 b c d h₁ h₂ h₃ σ G U
      simpa using this)
  have ha : CKDom (fun (_ : Fin n → Fin q) (_ : RSGraph n) (_ : Finset (Fin n)) => a) :=
    ckM_dom (B := |a|) (fun _ _ _ => le_refl _)
  rw [ck_QExp_add hp hϱ π ha h123, ck_QExp_add hp hϱ π hb1 h23, ck_QExp_add hp hϱ π hc2 hd3,
    ck_QExp_const hp hϱ π a, ck_QExp_smul, ck_QExp_smul, ck_QExp_smul]

/-- `E_𝖰 f ≥ 0` for bounded `f ≥ 0`. -/
private lemma ckM_QExp_nonneg {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ π : ℝ} (hϱ : 0 ≤ ϱ)
    (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) {f : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ}
    {B : ℝ} (hfb : ∀ σ G U, |f σ G U| ≤ B) (hf0 : ∀ σ G U, 0 ≤ f σ G U) :
    0 ≤ ckQExp q t ϱ π n f := by
  have h := ck_QExp_mono hp hϱ hπ0 hπ1 (f := fun _ _ _ => (0 : ℝ)) (g := f)
    (ckM_dom (B := 0) (fun _ _ _ => by simp)) (ckM_dom hfb) hf0
  rwa [ck_QExp_const hp hϱ π 0] at h

/-! ### Bounds on the functionals of a probability mass function -/

private lemma ckM_le_one {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (τ : Fin n → Fin q) : μ τ ≤ 1 := by
  have h := Finset.single_le_sum (fun τ' _ => hμ.1 τ') (Finset.mem_univ τ)
  rw [hμ.2] at h
  exact h

private lemma ckM_dev_mem {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) :
    0 ≤ ckDev μ ∧ ckDev μ ≤ ∑ τ : Fin n → Fin q, Real.sqrt (rsDevSq τ) := by
  constructor
  · exact Finset.sum_nonneg (fun τ _ => mul_nonneg (hμ.1 τ) (Real.sqrt_nonneg _))
  · apply Finset.sum_le_sum
    intro τ _
    calc μ τ * Real.sqrt (rsDevSq τ) ≤ 1 * Real.sqrt (rsDevSq τ) :=
          mul_le_mul_of_nonneg_right (ckM_le_one hμ τ) (Real.sqrt_nonneg _)
      _ = Real.sqrt (rsDevSq τ) := one_mul _

private lemma ckM_Jbar_mem {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ ckJbar p μ ∧ ckJbar p μ ≤ n * Real.log q := by
  have hlog : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hJ : ∀ W : Finset (Fin n), 0 ≤ ckJ μ W ∅ ∧ ckJ μ W ∅ ≤ n * Real.log q := by
    intro W
    constructor
    · exact Finset.sum_nonneg (fun w _ => ck_MI_nonneg hμ _ _ _)
    · calc ckJ μ W ∅ ≤ ∑ _w ∈ W, Real.log q :=
            Finset.sum_le_sum (fun w _ => ck_MI_single_le hμ w _ _)
        _ = W.card * Real.log q := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ n * Real.log q := by
            apply mul_le_mul_of_nonneg_right _ hlog
            have := Finset.card_le_univ W
            rw [Fintype.card_fin] at this
            exact_mod_cast this
  constructor
  · exact Finset.sum_nonneg (fun W _ => mul_nonneg (ck_bern_nonneg hp0 hp1 W) (hJ W).1)
  · calc ckJbar p μ ≤ ∑ W : Finset (Fin n), ckBern p W * (n * Real.log q) :=
          Finset.sum_le_sum (fun W _ =>
            mul_le_mul_of_nonneg_left (hJ W).2 (ck_bern_nonneg hp0 hp1 W))
      _ = n * Real.log q := by rw [← Finset.sum_mul, ck_bern_sum, one_mul]

private lemma ckM_iota_mem {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) :
    0 ≤ ckIota2 μ ∧ ckIota2 μ ≤
      Real.sqrt (((n : ℝ) ^ 2)⁻¹ * ∑ v : Fin n, ∑ _w ∈ Finset.univ.erase v, Real.log q) := by
  constructor
  · exact Real.sqrt_nonneg _
  · unfold ckIota2
    apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum (fun v _ => Finset.sum_le_sum (fun w _ => ck_MI_single_le hμ v _ _))

/-! ### Proposition 8.1: the per-posterior bound -/

/-- Lemma 7.3 + Lemma 5.4 + Lemma 2.3 + Lemma 2.2 + the `η`-hypothesis, for one posterior `μ`. -/
private lemma ckM_post_bound {q : ℕ} {t : ℝ} (hp : CKPar q t) {s η : ℝ} (hs : 0 < s)
    (hη : ∀ (K : ℕ) (w : Fin K → ℝ) (μ : Fin K → Fin q → ℝ), ckFinPu q w μ →
      ckPsi q t s w μ ≤ η) :
    ∃ C1 C2 C3 C4 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ 0 ≤ C3 ∧ 0 ≤ C4 ∧
      ∀ n : ℕ, 2 ≤ n → ∀ μ : (Fin n → Fin q) → ℝ, IsPMF μ →
        ckVert q t (s / (2 * ((n : ℝ) + 1))) μ -
            s / (2 * n * ((n : ℝ) + 1)) * ckEdgeKL q t μ ≤
          (η + C1 * (1 / Real.sqrt n)) + (C2 * ckDev μ +
            (C3 * Real.sqrt (ckJbar (1 - Real.exp (-(s / ((n : ℝ) + 1)))) μ) +
              C4 * ckIota2 μ)) := by
  obtain ⟨CV, hCV⟩ := ck_vertex hp hs
  obtain ⟨Cmf, hCmf⟩ := ck_mean_fix hp hs.le
  obtain ⟨Cr, hCr⟩ := ck_psi_rate hp hs.le
  have hcb := ck_const_bounds hp
  have hℓ : 0 < ckEll q t := hcb.2.2.2.2.2.1
  have hmp : 1 < ckMp t := hcb.2.2.1
  have hmm1 : ckMm q t < 1 := hcb.2.1
  have hgap : 0 ≤ ckMp t - ckMm q t := by linarith
  have hCV' : 0 ≤ max CV 0 := le_max_right _ _
  have hCmf' : 0 ≤ max Cmf 0 := le_max_right _ _
  have hCr' : 0 ≤ max Cr 0 := le_max_right _ _
  refine ⟨max Cr 0 * s + max CV 0 + s * ckEll q t * (ckMp t - ckMm q t) / 2,
    max Cmf 0 + max CV 0, max CV 0, s * ckEll q t * ckMp t, ?_, ?_, hCV', ?_, ?_⟩
  · have h1 : 0 ≤ max Cr 0 * s := mul_nonneg hCr' hs.le
    have h2 : 0 ≤ s * ckEll q t * (ckMp t - ckMm q t) / 2 :=
      div_nonneg (mul_nonneg (mul_nonneg hs.le hℓ.le) hgap) (by norm_num)
    linarith
  · linarith
  · exact mul_nonneg (mul_nonneg hs.le hℓ.le) (by linarith)
  intro n hn μ hμ
  have hn0 : 0 < n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hsqn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hsqn_le : Real.sqrt (n : ℝ) ≤ n := by
    rw [Real.sqrt_le_left hnpos.le]; nlinarith
  have hinv1 : 1 / (n : ℝ) ≤ 1 / Real.sqrt n := one_div_le_one_div_of_le hsqn hsqn_le
  have hinv2 : 1 / ((n : ℝ) + 1) ≤ 1 / Real.sqrt n :=
    one_div_le_one_div_of_le hsqn (by linarith)
  have hu0 : 0 ≤ 1 / Real.sqrt (n : ℝ) := by positivity
  -- the rate `r = s n / (n + 1)`
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = s * n / ((n : ℝ) + 1) := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hrs : r ≤ s := by rw [hr, div_le_iff₀ hn1pos]; nlinarith
  have hsr : s - r = s * (1 / ((n : ℝ) + 1)) := by rw [hr]; field_simp; ring
  have hβ : s / (2 * n * ((n : ℝ) + 1)) * (n : ℝ) ^ 2 = r / 2 := by
    rw [hr]; field_simp
  -- the empirical law of the marginals
  have hlaw : ckFinLaw q (fun _ : Fin n => (n : ℝ)⁻¹) (ckMarg μ) := by
    unfold ckFinLaw
    refine ⟨fun _ => by positivity, ?_, fun v => ck_marg_mem hμ v⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_inv_cancel₀ hnpos.ne']
  obtain ⟨w', μ', hPu, hmf⟩ := hCmf n _ _ hlaw
  have h1 := hmf r hr0 hrs
  have h2 := hCr (n + 1) w' μ' hPu.1 r hr0 hrs
  have h3 := hη (n + 1) w' μ' hPu
  have h4 := hCV n hn μ hμ
  rw [← hr] at h4
  have h5 := ck_edge_pairwise hp hn0 hμ
  have h6 := ck_mean_dev_le hn0 hμ
  simp only [Finset.mul_sum] at h1 h6
  have hdev := ckM_dev_mem hμ
  have hJ0 : 0 ≤ Real.sqrt (ckJbar (1 - Real.exp (-(s / ((n : ℝ) + 1)))) μ) :=
    Real.sqrt_nonneg _
  have hι0 : 0 ≤ ckIota2 μ := Real.sqrt_nonneg _
  -- mean fixing: `Ψ_r(ρ_μ) ≤ Ψ_r(ρ'_μ) + C_mf dev(μ)`
  have hF : ∀ X : ℝ, 0 ≤ X → X ≤ ckDev μ → Cmf * X ≤ max Cmf 0 * ckDev μ :=
    fun X hX0 hX => (mul_le_mul_of_nonneg_right (le_max_left _ _) hX0).trans
      (mul_le_mul_of_nonneg_left hX hCmf')
  have h7 := hF _ (Real.sqrt_nonneg _) h6
  have h1' := (abs_sub_le_iff.mp h1).2
  -- rate change
  have h2' := (abs_sub_le_iff.mp h2).2
  have hCrb : Cr * (s - r) ≤ max Cr 0 * s * (1 / Real.sqrt n) := by
    calc Cr * (s - r) ≤ max Cr 0 * (s - r) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
      _ = max Cr 0 * s * (1 / ((n : ℝ) + 1)) := by rw [hsr]; ring
      _ ≤ max Cr 0 * s * (1 / Real.sqrt n) :=
          mul_le_mul_of_nonneg_left hinv2 (mul_nonneg hCr' hs.le)
  have hII : ckPsi q t r (fun _ : Fin n => (n : ℝ)⁻¹) (ckMarg μ) ≤
      η + max Cr 0 * s * (1 / Real.sqrt n) + max Cmf 0 * ckDev μ := by
    linarith
  -- the vertex term with a nonnegative constant
  have hCVb : CV * (1 / Real.sqrt n + ckDev μ +
        Real.sqrt (ckJbar (1 - Real.exp (-(s / ((n : ℝ) + 1)))) μ)) ≤
      max CV 0 * (1 / Real.sqrt n + ckDev μ +
        Real.sqrt (ckJbar (1 - Real.exp (-(s / ((n : ℝ) + 1)))) μ)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith [hdev.1])
  -- the edge term
  have hE : r / 2 * (ckBE q t (fun _ => (n : ℝ)⁻¹) (ckMarg μ) -
        2 * ckEll q t * ckMp t * ckIota2 μ - ckEll q t * (ckMp t - ckMm q t) / n) ≤
      s / (2 * n * ((n : ℝ) + 1)) * ckEdgeKL q t μ := by
    rw [← hβ, mul_assoc]
    exact mul_le_mul_of_nonneg_left h5 (by positivity)
  have hPsi : ckPsi q t r (fun _ : Fin n => (n : ℝ)⁻¹) (ckMarg μ) =
      ckBV q t r (fun _ : Fin n => (n : ℝ)⁻¹) (ckMarg μ) -
        r / 2 * ckBE q t (fun _ : Fin n => (n : ℝ)⁻¹) (ckMarg μ) := rfl
  have hI : ckVert q t (s / (2 * ((n : ℝ) + 1))) μ -
        s / (2 * n * ((n : ℝ) + 1)) * ckEdgeKL q t μ ≤
      ckPsi q t r (fun _ : Fin n => (n : ℝ)⁻¹) (ckMarg μ) +
        max CV 0 * (1 / Real.sqrt n + ckDev μ +
          Real.sqrt (ckJbar (1 - Real.exp (-(s / ((n : ℝ) + 1)))) μ)) +
        (r / 2 * (2 * ckEll q t * ckMp t * ckIota2 μ) +
          r / 2 * (ckEll q t * (ckMp t - ckMm q t) / n)) := by
    calc ckVert q t (s / (2 * ((n : ℝ) + 1))) μ -
          s / (2 * n * ((n : ℝ) + 1)) * ckEdgeKL q t μ ≤
        ckBV q t r (fun _ : Fin n => (n : ℝ)⁻¹) (ckMarg μ) +
          max CV 0 * (1 / Real.sqrt n + ckDev μ +
            Real.sqrt (ckJbar (1 - Real.exp (-(s / ((n : ℝ) + 1)))) μ)) -
          r / 2 * (ckBE q t (fun _ => (n : ℝ)⁻¹) (ckMarg μ) -
            2 * ckEll q t * ckMp t * ckIota2 μ - ckEll q t * (ckMp t - ckMm q t) / n) := by
          linarith
      _ = _ := by rw [hPsi]; ring
  have hIII : r / 2 * (2 * ckEll q t * ckMp t * ckIota2 μ) ≤
      s * ckEll q t * ckMp t * ckIota2 μ := by
    have : 0 ≤ ckEll q t * ckMp t * ckIota2 μ :=
      mul_nonneg (mul_nonneg hℓ.le (by linarith)) hι0
    calc r / 2 * (2 * ckEll q t * ckMp t * ckIota2 μ) =
          r * (ckEll q t * ckMp t * ckIota2 μ) := by ring
      _ ≤ s * (ckEll q t * ckMp t * ckIota2 μ) := mul_le_mul_of_nonneg_right hrs this
      _ = s * ckEll q t * ckMp t * ckIota2 μ := by ring
  have hIV : r / 2 * (ckEll q t * (ckMp t - ckMm q t) / n) ≤
      s * ckEll q t * (ckMp t - ckMm q t) / 2 * (1 / Real.sqrt n) := by
    have hc : 0 ≤ ckEll q t * (ckMp t - ckMm q t) / 2 :=
      div_nonneg (mul_nonneg hℓ.le hgap) (by norm_num)
    have hrn : r * (1 / (n : ℝ)) ≤ s * (1 / Real.sqrt n) :=
      mul_le_mul hrs hinv1 (by positivity) hs.le
    calc r / 2 * (ckEll q t * (ckMp t - ckMm q t) / n) =
          ckEll q t * (ckMp t - ckMm q t) / 2 * (r * (1 / (n : ℝ))) := by ring
      _ ≤ ckEll q t * (ckMp t - ckMm q t) / 2 * (s * (1 / Real.sqrt n)) :=
          mul_le_mul_of_nonneg_left hrn hc
      _ = s * ckEll q t * (ckMp t - ckMm q t) / 2 * (1 / Real.sqrt n) := by ring
  calc ckVert q t (s / (2 * ((n : ℝ) + 1))) μ -
        s / (2 * n * ((n : ℝ) + 1)) * ckEdgeKL q t μ ≤ _ := hI
    _ ≤ (η + max Cr 0 * s * (1 / Real.sqrt n) + max Cmf 0 * ckDev μ) +
          max CV 0 * (1 / Real.sqrt n + ckDev μ +
            Real.sqrt (ckJbar (1 - Real.exp (-(s / ((n : ℝ) + 1)))) μ)) +
          (s * ckEll q t * ckMp t * ckIota2 μ +
            s * ckEll q t * (ckMp t - ckMm q t) / 2 * (1 / Real.sqrt n)) :=
        add_le_add (add_le_add hII le_rfl) (add_le_add hIII hIV)
    _ = _ := by ring

/-! ### Proposition 8.1: one pin level `k` -/

/-- `π_k(n+1) = 1 - (1-p)^k` with `p = 1 - e^{-s/(n+1)}`. -/
private lemma ckM_pin_eq {s : ℝ} {n : ℕ} {p : ℝ}
    (hpdef : p = 1 - Real.exp (-(s / ((n : ℝ) + 1)))) (k : ℕ) :
    ckPin s k (n + 1) = 1 - (1 - p) ^ k := by
  rw [hpdef, sub_sub_cancel, ← Real.exp_nat_mul]
  unfold ckPin
  congr 2
  push_cast
  ring

/-- Expectation of the per-posterior bound at pin level `k`. -/
private lemma ckM_step_k {q : ℕ} {t : ℝ} (hp : CKPar q t) {s η : ℝ} (hs : 0 < s)
    {C1 C2 C3 C4 : ℝ} (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hpost : ∀ n : ℕ, 2 ≤ n → ∀ μ : (Fin n → Fin q) → ℝ, IsPMF μ →
        ckVert q t (s / (2 * ((n : ℝ) + 1))) μ -
            s / (2 * n * ((n : ℝ) + 1)) * ckEdgeKL q t μ ≤
          (η + C1 * (1 / Real.sqrt n)) + (C2 * ckDev μ +
            (C3 * Real.sqrt (ckJbar (1 - Real.exp (-(s / ((n : ℝ) + 1)))) μ) +
              C4 * ckIota2 μ)))
    {n : ℕ} (hn : 2 ≤ n) {ϱ p : ℝ} (hϱ : ϱ = s / (2 * ((n : ℝ) + 1)))
    (hpdef : p = 1 - Real.exp (-(s / ((n : ℝ) + 1)))) (k : ℕ) :
    ckA q t s (n + 1) k - ckA q t s n k ≤
      (η + (C1 + C2) * (1 / Real.sqrt n)) +
        (C3 * Real.sqrt (ckQExp q t ϱ (1 - (1 - p) ^ k) n
            (fun σ G U => ckJbar p (ckPost q t ϱ G U σ))) +
          C4 * Real.sqrt (ckQExp q t ϱ (1 - (1 - p) ^ k) n
            (fun σ G U => ckIota2 (ckPost q t ϱ G U σ) ^ 2))) +
        k * s * Real.log q / ((n : ℝ) + 1) := by
  have hn0 : 0 < n := by omega
  have hϱ0 : 0 ≤ ϱ := by rw [hϱ]; positivity
  have hp0 : 0 ≤ p := by
    rw [hpdef, sub_nonneg, Real.exp_le_one_iff, neg_nonpos]; positivity
  have hp1 : p ≤ 1 := by
    rw [hpdef]; linarith [Real.exp_pos (-(s / ((n : ℝ) + 1)))]
  have hπ0 : 0 ≤ 1 - (1 - p) ^ k := by
    rw [sub_nonneg]; exact pow_le_one₀ (by linarith) (by linarith)
  have hπ1 : 1 - (1 - p) ^ k ≤ 1 := by
    have := pow_nonneg (show (0 : ℝ) ≤ 1 - p by linarith) k
    linarith
  -- the cavity decomposition at pin level `k`
  have hdec := ck_step_decomp hp hs.le hn0 k
  rw [ckM_pin_eq hpdef k, ← hϱ] at hdec
  -- the per-posterior bound, with `ϱ` and `p`
  have hpost' : ∀ μ : (Fin n → Fin q) → ℝ, IsPMF μ →
      ckVert q t ϱ μ - s / (2 * n * ((n : ℝ) + 1)) * ckEdgeKL q t μ ≤
        (η + C1 * (1 / Real.sqrt n)) + (C2 * ckDev μ +
          (C3 * Real.sqrt (ckJbar p μ) + C4 * ckIota2 μ)) := by
    intro μ hμ
    have h := hpost n hn μ hμ
    rw [← hϱ, ← hpdef] at h
    exact h
  -- boundedness of everything under `𝖰`
  obtain ⟨BV, hBV⟩ := ck_vert_bdd (n := n) hp hϱ0
  have hβ0 : 0 ≤ s / (2 * n * ((n : ℝ) + 1)) := by positivity
  have hfb : ∀ (σ : Fin n → Fin q) (G : RSGraph n) (U : Finset (Fin n)), |ckVert q t ϱ (ckPost q t ϱ G U σ) -
      s / (2 * n * ((n : ℝ) + 1)) * ckEdgeKL q t (ckPost q t ϱ G U σ)| ≤
      BV + s / (2 * n * ((n : ℝ) + 1)) * ((n : ℝ) ^ 2 * (1 + ckEll q t * ckMp t)) := by
    intro σ G U
    have hμ := ck_post_isPMF hp hϱ0 G U σ
    have h1 := abs_le.mp (hBV _ hμ)
    have h2 := ck_edgeKL_mem hp hμ
    have h3 := mul_le_mul_of_nonneg_left h2.2 hβ0
    have h4 := mul_nonneg hβ0 h2.1
    rw [abs_le]
    constructor <;> linarith
  have hdevb : ∀ (σ : Fin n → Fin q) (G : RSGraph n) (U : Finset (Fin n)), |ckDev (ckPost q t ϱ G U σ)| ≤
      ∑ τ : Fin n → Fin q, Real.sqrt (rsDevSq τ) := by
    intro σ G U
    have h := ckM_dev_mem (ck_post_isPMF hp hϱ0 G U σ)
    rw [abs_of_nonneg h.1]; exact h.2
  have hJb : ∀ (σ : Fin n → Fin q) (G : RSGraph n) (U : Finset (Fin n)), |ckJbar p (ckPost q t ϱ G U σ)| ≤ n * Real.log q := by
    intro σ G U
    have h := ckM_Jbar_mem (ck_post_isPMF hp hϱ0 G U σ) hp0 hp1
    rw [abs_of_nonneg h.1]; exact h.2
  have hJ0 : ∀ (σ : Fin n → Fin q) (G : RSGraph n) (U : Finset (Fin n)), 0 ≤ ckJbar p (ckPost q t ϱ G U σ) := fun σ G U =>
    (ckM_Jbar_mem (ck_post_isPMF hp hϱ0 G U σ) hp0 hp1).1
  have hsJb : ∀ (σ : Fin n → Fin q) (G : RSGraph n) (U : Finset (Fin n)), |Real.sqrt (ckJbar p (ckPost q t ϱ G U σ))| ≤
      Real.sqrt (n * Real.log q) := by
    intro σ G U
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (ckM_Jbar_mem (ck_post_isPMF hp hϱ0 G U σ) hp0 hp1).2
  have hιb : ∀ (σ : Fin n → Fin q) (G : RSGraph n) (U : Finset (Fin n)), |ckIota2 (ckPost q t ϱ G U σ)| ≤
      Real.sqrt (((n : ℝ) ^ 2)⁻¹ * ∑ v : Fin n, ∑ _w ∈ Finset.univ.erase v, Real.log q) := by
    intro σ G U
    have h := ckM_iota_mem (ck_post_isPMF hp hϱ0 G U σ)
    rw [abs_of_nonneg h.1]; exact h.2
  have hι2b : ∀ (σ : Fin n → Fin q) (G : RSGraph n) (U : Finset (Fin n)), |ckIota2 (ckPost q t ϱ G U σ) ^ 2| ≤
      Real.sqrt (((n : ℝ) ^ 2)⁻¹ * ∑ v : Fin n, ∑ _w ∈ Finset.univ.erase v, Real.log q) ^ 2 := by
    intro σ G U
    have h := ckM_iota_mem (ck_post_isPMF hp hϱ0 G U σ)
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ h.1 h.2 2
  -- `E[f] ≤ E[g]`
  have hmono := ck_QExp_mono hp hϱ0 hπ0 hπ1 (ckM_dom hfb)
    (ckM_dom (ckM_bdd_lin (η + C1 * (1 / Real.sqrt n)) C2 C3 C4 hdevb hsJb hιb))
    (fun σ G U => hpost' _ (ck_post_isPMF hp hϱ0 G U σ))
  rw [ckM_QExp_lin hp hϱ0 _ _ _ _ _ hdevb hsJb hιb] at hmono
  -- the three expectations
  have hdev := ck_magnetization hp hn0 hϱ0 hπ0 hπ1
  have hsJ := ck_QExp_sqrt_le hp hϱ0 hπ0 hπ1 hJ0 (ckM_dom hJb)
  have hι := ck_QExp_sqrt_le hp hϱ0 hπ0 hπ1 (fun σ G U => sq_nonneg (ckIota2 (ckPost q t ϱ G U σ)))
    (ckM_dom hι2b)
  have hιeq : ckQExp q t ϱ (1 - (1 - p) ^ k) n (fun σ G U => ckIota2 (ckPost q t ϱ G U σ)) =
      ckQExp q t ϱ (1 - (1 - p) ^ k) n
        (fun σ G U => Real.sqrt (ckIota2 (ckPost q t ϱ G U σ) ^ 2)) := by
    congr 1
    funext σ G U
    exact (Real.sqrt_sq (Real.sqrt_nonneg _)).symm
  rw [← hιeq] at hι
  have h1 : C2 * ckQExp q t ϱ (1 - (1 - p) ^ k) n
      (fun σ G U => ckDev (ckPost q t ϱ G U σ)) ≤ C2 * (1 / Real.sqrt n) :=
    mul_le_mul_of_nonneg_left hdev hC2
  have h2 := mul_le_mul_of_nonneg_left hsJ hC3
  have h3 := mul_le_mul_of_nonneg_left hι hC4
  linarith

/-! ### Proposition 8.1: averaging over the pin levels -/

private lemma ckM_pi_mem {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    0 ≤ 1 - (1 - p) ^ k ∧ 1 - (1 - p) ^ k ≤ 1 := by
  constructor
  · rw [sub_nonneg]; exact pow_le_one₀ (by linarith) (by linarith)
  · have := pow_nonneg (show (0 : ℝ) ≤ 1 - p by linarith) k
    linarith

private lemma ckM_QExp_J_nonneg {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ π p : ℝ} (hϱ : 0 ≤ ϱ)
    (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ ckQExp q t ϱ π n (fun σ G U => ckJbar p (ckPost q t ϱ G U σ)) := by
  refine ckM_QExp_nonneg hp hϱ hπ0 hπ1 (B := n * Real.log q) (fun σ G U => ?_)
    (fun σ G U => (ckM_Jbar_mem (ck_post_isPMF hp hϱ G U σ) hp0 hp1).1)
  have h := ckM_Jbar_mem (ck_post_isPMF hp hϱ G U σ) hp0 hp1
  rw [abs_of_nonneg h.1]; exact h.2

private lemma ckM_QExp_iota_nonneg {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ π : ℝ} (hϱ : 0 ≤ ϱ)
    (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) :
    0 ≤ ckQExp q t ϱ π n (fun σ G U => ckIota2 (ckPost q t ϱ G U σ) ^ 2) := by
  refine ckM_QExp_nonneg hp hϱ hπ0 hπ1
    (B := Real.sqrt (((n : ℝ) ^ 2)⁻¹ * ∑ v : Fin n, ∑ _w ∈ Finset.univ.erase v, Real.log q) ^ 2)
    (fun σ G U => ?_) (fun σ G U => sq_nonneg _)
  have h := ckM_iota_mem (ck_post_isPMF hp hϱ G U σ)
  rw [abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ h.1 h.2 2

private lemma ckM_avg_add3 {T : ℕ} (hT : 1 ≤ T) (A c d : ℝ) (x y : ℕ → ℝ) :
    (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, (A + (c * x k + d * y k)) =
      A + (c * ((T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, x k) +
        d * ((T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, y k)) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    mul_add, ckM_avg_const hT]
  ring

/-- `p/(1-p) · n ≤ s e^s` for `p = 1 - e^{-a}`, `a = s/(n+1)`. -/
private lemma ckM_pJ_le {q : ℕ} {s : ℝ} (hs : 0 < s) {n : ℕ} (hn : 1 ≤ n) {p : ℝ}
    (hpdef : p = 1 - Real.exp (-(s / ((n : ℝ) + 1)))) :
    p / (1 - p) * (n * Real.log q) ≤ s * Real.exp s * Real.log q := by
  have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = s / ((n : ℝ) + 1) := ⟨_, rfl⟩
  rw [← ha] at hpdef
  have ha0 : 0 < a := by rw [ha]; positivity
  have has : a ≤ s := by rw [ha]; exact div_le_self hs.le (by linarith)
  have han : a * n ≤ s := by
    rw [ha, div_mul_eq_mul_div, div_le_iff₀ hn1pos]; nlinarith
  have hpa : p ≤ a := by
    have := Real.add_one_le_exp (-a)
    rw [hpdef]; linarith
  have h1p : 1 - p = Real.exp (-a) := by rw [hpdef]; ring
  have h1 : p * Real.exp a ≤ a * Real.exp s :=
    mul_le_mul hpa (Real.exp_le_exp.mpr has) (Real.exp_pos a).le ha0.le
  have hpn : p * Real.exp a * n ≤ s * Real.exp s := by
    calc p * Real.exp a * n ≤ a * Real.exp s * n :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ = (a * n) * Real.exp s := by ring
      _ ≤ s * Real.exp s := mul_le_mul_of_nonneg_right han (Real.exp_pos s).le
  calc p / (1 - p) * (n * Real.log q) = (p * Real.exp a * n) * Real.log q := by
        rw [h1p, Real.exp_neg, div_inv_eq_mul]; ring
    _ ≤ (s * Real.exp s) * Real.log q := mul_le_mul_of_nonneg_right hpn hlogq

/-- `(1 + np)/(np) ≤ 1 + (2+s)/s` for `p = 1 - e^{-a}`, `a = s/(n+1)`. -/
private lemma ckM_pι_le {q : ℕ} {s : ℝ} (hs : 0 < s) {n : ℕ} (hn : 1 ≤ n) {p : ℝ}
    (hpdef : p = 1 - Real.exp (-(s / ((n : ℝ) + 1)))) :
    (1 + n * p) / (n * p) * Real.log q ≤ (1 + (2 + s) / s) * Real.log q := by
  have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = s / ((n : ℝ) + 1) := ⟨_, rfl⟩
  rw [← ha] at hpdef
  have ha0 : 0 < a := by rw [ha]; positivity
  have hexp_pos : 0 < Real.exp (-a) := Real.exp_pos _
  have hp0 : 0 < p := by
    have : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    rw [hpdef]; linarith
  have hea : Real.exp (-a) * (1 + a) ≤ 1 := by
    have h := Real.add_one_le_exp a
    calc Real.exp (-a) * (1 + a) ≤ Real.exp (-a) * Real.exp a :=
          mul_le_mul_of_nonneg_left (by linarith) hexp_pos.le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hpa1 : a ≤ p * (1 + a) := by rw [hpdef]; nlinarith
  have han1 : a * ((n : ℝ) + 1) = s := by rw [ha]; field_simp
  have h2 : s ≤ p * ((n : ℝ) + 1 + s) := by
    have h3 := mul_le_mul_of_nonneg_right hpa1 hn1pos.le
    have e : p * (1 + a) * ((n : ℝ) + 1) = p * ((n : ℝ) + 1) + p * (a * ((n : ℝ) + 1)) := by
      ring
    rw [e, han1] at h3
    linarith
  have h4 : p * ((n : ℝ) + 1 + s) ≤ n * p * (2 + s) := by
    have := mul_nonneg (mul_nonneg hp0.le (by linarith : (0 : ℝ) ≤ n - 1))
      (by linarith : (0 : ℝ) ≤ 1 + s)
    linarith
  have hnp0 : 0 < (n : ℝ) * p := mul_pos (by linarith) hp0
  have hnp : s / (2 + s) ≤ n * p := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hinv : 1 / ((n : ℝ) * p) ≤ (2 + s) / s := by
    have := one_div_le_one_div_of_le (by positivity) hnp
    rwa [one_div_div] at this
  have e : (1 + n * p) / (n * p) = 1 / ((n : ℝ) * p) + 1 := by
    field_simp
  rw [e]
  apply mul_le_mul_of_nonneg_right _ hlogq
  linarith

-- Proposition 8.1 (η-hypothesis on finitely supported laws only)
theorem ck_step_avg {q : ℕ} {t : ℝ} (hp : CKPar q t) {s η : ℝ} (hs : 0 < s)
    (hη : ∀ (K : ℕ) (w : Fin K → ℝ) (μ : Fin K → Fin q → ℝ), ckFinPu q w μ →
      ckPsi q t s w μ ≤ η) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ T : ℕ, 1 ≤ T →
      (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, (ckA q t s (n + 1) k - ckA q t s n k) ≤
        η + C * (1 / Real.sqrt n + 1 / Real.sqrt T) + T * s * Real.log q / ((n : ℝ) + 1) := by
  obtain ⟨C1, C2, C3, C4, hC1, hC2, hC3, hC4, hpost⟩ := ckM_post_bound hp hs hη
  have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hKJ : 0 ≤ s * Real.exp s * Real.log q := by positivity
  have hKι : 0 ≤ (1 + (2 + s) / s) * Real.log q := by positivity
  refine ⟨C1 + C2 + C3 * Real.sqrt (s * Real.exp s * Real.log q) +
    C4 * Real.sqrt ((1 + (2 + s) / s) * Real.log q), ?_⟩
  intro n hn T hT
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  obtain ⟨ϱ, hϱ⟩ : ∃ ϱ : ℝ, ϱ = s / (2 * ((n : ℝ) + 1)) := ⟨_, rfl⟩
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = 1 - Real.exp (-(s / ((n : ℝ) + 1))) := ⟨_, rfl⟩
  have hϱ0 : 0 ≤ ϱ := by rw [hϱ]; positivity
  have hexp_pos : 0 < Real.exp (-(s / ((n : ℝ) + 1))) := Real.exp_pos _
  have hsn : 0 < s / ((n : ℝ) + 1) := by positivity
  have hexp_lt : Real.exp (-(s / ((n : ℝ) + 1))) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hp0 : 0 < p := by rw [hpdef]; linarith
  have hp1 : p < 1 := by rw [hpdef]; linarith
  -- the bound at each pin level
  have hk : ∀ k ∈ Finset.range T, ckA q t s (n + 1) k - ckA q t s n k ≤
      (η + (C1 + C2) * (1 / Real.sqrt n) + T * s * Real.log q / ((n : ℝ) + 1)) +
        (C3 * Real.sqrt (ckQExp q t ϱ (1 - (1 - p) ^ k) n
            (fun σ G U => ckJbar p (ckPost q t ϱ G U σ))) +
          C4 * Real.sqrt (ckQExp q t ϱ (1 - (1 - p) ^ k) n
            (fun σ G U => ckIota2 (ckPost q t ϱ G U σ) ^ 2))) := by
    intro k hk
    have h := ckM_step_k hp hs hC2 hC3 hC4 hpost hn hϱ hpdef k
    have hkT : (k : ℝ) * s * Real.log q / ((n : ℝ) + 1) ≤
        T * s * Real.log q / ((n : ℝ) + 1) := by
      apply div_le_div_of_nonneg_right _ hn1pos.le
      have : (k : ℝ) ≤ T := by exact_mod_cast (Finset.mem_range.mp hk).le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hs.le) hlogq
    linarith
  have hsum := ckM_avg_mono hk
  rw [ckM_avg_add3 hT] at hsum
  -- Jensen and Corollary 6.2(a)
  have hJ : (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, Real.sqrt (ckQExp q t ϱ (1 - (1 - p) ^ k) n
      (fun σ G U => ckJbar p (ckPost q t ϱ G U σ))) ≤
      Real.sqrt (s * Real.exp s * Real.log q) * (1 / Real.sqrt T) := by
    calc _ ≤ Real.sqrt ((T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, ckQExp q t ϱ (1 - (1 - p) ^ k) n
          (fun σ G U => ckJbar p (ckPost q t ϱ G U σ))) :=
          ckM_avg_sqrt_le hT (fun k _ => ckM_QExp_J_nonneg hp hϱ0
            (ckM_pi_mem hp0.le hp1.le k).1 (ckM_pi_mem hp0.le hp1.le k).2 hp0.le hp1.le)
      _ ≤ Real.sqrt (s * Real.exp s * Real.log q / T) := by
          apply Real.sqrt_le_sqrt
          refine (ck_pin_post_J (n := n) hp hϱ0 hp0 hp1 hT).trans ?_
          exact div_le_div_of_nonneg_right (ckM_pJ_le hs hn1 hpdef) hT0.le
      _ = Real.sqrt (s * Real.exp s * Real.log q) * (1 / Real.sqrt T) := by
          rw [Real.sqrt_div hKJ, div_eq_mul_one_div]
  -- Jensen and Corollary 6.2(b)
  have hι : (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, Real.sqrt (ckQExp q t ϱ (1 - (1 - p) ^ k) n
      (fun σ G U => ckIota2 (ckPost q t ϱ G U σ) ^ 2)) ≤
      Real.sqrt ((1 + (2 + s) / s) * Real.log q) * (1 / Real.sqrt T) := by
    calc _ ≤ Real.sqrt ((T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, ckQExp q t ϱ (1 - (1 - p) ^ k) n
          (fun σ G U => ckIota2 (ckPost q t ϱ G U σ) ^ 2)) :=
          ckM_avg_sqrt_le hT (fun k _ => ckM_QExp_iota_nonneg hp hϱ0
            (ckM_pi_mem hp0.le hp1.le k).1 (ckM_pi_mem hp0.le hp1.le k).2)
      _ ≤ Real.sqrt ((1 + (2 + s) / s) * Real.log q / T) := by
          apply Real.sqrt_le_sqrt
          refine (ck_pin_post_iota (n := n) hp hn hϱ0 hp0 hp1 hT).trans ?_
          exact div_le_div_of_nonneg_right (ckM_pι_le hs hn1 hpdef) hT0.le
      _ = Real.sqrt ((1 + (2 + s) / s) * Real.log q) * (1 / Real.sqrt T) := by
          rw [Real.sqrt_div hKι, div_eq_mul_one_div]
  have h3 := mul_le_mul_of_nonneg_left hJ hC3
  have h4 := mul_le_mul_of_nonneg_left hι hC4
  have hu : 0 ≤ 1 / Real.sqrt (n : ℝ) := by positivity
  have hv : 0 ≤ 1 / Real.sqrt (T : ℝ) := by positivity
  have e1 : 0 ≤ (C1 + C2) * (1 / Real.sqrt (T : ℝ)) := mul_nonneg (add_nonneg hC1 hC2) hv
  have e2 : 0 ≤ (C3 * Real.sqrt (s * Real.exp s * Real.log q) +
      C4 * Real.sqrt ((1 + (2 + s) / s) * Real.log q)) * (1 / Real.sqrt (n : ℝ)) :=
    mul_nonneg (add_nonneg (mul_nonneg hC3 (Real.sqrt_nonneg _))
      (mul_nonneg hC4 (Real.sqrt_nonneg _))) hu
  linarith

-- Proposition 8.2
theorem ck_cesaro {q : ℕ} {t : ℝ} (hp : CKPar q t) {s η : ℝ} (hs : 0 < s)
    (hη : ∀ (K : ℕ) (w : Fin K → ℝ) (μ : Fin K → Fin q → ℝ), ckFinPu q w μ →
      ckPsi q t s w μ ≤ η) :
    ∃ C : ℝ, ∀ T : ℕ, 1 ≤ T → ∀ N : ℕ, 3 ≤ N →
      rsFbar q N s t ≤ N * η + C * (1 + Real.sqrt N + N / Real.sqrt T) +
        T * s * Real.log q * (1 + Real.log N) := by
  obtain ⟨C, hC⟩ := ck_step_avg hp hs hη
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by linarith [hp.two_le] : 1 ≤ q)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hcb := ck_const_bounds hp
  set C1 := max C 0 with hC1def
  have hC1 : 0 ≤ C1 := le_max_right _ _
  have hCC1 : C ≤ C1 := le_max_left _ _
  set C0 := 2 * Real.log q + s * 2 / 2 * (1 + ckMp t * ckEll q t) with hC0def
  have hC0 : 0 ≤ C0 := by
    have : 0 ≤ ckMp t * ckEll q t := mul_nonneg (by linarith [hcb.2.2.1]) hcb.2.2.2.2.2.1.le
    have : 0 ≤ s * 2 / 2 * (1 + ckMp t * ckEll q t) := by positivity
    linarith
  refine ⟨2 * |η| + C0 + 2 * C1, ?_⟩
  intro T hT N hN
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hTs : 0 ≤ (T : ℝ) * s * Real.log q := by positivity
  set A : ℕ → ℝ := fun M => (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, ckA q t s M k with hAdef
  -- the averaged step bound with a nonnegative constant
  have hstep : ∀ n : ℕ, 2 ≤ n → A (n + 1) - A n ≤
      η + C1 * (1 / Real.sqrt n + 1 / Real.sqrt T) + T * s * Real.log q / ((n : ℝ) + 1) := by
    intro n hn
    have h := hC n hn T hT
    have e : A (n + 1) - A n =
        (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, (ckA q t s (n + 1) k - ckA q t s n k) := by
      simp only [hAdef, Finset.sum_sub_distrib, mul_sub]
    rw [e]
    have : C * (1 / Real.sqrt n + 1 / Real.sqrt T) ≤ C1 * (1 / Real.sqrt n + 1 / Real.sqrt T) :=
      mul_le_mul_of_nonneg_right hCC1 (by positivity)
    linarith
  -- telescoping
  have htel : ∀ M : ℕ, 2 ≤ M → A M ≤ A 2 + ((M : ℝ) - 2) * η +
      C1 * (2 * Real.sqrt ((M : ℝ) - 1) + ((M : ℝ) - 2) / Real.sqrt T) +
      T * s * Real.log q * Real.log M := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base =>
      have e : ((2 : ℕ) : ℝ) = 2 := by norm_num
      rw [e]
      have e2 : Real.sqrt ((2 : ℝ) - 1) = 1 := by norm_num
      rw [e2]
      simp only [sub_self, zero_mul, zero_div, add_zero, mul_one]
      have hl2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
      have : 0 ≤ T * s * Real.log q * Real.log 2 := mul_nonneg hTs hl2
      nlinarith
    | succ M hM ih =>
      have h1 := hstep M hM
      have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
      have h2 := ckM_sqrt_step hM1
      have h3 := ckM_log_step (by linarith : (0 : ℝ) < M)
      have e1 : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
      rw [e1, show (M : ℝ) + 1 - 1 = M by ring]
      have h4 : C1 * (2 * Real.sqrt ((M : ℝ) - 1) + 1 / Real.sqrt M) ≤
          C1 * (2 * Real.sqrt M) := mul_le_mul_of_nonneg_left h2 hC1
      have h5 : T * s * Real.log q * (Real.log M + 1 / ((M : ℝ) + 1)) ≤
          T * s * Real.log q * Real.log ((M : ℝ) + 1) := mul_le_mul_of_nonneg_left h3 hTs
      have e2 : ((M : ℝ) + 1 - 2) / Real.sqrt T =
          ((M : ℝ) - 2) / Real.sqrt T + 1 / Real.sqrt T := by ring
      rw [e2]
      have e3 : T * s * Real.log q / ((M : ℝ) + 1) =
          T * s * Real.log q * (1 / ((M : ℝ) + 1)) := by ring
      rw [e3] at h1
      linarith
  -- the average at `N = 2`
  have hA2 : A 2 ≤ C0 := by
    have hb : ∀ k ∈ Finset.range T, ckA q t s 2 k ≤ C0 := by
      intro k _
      have h := ck_abs_A_le hp hs.le (N := 2) (by norm_num) k
      have h' := (abs_le.mp h).2
      have e : ((2 : ℕ) : ℝ) = 2 := by norm_num
      rw [e] at h'
      exact h'
    calc A 2 ≤ (T : ℝ)⁻¹ * ∑ _k ∈ Finset.range T, C0 := ckM_avg_mono hb
      _ = C0 := ckM_avg_const hT C0
  -- domination
  have hN0 : 0 < N := by omega
  have hdom : rsFbar q N s t ≤ A N + T * s * Real.log q := by
    have h1 := ck_fbar_le_K hp hN0 hs.le
    have hpin0 : ckPin s 0 N = 0 := by
      unfold ckPin
      rw [Nat.cast_zero, zero_mul, zero_div, neg_zero, Real.exp_zero, sub_self]
    have h2 : ckK q t (s / (2 * N)) 0 N = ckA q t s N 0 := by
      unfold ckA; rw [hpin0]
    have h3 : ∀ k ∈ Finset.range T, ckA q t s N 0 ≤ ckA q t s N k + T * s * Real.log q := by
      intro k hk
      have h := ck_A_zero_le hp hs.le hN0 k
      have hk' : (k : ℝ) ≤ T := by exact_mod_cast (Finset.mem_range.mp hk).le
      have : (k : ℝ) * s * Real.log q ≤ T * s * Real.log q :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk' hs.le) hlogq
      linarith
    have h4 : ckA q t s N 0 ≤ A N + T * s * Real.log q := by
      calc ckA q t s N 0 = (T : ℝ)⁻¹ * ∑ _k ∈ Finset.range T, ckA q t s N 0 :=
            (ckM_avg_const hT _).symm
        _ ≤ (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, (ckA q t s N k + T * s * Real.log q) :=
            ckM_avg_mono h3
        _ = A N + T * s * Real.log q := by
            rw [Finset.sum_add_distrib, mul_add, ckM_avg_const hT]
    rw [h2] at h1
    linarith
  have hN2 : 2 ≤ N := by omega
  have h := htel N hN2
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hsq : Real.sqrt ((N : ℝ) - 1) ≤ Real.sqrt N := Real.sqrt_le_sqrt (by linarith)
  have hsqN : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hsqT : 0 ≤ Real.sqrt (T : ℝ) := Real.sqrt_nonneg _
  have hNT : ((N : ℝ) - 2) / Real.sqrt T ≤ (N : ℝ) / Real.sqrt T :=
    div_le_div_of_nonneg_right (by linarith) hsqT
  have hNT0 : 0 ≤ (N : ℝ) / Real.sqrt T := div_nonneg (by linarith) hsqT
  set F := 1 + Real.sqrt N + N / Real.sqrt T with hFdef
  have hF1 : 1 ≤ F := by linarith
  have h5 : 2 * |η| ≤ 2 * |η| * F := le_mul_of_one_le_right (by positivity) hF1
  have h6 : C0 ≤ C0 * F := le_mul_of_one_le_right hC0 hF1
  have h7 : C1 * (2 * Real.sqrt ((N : ℝ) - 1) + ((N : ℝ) - 2) / Real.sqrt T) ≤
      2 * C1 * F := by
    have : 2 * Real.sqrt ((N : ℝ) - 1) + ((N : ℝ) - 2) / Real.sqrt T ≤ 2 * F := by linarith
    nlinarith
  have h8 : ((N : ℝ) - 2) * η ≤ N * η + 2 * |η| := by
    have := neg_abs_le η
    linarith
  have e : (2 * |η| + C0 + 2 * C1) * F = 2 * |η| * F + C0 * F + 2 * C1 * F := by ring
  rw [e]
  have e' : T * s * Real.log q * (1 + Real.log N) =
      T * s * Real.log q + T * s * Real.log q * Real.log N := by ring
  rw [e']
  linarith

-- (H3) form: Proposition 8.2 + Fact 0.2
theorem ck_planted_fe {q : ℕ} (hq : 2 ≤ q) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {s : ℝ}
    (hs : 0 < s) {η : ℝ} (hη : ∀ ν ∈ rsPu q, bethePsi q s x ν ≤ η) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, rsFbar q n s (tRe q x) ≤ (η + ε) * n := by
  have hp := ckPar_tRe hq hx0 hx1
  have hη' : ∀ (K : ℕ) (w : Fin K → ℝ) (μ : Fin K → Fin q → ℝ), ckFinPu q w μ →
      ckPsi q (tRe q x) s w μ ≤ η := by
    intro K w μ h
    obtain ⟨ν, hν, he⟩ := ck_bethePsi_fin (by omega) h s x
    rw [← he]
    exact hη ν hν
  obtain ⟨C, hC⟩ := ck_cesaro hp hs hη'
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  set C' := max C 0 with hC'def
  have hC' : 0 ≤ C' := le_max_right _ _
  have hCC' : C ≤ C' := le_max_left _ _
  -- the choice of `T`
  set T : ℕ := ⌈(3 * C' / ε) ^ 2⌉₊ + 1 with hTdef
  have hT1 : 1 ≤ T := by omega
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
  have hsqT : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr hT0
  have hTC : C' / Real.sqrt T ≤ ε / 3 := by
    have h1 : (3 * C' / ε) ^ 2 ≤ (T : ℝ) := by
      have := Nat.le_ceil ((3 * C' / ε) ^ 2)
      have h2 : ((⌈(3 * C' / ε) ^ 2⌉₊ : ℕ) : ℝ) ≤ (T : ℝ) := by
        exact_mod_cast (by omega : ⌈(3 * C' / ε) ^ 2⌉₊ ≤ T)
      linarith
    have h3 : 3 * C' / ε ≤ Real.sqrt T :=
      (Real.le_sqrt (by positivity) hT0.le).mpr h1
    rw [div_le_iff₀ hε] at h3
    rw [div_le_iff₀ hsqT]
    linarith
  set K := 2 * C' + 3 * (T * s * Real.log q) with hKdef
  filter_upwards [eventually_ge_atTop 3, ckM_ev_sqrt_le K (by positivity : 0 < 2 * ε / 3)]
    with N hN3 hNK
  have h := hC T hT1 N hN3
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hsqN1 : 1 ≤ Real.sqrt (N : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hN1
  have hlogN := ckM_log_le_two_sqrt hN0
  have hTs : 0 ≤ (T : ℝ) * s * Real.log q := by positivity
  have hNT : 0 ≤ (N : ℝ) / Real.sqrt T := div_nonneg hN0.le hsqT.le
  -- `C (1 + √N + N/√T) ≤ C' (1 + √N) + (ε/3) N`
  have h1 : C * (1 + Real.sqrt N + N / Real.sqrt T) ≤
      C' * (1 + Real.sqrt N + N / Real.sqrt T) :=
    mul_le_mul_of_nonneg_right hCC' (by positivity)
  have h2 : C' * ((N : ℝ) / Real.sqrt T) ≤ ε / 3 * N := by
    rw [mul_div_assoc', mul_comm C' (N : ℝ), mul_div_assoc]
    have := mul_le_mul_of_nonneg_left hTC hN0.le
    linarith
  have h3 : C' * 1 ≤ C' * Real.sqrt N := mul_le_mul_of_nonneg_left hsqN1 hC'
  have h4 : T * s * Real.log q * (1 + Real.log N) ≤ T * s * Real.log q * (3 * Real.sqrt N) :=
    mul_le_mul_of_nonneg_left (by linarith) hTs
  have e1 : C' * (1 + Real.sqrt N + N / Real.sqrt T) =
      C' * 1 + C' * Real.sqrt N + C' * ((N : ℝ) / Real.sqrt T) := by ring
  have e2 : K * Real.sqrt N = 2 * C' * Real.sqrt N + T * s * Real.log q * (3 * Real.sqrt N) := by
    rw [hKdef]; ring
  have e3 : (η + ε) * N = N * η + ε / 3 * N + 2 * ε / 3 * N := by ring
  rw [e3]
  linarith

-- Theorem 0.1: `ck_bridge` + `ck_planted_fe`
theorem ckpz_prop36 {q : ℕ} (hq : 2 ≤ q) : CKPZProp36 q := by
  intro x hx0 hx1 s hs η hη ε hε
  obtain ⟨C, hC⟩ := ck_bridge hq hx0 hx1 hs
  have h1 := ck_planted_fe hq hx0 hx1 hs hη (half_pos hε)
  have h2 := ckM_ev_sqrt_le C (half_pos hε)
  filter_upwards [h1, h2, eventually_ge_atTop 2] with n hn1 hn2 hn3
  obtain ⟨-, hb⟩ := hC n hn3
  have h := (abs_le.mp hb).2
  have e : (η + ε) * n = (η + ε / 2) * n + ε / 2 * n := by ring
  rw [e]
  linarith

end

end ERZeroFreeness
