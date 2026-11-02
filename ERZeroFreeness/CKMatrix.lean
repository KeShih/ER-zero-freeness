/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.CKDefs
import ERZeroFreeness.RSPoisPi
import ERZeroFreeness.RSModel
import ERZeroFreeness.RSBetheBasic
import ERZeroFreeness.RSPoisSplit
import ERZeroFreeness.Poisson

/-!
# Proof of [CKPZ, Prop. 3.6]: the matrix `M` (§0.2, Lemma 1.4)

Part of the proof of `CKPZProp36 q` in the CK* modules (see `CKDefs`), following §0.2 and
Lemma 1.4 of `docs/ckpz-proof.md`.  Under `CKPar q t` the matrix `M = rsM q t` has diagonal
entries `m₋ = 1 + t(q-1) ∈ (0,1)` and off-diagonal entries `m₊ = 1 - t ∈ (1,2]`.

* `ckPar_tRe`: `t(x)` satisfies `CKPar` for `x ∈ (0,1)` (§0.1);
* `ck_rsM_eq`, `ck_rsM_mem`: the entries of `M` (Lemma 1.4(a));
* `ck_const_bounds`, `ck_abs_log_rsM_le`: the constants of §0.2, `m₋ m₊ < 1` and
  `|log M(a,b)| ≤ ℓ₀` (Lemma 1.4(e));
* `ck_betheMvec_mem`, `ck_betheE_mem`, `ck_betheE_self_le_one`: `(Mμ)_c` and `μᵀMν` lie in
  `[m₋, m₊]`, and `μᵀMμ ≤ 1` (Lemma 1.4(b));
* `ck_S_eq`, `ck_S_mem`, `ck_sum_rsM_sub_one`: `S(τ) = tqn²‖λ_τ - u‖² ∈ [-n², 0]` and
  `∑_v (M(τ_v, c) - 1) = tqn(λ_τ(c) - 1/q)` (Lemma 1.4(c));
* `ck_avg_devSq`: `E‖λ_σ - u‖² = (q-1)/(qn)` for uniform `σ` (Lemma 1.4(d)).
-/

open Filter Topology MeasureTheory

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-! ### Private helpers: colour counts and the matrix `A` -/

/-- `A_{ab} = q·[a = b] - 1` as a real number. -/
private lemma ckMat_rsA_cast {q : ℕ} (a b : Fin q) :
    ((rsA q a b : ℤ) : ℝ) = (q : ℝ) * (if a = b then 1 else 0) - 1 := by
  unfold rsA
  split_ifs <;> push_cast <;> ring

/-- `N_c = ∑_v [τ_v = c]`. -/
private lemma ckMat_fiber_eq {n q : ℕ} (τ : Fin n → Fin q) (c : Fin q) :
    (fiberCard τ c : ℝ) = ∑ v, if τ v = c then (1 : ℝ) else 0 := by
  unfold fiberCard
  rw [Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> rfl

/-- `∑_c N_c = n`. -/
private lemma ckMat_sum_fiber {n q : ℕ} (τ : Fin n → Fin q) :
    ∑ c, (fiberCard τ c : ℝ) = n := by
  simp_rw [ckMat_fiber_eq]
  rw [Finset.sum_comm]
  simp

/-- `∑_{u,v} [τ_u = τ_v] = ∑_c N_c²`. -/
private lemma ckMat_pairs_eq {n q : ℕ} (τ : Fin n → Fin q) :
    ∑ u, ∑ v, (if τ u = τ v then (1 : ℝ) else 0) = ∑ c, (fiberCard τ c : ℝ) ^ 2 := by
  have h : ∀ u v, (if τ u = τ v then (1 : ℝ) else 0) =
      ∑ c, (if τ u = c then (1 : ℝ) else 0) * (if τ v = c then (1 : ℝ) else 0) := by
    intro u v
    by_cases huv : τ u = τ v <;> simp [huv]
  simp_rw [h, ckMat_fiber_eq, sq, Finset.sum_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]

/-- One summand of `q n² ‖λ_τ - u‖²`. -/
private lemma ckMat_devSq_term {n q : ℕ} (hq : q ≠ 0) (hn : n ≠ 0) (N : ℝ) :
    (q : ℝ) * (n : ℝ) ^ 2 * (N / n - 1 / (q : ℝ)) ^ 2 =
      (q : ℝ) * N ^ 2 - 2 * n * N + (n : ℝ) ^ 2 / q := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp
  ring

/-- `q n² ‖λ_τ - u‖² = q ∑_c N_c² - n²`. -/
private lemma ckMat_qn2_devSq {n q : ℕ} (hq : q ≠ 0) (τ : Fin n → Fin q) :
    (q : ℝ) * (n : ℝ) ^ 2 * rsDevSq τ =
      (q : ℝ) * ∑ c, (fiberCard τ c : ℝ) ^ 2 - (n : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [fiberCard]
  · have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
    unfold rsDevSq colorFrac
    rw [Finset.mul_sum]
    simp_rw [ckMat_devSq_term hq hn.ne']
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ckMat_sum_fiber]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring

/-- `∑_{u,v} A_{τ_u τ_v} = q n² ‖λ_τ - u‖²`. -/
private lemma ckMat_sum_rsA {n q : ℕ} (hq : q ≠ 0) (τ : Fin n → Fin q) :
    ∑ u, ∑ v, ((rsA q (τ u) (τ v) : ℤ) : ℝ) = (q : ℝ) * (n : ℝ) ^ 2 * rsDevSq τ := by
  rw [ckMat_qn2_devSq hq, ← ckMat_pairs_eq]
  simp_rw [ckMat_rsA_cast]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- `S(τ) = t ∑_{u,v} A_{τ_u τ_v}`. -/
private lemma ckMat_S_eq_rsA {q n : ℕ} (t : ℝ) (τ : Fin n → Fin q) :
    ckS q t τ = t * ∑ u, ∑ v, ((rsA q (τ u) (τ v) : ℤ) : ℝ) := by
  unfold ckS rsM
  rw [Fintype.sum_prod_type]
  simp [Finset.mul_sum]

/-- For `u ≠ v`, `∑_σ A_{σ_u σ_v} = 0`, since the rows of `A` sum to zero. -/
private lemma ckMat_sum_sigma_rsA_of_ne {n q : ℕ} {u v : Fin n} (h : u ≠ v) :
    ∑ σ : Fin n → Fin q, ((rsA q (σ u) (σ v) : ℤ) : ℝ) = 0 := by
  rw [← (Equiv.funSplitAt v (Fin q)).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.funSplitAt_symm_apply, dif_pos, dif_neg h]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun σ' _ => rs_sum_rsA _ _

/-- `∑_σ ∑_{u,v} A_{σ_u σ_v} = q^n · n (q-1)`: only the diagonal pairs `u = v` contribute. -/
private lemma ckMat_sum_sigma_sum_rsA {n q : ℕ} :
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
      exact ckMat_sum_sigma_rsA_of_ne (Ne.symm hv)
    · simp
  rw [Finset.sum_congr rfl fun u _ => hu u]
  simp
  ring

/-- `(M μ)_a = 1 + t (q μ_a - 1)` when `∑_b μ_b = 1`. -/
private lemma ckMat_betheMvec_eq {q : ℕ} (t : ℝ) {μ : Fin q → ℝ} (hμ : ∑ b, μ b = 1)
    (a : Fin q) : betheMvec q t μ a = 1 + t * ((q : ℝ) * μ a - 1) := by
  unfold betheMvec rsM
  simp_rw [ckMat_rsA_cast]
  have h : ∀ b, (1 + t * ((q : ℝ) * (if a = b then 1 else 0) - 1)) * μ b =
      (1 - t) * μ b + t * q * (if a = b then μ b else 0) := by
    intro b
    split_ifs <;> ring
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum, hμ, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  ring


/-- For `x ∈ (0,1)`, `t(x)` satisfies `CKPar` (§0.1). -/
theorem ckPar_tRe {q : ℕ} (hq : 2 ≤ q) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    CKPar q (tRe q x) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hd : 0 < x + q - 1 := by linarith
  refine ⟨hq, ?_, ?_⟩
  · unfold tRe
    exact div_neg_of_neg_of_pos (by linarith) hd
  · unfold tRe
    rw [div_mul_eq_mul_div, lt_div_iff₀ hd]
    nlinarith [mul_pos hx0 (by linarith : (0 : ℝ) < q)]

/-- The entries of `M`: `m₋` on the diagonal and `m₊` off it (Lemma 1.4(a)). -/
theorem ck_rsM_eq (q : ℕ) (t : ℝ) (a b : Fin q) :
    rsM q t a b = if a = b then ckMm q t else ckMp t := by
  unfold rsM rsA ckMm ckMp
  split_ifs <;> push_cast <;> ring

/-- The constants of §0.2: `0 < m₋ < 1 < m₊ ≤ 2`, `m₋ m₊ < 1`, `0 < ℓ₀` and `log m₊ < ℓ₀`
(Lemma 1.4(e)). -/
theorem ck_const_bounds {q : ℕ} {t : ℝ} (hp : CKPar q t) :
    0 < ckMm q t ∧ ckMm q t < 1 ∧ 1 < ckMp t ∧ ckMp t ≤ 2 ∧ ckMm q t * ckMp t < 1 ∧
      0 < ckEll q t ∧ Real.log (ckMp t) < ckEll q t := by
  obtain ⟨hq, ht, hgt⟩ := hp
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have htq : t * ((q : ℝ) - 1) < 0 := mul_neg_of_neg_of_pos ht hq1
  have htt : t * ((q : ℝ) - 1) ≤ t := by nlinarith
  have h1 : 0 < ckMm q t := by unfold ckMm; linarith
  have h2 : ckMm q t < 1 := by unfold ckMm; linarith
  have h3 : 1 < ckMp t := by unfold ckMp; linarith
  have h4 : ckMp t ≤ 2 := by unfold ckMp; linarith
  have h5 : ckMm q t * ckMp t < 1 := by
    unfold ckMm ckMp
    nlinarith [mul_pos (mul_pos_of_neg_of_neg ht ht) hq1]
  have hp3 : 0 < ckMp t := by linarith
  have h6 : 0 < ckEll q t := by
    unfold ckEll
    have := Real.log_neg h1 h2
    linarith
  have h7 : Real.log (ckMp t) < ckEll q t := by
    unfold ckEll
    have := Real.log_neg (mul_pos h1 hp3) h5
    rw [Real.log_mul h1.ne' hp3.ne'] at this
    linarith
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- Every entry of `M` lies in `[m₋, m₊]` (Lemma 1.4(a)). -/
theorem ck_rsM_mem {q : ℕ} {t : ℝ} (hp : CKPar q t) (a b : Fin q) :
    ckMm q t ≤ rsM q t a b ∧ rsM q t a b ≤ ckMp t := by
  obtain ⟨_, h2, h3, -⟩ := ck_const_bounds hp
  rw [ck_rsM_eq]
  split_ifs <;> constructor <;> linarith

/-- `|log M(a,b)| ≤ ℓ₀` (Lemma 1.4(e)). -/
theorem ck_abs_log_rsM_le {q : ℕ} {t : ℝ} (hp : CKPar q t) (a b : Fin q) :
    |Real.log (rsM q t a b)| ≤ ckEll q t := by
  obtain ⟨h1, h2, h3, -, -, -, h7⟩ := ck_const_bounds hp
  rw [ck_rsM_eq]
  split_ifs
  · rw [abs_of_neg (Real.log_neg h1 h2)]
    exact le_of_eq rfl
  · rw [abs_of_pos (Real.log_pos h3)]
    exact h7.le

/-- `(Mμ)_a ∈ [m₋, m₊]` for `μ` in the simplex, as a convex combination of entries of `M`
(Lemma 1.4(b)). -/
theorem ck_betheMvec_mem {q : ℕ} {t : ℝ} (hp : CKPar q t) {μ : Fin q → ℝ}
    (hμ : μ ∈ stdSimplex ℝ (Fin q)) (a : Fin q) :
    ckMm q t ≤ betheMvec q t μ a ∧ betheMvec q t μ a ≤ ckMp t := by
  have hnn : ∀ b, 0 ≤ μ b := hμ.1
  have hsum : ∑ b, μ b = 1 := hμ.2
  unfold betheMvec
  constructor
  · calc ckMm q t = ∑ b, ckMm q t * μ b := by rw [← Finset.mul_sum, hsum, mul_one]
      _ ≤ ∑ b, rsM q t a b * μ b := Finset.sum_le_sum fun b _ =>
          mul_le_mul_of_nonneg_right (ck_rsM_mem hp a b).1 (hnn b)
  · calc ∑ b, rsM q t a b * μ b ≤ ∑ b, ckMp t * μ b := Finset.sum_le_sum fun b _ =>
          mul_le_mul_of_nonneg_right (ck_rsM_mem hp a b).2 (hnn b)
      _ = ckMp t := by rw [← Finset.mul_sum, hsum, mul_one]

/-- `μᵀMν ∈ [m₋, m₊]` for `μ, ν` in the simplex (Lemma 1.4(b)). -/
theorem ck_betheE_mem {q : ℕ} {t : ℝ} (hp : CKPar q t) {μ ν : Fin q → ℝ}
    (hμ : μ ∈ stdSimplex ℝ (Fin q)) (hν : ν ∈ stdSimplex ℝ (Fin q)) :
    ckMm q t ≤ betheE q t μ ν ∧ betheE q t μ ν ≤ ckMp t := by
  have hnn : ∀ a, 0 ≤ μ a := hμ.1
  have hsum : ∑ a, μ a = 1 := hμ.2
  unfold betheE
  constructor
  · calc ckMm q t = ∑ a, μ a * ckMm q t := by rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ a, μ a * betheMvec q t ν a := Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (ck_betheMvec_mem hp hν a).1 (hnn a)
  · calc ∑ a, μ a * betheMvec q t ν a ≤ ∑ a, μ a * ckMp t := Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (ck_betheMvec_mem hp hν a).2 (hnn a)
      _ = ckMp t := by rw [← Finset.sum_mul, hsum, one_mul]

/-- `μᵀMμ = 1 + t(q‖μ‖² - 1) ≤ 1` whenever `∑_a μ_a = 1`, since `t < 0` and `q‖μ‖² ≥ 1`
(Lemma 1.4(b); this is the balance condition BAL). -/
theorem ck_betheE_self_le_one {q : ℕ} {t : ℝ} (hp : CKPar q t) {μ : Fin q → ℝ}
    (hμ : ∑ a, μ a = 1) : betheE q t μ μ ≤ 1 := by
  have hE : betheE q t μ μ = 1 + t * ((q : ℝ) * ∑ a, μ a ^ 2 - 1) := by
    unfold betheE
    simp_rw [ckMat_betheMvec_eq t hμ]
    have h : ∀ a, μ a * (1 + t * ((q : ℝ) * μ a - 1)) = (1 - t) * μ a + t * q * μ a ^ 2 := by
      intro a
      ring
    simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum, hμ]
    ring
  have hCS : (∑ a, μ a) ^ 2 ≤ (q : ℝ) * ∑ a, μ a ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin q))) (f := μ)
    simpa [Finset.card_univ, Fintype.card_fin] using this
  rw [hμ, one_pow] at hCS
  rw [hE]
  nlinarith [hp.neg]

/-- `S(τ) = tqn²‖λ_τ - u‖²` (Lemma 1.4(c)). -/
theorem ck_S_eq {q n : ℕ} (hq : q ≠ 0) (t : ℝ) (τ : Fin n → Fin q) :
    ckS q t τ = t * q * (n : ℝ) ^ 2 * rsDevSq τ := by
  rw [ckMat_S_eq_rsA, ckMat_sum_rsA hq]
  ring

/-- `-n² ≤ S(τ) ≤ 0` (Lemma 1.4(c)). -/
theorem ck_S_mem {q n : ℕ} {t : ℝ} (hp : CKPar q t) (τ : Fin n → Fin q) :
    -((n : ℝ) ^ 2) ≤ ckS q t τ ∧ ckS q t τ ≤ 0 := by
  have hq2 := hp.two_le
  have hq0 : q ≠ 0 := by omega
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hS := ckMat_S_eq_rsA t τ
  have hlow : 0 ≤ ∑ u, ∑ v, ((rsA q (τ u) (τ v) : ℤ) : ℝ) := by
    rw [ckMat_sum_rsA hq0]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hup : ∑ u, ∑ v, ((rsA q (τ u) (τ v) : ℤ) : ℝ) ≤ ((q : ℝ) - 1) * (n : ℝ) ^ 2 := by
    calc ∑ u, ∑ v, ((rsA q (τ u) (τ v) : ℤ) : ℝ)
        ≤ ∑ _u : Fin n, ∑ _v : Fin n, ((q : ℝ) - 1) :=
          Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => by
            rw [ckMat_rsA_cast]
            split_ifs <;> linarith
      _ = ((q : ℝ) - 1) * (n : ℝ) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  set X := ∑ u, ∑ v, ((rsA q (τ u) (τ v) : ℤ) : ℝ)
  have ht := hp.neg
  have hgt := hp.gt
  rw [hS]
  constructor
  · have h1 : t * ((q : ℝ) - 1) * (n : ℝ) ^ 2 ≤ t * X := by
      nlinarith [mul_nonneg_of_nonpos_of_nonpos ht.le (sub_nonpos.mpr hup)]
    have h2 : -((n : ℝ) ^ 2) ≤ t * ((q : ℝ) - 1) * (n : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ t * ((q : ℝ) - 1) + 1)
        (sq_nonneg (n : ℝ))]
    linarith
  · exact mul_nonpos_of_nonpos_of_nonneg ht.le hlow

/-- `∑_v (M(τ_v, c) - 1) = tqn(λ_τ(c) - 1/q)` (Lemma 1.4(c), second identity). -/
theorem ck_sum_rsM_sub_one {q n : ℕ} (hq : q ≠ 0) (t : ℝ) (τ : Fin n → Fin q) (c : Fin q) :
    ∑ v, (rsM q t (τ v) c - 1) = t * q * n * (colorFrac τ c - (q : ℝ)⁻¹) := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have h0 : ∀ v, rsM q t (τ v) c - 1 = t * q * (if τ v = c then (1 : ℝ) else 0) - t := by
    intro v
    unfold rsM
    rw [ckMat_rsA_cast]
    ring
  have h1 : ∑ v, (rsM q t (τ v) c - 1) = t * ((q : ℝ) * fiberCard τ c - n) := by
    simp_rw [h0]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← ckMat_fiber_eq]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [h1]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [fiberCard]
  · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    unfold colorFrac
    field_simp

/-- For uniform `σ`, `E‖λ_σ - u‖² = (q-1)/(qn)` (Lemma 1.4(d)). -/
theorem ck_avg_devSq {q n : ℕ} (hq : q ≠ 0) (hn : n ≠ 0) :
    ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q, rsDevSq σ = ((q : ℝ) - 1) / (q * n) := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hQ : (q : ℝ) ^ n ≠ 0 := pow_ne_zero _ hq'
  have h := ckMat_sum_sigma_sum_rsA (n := n) (q := q)
  simp_rw [ckMat_sum_rsA hq] at h
  rw [← Finset.mul_sum] at h
  have hden : (q : ℝ) * (n : ℝ) ^ 2 ≠ 0 := mul_ne_zero hq' (pow_ne_zero _ hn')
  have hsum : ∑ σ : Fin n → Fin q, rsDevSq σ =
      (q : ℝ) ^ n * (n * ((q : ℝ) - 1)) / ((q : ℝ) * (n : ℝ) ^ 2) := by
    rw [eq_div_iff hden, ← h]
    ring
  rw [hsum]
  field_simp

end

end ERZeroFreeness
