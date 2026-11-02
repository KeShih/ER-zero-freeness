/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSBetheBasic

/-!
# Appendix C: the Kesten–Stigum bound `d_cond(q,x) ≤ t(x)^{-2}` (Lemma C.3, second assertion)

* `rs_ks_certificate`: for `x ∈ [0,1)` and `s > t(x)^{-2}` there is `ν ∈ 𝒫_u` with
  `Ψ_{s,x}(ν) > 0`.  This is the paper's Kesten–Stigum argument (proof of `lem:rs-ckpz`,
  "Kesten–Stigum bound"), stated as a nonemptiness certificate: it also shows that the set whose
  infimum defines `dCond q x` is nonempty, so `dCond` is a genuine infimum.
* `rs_ks_lower_bound`: an explicit lower bound for `Ψ_{s,x}(ν_ε)`; the certificate follows by
  choosing `ε` small, since `st² > 1`;
* `rs_dCond_le_inv_sq`: `d_cond(q,x) ≤ t(x)^{-2}`, from the certificate.

## Proof

Work with `t = t(x) ∈ [-1/(q-1), 0)`.  The paper's `ε`-expansion with `O(ε³)` terms is replaced by
exact identities and global inequalities for `φ(v) = v log v - v + 1`:

* `ν_ε = q⁻¹ ∑_a δ_{u + ε(e_a - u)}` (`ε ∈ [0,1]`) lies in `𝒫_u` (`integral_smul_measure`,
  `integral_finsetSum_measure`, `integral_dirac`); its products are
  `ν_ε^{⊗k} = q^{-k} ∑_{a : Fin k → Fin q} δ_{(u + ε(e_{a_i} - u))_i}` (`Measure.pi_eq` on boxes),
  so all integrals are finite sums.
* `(M_t μ_i)_b = 1 + εt A_{b a_i}` and `E = 1 + ε²t A_{a_1 a_2}`; with `w = εt`,
  `V_k(a) = q⁻¹ ∑_b ∏_i (1 + w A_{b a_i}) ∈ [0, (1+ε)^k]`, `∑_a V_k(a) = q^k`, and
  `∑_a V_k(a)² = q^k ((1 + (q-1)w²)^k + (q-1)(1 - w²)^k)/q` (expand the square,
  `Fintype.sum_pow`, `∑_c (1 + wA_{bc})(1 + wA_{b'c}) = q(1 + w² A_{bb'})`).
* `(v-1)²/(2B) ≤ φ(v)` for `0 ≤ v ≤ B`, `B ≥ 1`, and `φ(v) ≤ (v-1)²/(2m)` for `0 < m ≤ min(1,v)`
  (from `log w ≤ (w - w⁻¹)/2` for `w ≥ 1` and `-log(1-y) ≥ y + y²/2`), and the binomial bound
  `C(k,2)(q-1)y² ≤ ((1+(q-1)y)^k + (q-1)(1-y)^k)/q - 1` (`add_pow`, coefficientwise).
* Hence `E[V_k log V_k] ≥ C(k,2)(q-1)(εt)⁴ / (2(1+ε)^k)`, `E[E log E] ≤ (q-1)ε⁴t²/(2(1-ε²))`, and
  with `∑_k Pois(s)(k) C(k,2) z^k = (sz)² e^{s(z-1)}/2` (`z = 1/(1+ε)`):
  `Ψ_{s,x}(ν_ε) ≥ (q-1)ε⁴t²/4 · (t²(sz)² e^{s(z-1)} - s/(1-ε²))`; the `V`-series converges by
  the crude bound `E[V_k log V_k] ≤ 4^k`.
* The bracket is continuous in `ε` and equals `s(st² - 1) > 0` at `ε = 0`, so it is positive for
  all small `ε > 0`.
-/

open Polynomial Filter Topology MeasureTheory

namespace ERZeroFreeness

open scoped Classical

noncomputable section

namespace RSBetheKSAux

open scoped ENNReal

/-- The point `u + ε(e_a - u)` of the simplex, as a vector. -/
def ksVecT (q : ℕ) (ε : ℝ) (a : Fin q) : Fin q → ℝ :=
  fun b => (1 - ε) / q + if b = a then ε else 0

/-- `u + ε(e_a - u)` lies in the simplex for `ε ∈ [0,1]`. -/
theorem ksVecT_mem {q : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (a : Fin q) :
    ksVecT q ε a ∈ stdSimplex ℝ (Fin q) := by
  have hq : (q : ℝ) ≠ 0 := by
    have : 0 < q := Fin.pos a
    exact_mod_cast this.ne'
  refine ⟨fun b => ?_, ?_⟩
  · unfold ksVecT
    have : 0 ≤ (1 - ε) / q := div_nonneg (by linarith) (Nat.cast_nonneg _)
    split_ifs <;> linarith
  · unfold ksVecT
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Finset.sum_ite_eq' Finset.univ a (fun _ => ε)]
    simp only [Finset.mem_univ, if_true, nsmul_eq_mul]
    field_simp
    ring

/-- `A_{bc} = q·[b = c] - 1`. -/
theorem ksA_eq (q : ℕ) (b c : Fin q) :
    ((rsA q b c : ℤ) : ℝ) = (q : ℝ) * (if b = c then 1 else 0) - 1 := by
  unfold rsA; split_ifs <;> push_cast <;> ring

/-- `A` is symmetric. -/
theorem ksA_symm (q : ℕ) (b c : Fin q) : rsA q b c = rsA q c b := by
  unfold rsA; simp only [eq_comm]

/-- `∑_c (if b = c then X else Y) = X + (q-1)Y`. -/
theorem ks_sum_ite (q : ℕ) (b : Fin q) (X Y : ℝ) :
    ∑ c : Fin q, (if b = c then X else Y) = X + ((q : ℝ) - 1) * Y := by
  have h : ∀ c : Fin q, (if b = c then X else Y) = Y + (if b = c then X - Y else 0) := by
    intro c; split_ifs <;> ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

/-- The columns of `A` sum to zero. -/
theorem ks_sum_rsA_col (q : ℕ) (c : Fin q) : ∑ b, ((rsA q b c : ℤ) : ℝ) = 0 := by
  simp_rw [ksA_symm q _ c]
  exact rs_sum_rsA q c

/-- `A² = qA`: `∑_c A_{bc} A_{b'c} = q A_{bb'}`. -/
theorem ks_sum_rsA_mul (q : ℕ) (b b' : Fin q) :
    ∑ c, ((rsA q b c : ℤ) : ℝ) * ((rsA q b' c : ℤ) : ℝ) = (q : ℝ) * ((rsA q b b' : ℤ) : ℝ) := by
  have h : ∀ c, ((rsA q b c : ℤ) : ℝ) * ((rsA q b' c : ℤ) : ℝ) =
      (q : ℝ) * (if b = c then ((rsA q b' c : ℤ) : ℝ) else 0) - ((rsA q b' c : ℤ) : ℝ) := by
    intro c; rw [ksA_eq q b c]; split_ifs <;> ring
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, rs_sum_rsA, sub_zero]
  rw [ksA_symm]

/-- `∑_{a,c} A_{ac}² = q²(q-1)`. -/
theorem ks_sum_rsA_sq (q : ℕ) :
    ∑ a : Fin q, ∑ c : Fin q, ((rsA q a c : ℤ) : ℝ) ^ 2 = (q : ℝ) ^ 2 * ((q : ℝ) - 1) := by
  have h : ∀ a, ∑ c : Fin q, ((rsA q a c : ℤ) : ℝ) ^ 2 = (q : ℝ) * ((q : ℝ) - 1) := by
    intro a
    have := ks_sum_rsA_mul q a a
    simp only [← sq] at this
    rw [this]; unfold rsA; simp
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- `(M_t (u + ε(e_a - u)))_b = 1 + εt A_{ba}`. -/
theorem ks_mvec {q : ℕ} (hq : q ≠ 0) (t ε : ℝ) (a b : Fin q) :
    betheMvec q t (ksVecT q ε a) b = 1 + ε * t * ((rsA q b a : ℤ) : ℝ) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  unfold betheMvec
  have h : ∀ c, rsM q t b c * ksVecT q ε a c =
      (1 - ε) / q + t * ((1 - ε) / q) * ((rsA q b c : ℤ) : ℝ) +
        (if c = a then ε * (1 + t * ((rsA q b a : ℤ) : ℝ)) else 0) := by
    intro c; unfold rsM ksVecT; split_ifs with hc
    · subst hc; ring
    · ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, rs_sum_rsA, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  field_simp
  ring

/-- `E(u + ε(e_a - u), u + ε(e_c - u)) = 1 + ε²t A_{ac}`. -/
theorem ks_E {q : ℕ} (hq : q ≠ 0) (t ε : ℝ) (a c : Fin q) :
    betheE q t (ksVecT q ε a) (ksVecT q ε c) = 1 + ε ^ 2 * t * ((rsA q a c : ℤ) : ℝ) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  unfold betheE
  simp only [ks_mvec hq]
  have h : ∀ b, ksVecT q ε a b * (1 + ε * t * ((rsA q b c : ℤ) : ℝ)) =
      (1 - ε) / q + (1 - ε) / q * (ε * t) * ((rsA q b c : ℤ) : ℝ) +
        (if b = a then ε * (1 + ε * t * ((rsA q a c : ℤ) : ℝ)) else 0) := by
    intro b; unfold ksVecT; split_ifs with hb
    · subst hb; ring
    · ring
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, ks_sum_rsA_col, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  field_simp
  ring

/-- `Y(a) = q⁻¹ ∑_b ∏_i (1 + w A_{b a_i})`. -/
def ksY (q : ℕ) (w : ℝ) {k : ℕ} (a : Fin k → Fin q) : ℝ :=
  (q : ℝ)⁻¹ * ∑ b : Fin q, ∏ i, (1 + w * ((rsA q b (a i) : ℤ) : ℝ))

/-- `V_k` at the points `u + ε(e_{a_i} - u)` is `Y(a)` with `w = εt`. -/
theorem ks_V {q : ℕ} (hq : q ≠ 0) (t ε : ℝ) {k : ℕ} (a : Fin k → Fin q) :
    betheV q t (fun i => ksVecT q ε (a i)) = ksY q (ε * t) a := by
  unfold betheV ksY
  simp only [ks_mvec hq]

/-- `∑_a Y(a) = q^k`. -/
theorem ks_sum_Y {q : ℕ} (hq : q ≠ 0) (w : ℝ) (k : ℕ) :
    ∑ a : Fin k → Fin q, ksY q w a = (q : ℝ) ^ k := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have h : ∀ b : Fin q, ∑ c : Fin q, (1 + w * ((rsA q b c : ℤ) : ℝ)) = q := by
    intro b
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, rs_sum_rsA]
    simp
  unfold ksY
  rw [← Finset.mul_sum, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun b _ =>
    (Fintype.sum_pow (fun c => 1 + w * ((rsA q b c : ℤ) : ℝ)) k).symm]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Moving the outer sum of a triple sum inside. -/
theorem ks_swap3 {α β : Type*} [Fintype α] [Fintype β] (F : α → β → β → ℝ) :
    ∑ a, ∑ b, ∑ b', F a b b' = ∑ b, ∑ b', ∑ a, F a b b' := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- `∑_a Y(a)² = q^k ((1 + (q-1)w²)^k + (q-1)(1 - w²)^k)/q`. -/
theorem ks_sum_Y_sq {q : ℕ} (hq : q ≠ 0) (w : ℝ) (k : ℕ) :
    ∑ a : Fin k → Fin q, ksY q w a ^ 2 =
      (q : ℝ) ^ k * (((1 + ((q : ℝ) - 1) * w ^ 2) ^ k + ((q : ℝ) - 1) * (1 - w ^ 2) ^ k) / q) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  set f : Fin q → Fin q → ℝ := fun b c => 1 + w * ((rsA q b c : ℤ) : ℝ) with hf
  have h1 : ∀ a : Fin k → Fin q, ksY q w a ^ 2 =
      ((q : ℝ)⁻¹) ^ 2 * ∑ b : Fin q, ∑ b' : Fin q, ∏ i, (f b (a i) * f b' (a i)) := by
    intro a
    unfold ksY
    rw [mul_pow, sq (∑ b : Fin q, _), Finset.sum_mul_sum]
    simp_rw [← Finset.prod_mul_distrib]
    rfl
  have h2 : ∀ b b' : Fin q, ∑ c : Fin q, f b c * f b' c =
      (q : ℝ) * (1 + w ^ 2 * ((rsA q b b' : ℤ) : ℝ)) := by
    intro b b'
    have e : ∀ c : Fin q, f b c * f b' c =
        1 + w * ((rsA q b c : ℤ) : ℝ) + w * ((rsA q b' c : ℤ) : ℝ) +
          w ^ 2 * (((rsA q b c : ℤ) : ℝ) * ((rsA q b' c : ℤ) : ℝ)) := by intro c; rw [hf]; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, rs_sum_rsA, ks_sum_rsA_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have h3 : ∀ b : Fin q, ∑ b' : Fin q, ((q : ℝ) * (1 + w ^ 2 * ((rsA q b b' : ℤ) : ℝ))) ^ k =
      (q : ℝ) ^ k * ((1 + ((q : ℝ) - 1) * w ^ 2) ^ k + ((q : ℝ) - 1) * (1 - w ^ 2) ^ k) := by
    intro b
    have e : ∀ b' : Fin q, ((q : ℝ) * (1 + w ^ 2 * ((rsA q b b' : ℤ) : ℝ))) ^ k =
        if b = b' then ((q : ℝ) * (1 + ((q : ℝ) - 1) * w ^ 2)) ^ k
        else ((q : ℝ) * (1 - w ^ 2)) ^ k := by
      intro b'; unfold rsA; split_ifs <;> push_cast <;> ring_nf
    simp only [e, ks_sum_ite, mul_pow]
    ring
  calc ∑ a : Fin k → Fin q, ksY q w a ^ 2
      = ((q : ℝ)⁻¹) ^ 2 * ∑ b : Fin q, ∑ b' : Fin q, ∑ a : Fin k → Fin q,
          ∏ i, (f b (a i) * f b' (a i)) := by
        simp only [h1]
        rw [← Finset.mul_sum, ks_swap3]
    _ = ((q : ℝ)⁻¹) ^ 2 * ∑ b : Fin q, ∑ b' : Fin q,
          ((q : ℝ) * (1 + w ^ 2 * ((rsA q b b' : ℤ) : ℝ))) ^ k := by
        congr 1
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
        rw [← h2, Fintype.sum_pow]
    _ = _ := by
        simp only [h3, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- `q⁻¹ ∑_a δ_{P a}` is a probability measure. -/
theorem ks_isProb {X : Type*} [MeasurableSpace X] {q : ℕ} (hq : q ≠ 0) (P : Fin q → X) :
    IsProbabilityMeasure ((q : ℝ≥0∞)⁻¹ • ∑ a : Fin q, Measure.dirac (P a)) := by
  constructor
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, measure_univ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hq) (ENNReal.natCast_ne_top q)

/-- The `k`-fold product of `q⁻¹ ∑_a δ_{P a}` is
`q^{-k} ∑_{a : Fin k → Fin q} δ_{P ∘ a}`. -/
theorem ks_pi_eq {X : Type*} [MeasurableSpace X] {q : ℕ} (hq : q ≠ 0) (P : Fin q → X) (k : ℕ) :
    Measure.pi (fun _ : Fin k => (q : ℝ≥0∞)⁻¹ • ∑ a : Fin q, Measure.dirac (P a)) =
      ((q : ℝ≥0∞) ^ k)⁻¹ • ∑ a : Fin k → Fin q, Measure.dirac (fun i => P (a i)) := by
  have := ks_isProb hq P
  refine Measure.pi_eq fun s hs => ?_
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.inv_pow, Fintype.prod_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
  simp_rw [Measure.dirac_apply' _ (hs _)]
  by_cases h : ∀ i, P (a i) ∈ s i
  · rw [Set.indicator_of_mem (by simpa [Set.mem_univ_pi] using h)]
    rw [Finset.prod_eq_one]
    · simp
    · intro i _
      rw [Set.indicator_of_mem (h i)]
      simp
  · simp only [not_forall] at h
    obtain ⟨i, hi⟩ := h
    rw [Set.indicator_of_notMem (by simp; exact ⟨i, hi⟩)]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]

/-- Integrals against the `k`-fold product of `q⁻¹ ∑_a δ_{P a}` are finite averages. -/
theorem ks_integral {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {q : ℕ}
    (hq : q ≠ 0) (P : Fin q → X) (k : ℕ) (g : (Fin k → X) → ℝ) :
    ∫ μ, g μ ∂(Measure.pi (fun _ : Fin k => (q : ℝ≥0∞)⁻¹ • ∑ a : Fin q, Measure.dirac (P a))) =
      ((q : ℝ) ^ k)⁻¹ * ∑ a : Fin k → Fin q, g (fun i => P (a i)) := by
  rw [ks_pi_eq hq P k, integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac, smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
      ENNReal.toReal_natCast]
  · intro a _
    exact (integrable_const (g (fun i => P (a i)))).congr (ae_eq_dirac g).symm

/-- Integrals against `q⁻¹ ∑_a δ_{P a}` are finite averages. -/
theorem ks_integral_one {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {q : ℕ}
    (P : Fin q → X) (g : X → ℝ) :
    ∫ μ, g μ ∂((q : ℝ≥0∞)⁻¹ • ∑ a : Fin q, Measure.dirac (P a)) =
      (q : ℝ)⁻¹ * ∑ a : Fin q, g (P a) := by
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac, smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · intro a _
    exact (integrable_const (g (P a))).congr (ae_eq_dirac g).symm

/-- `log w ≤ (w - w⁻¹)/2` for `w ≥ 1`. -/
theorem ks_log_le_half_sub_inv {w : ℝ} (hw : 1 ≤ w) : Real.log w ≤ (w - w⁻¹) / 2 := by
  have hw0 : 0 < w := by linarith
  have h := Real.self_le_sinh_iff.mpr (Real.log_nonneg hw)
  rw [Real.sinh_eq, Real.exp_neg, Real.exp_log hw0] at h
  exact h

/-- `y + y²/2 ≤ -log(1-y)` for `0 ≤ y < 1`. -/
theorem ks_add_sq_le_neg_log {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    y + y ^ 2 / 2 ≤ -Real.log (1 - y) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := y) (by rw [abs_of_nonneg hy0]; exact hy1)
  have h2 := sum_le_hasSum (Finset.range 2) (fun i _ => by positivity) h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h2
  norm_num at h2
  linarith

/-- Lower bound: `(v-1) + (v-1)²/(2B) ≤ v log v` for `0 ≤ v ≤ B`, `1 ≤ B`. -/
theorem ks_mulLog_ge {v B : ℝ} (hv0 : 0 ≤ v) (hvB : v ≤ B) (hB : 1 ≤ B) :
    (v - 1) + (v - 1) ^ 2 / (2 * B) ≤ v * Real.log v := by
  have hB0 : 0 < B := by linarith
  rcases hv0.eq_or_lt with hv | hv
  · subst hv
    simp only [Real.log_zero, mul_zero]
    have : (0 - 1 : ℝ) ^ 2 / (2 * B) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  rcases le_or_gt v 1 with hv1 | hv1
  · -- `0 < v ≤ 1`: use the bound at `w = v⁻¹`
    have h := ks_log_le_half_sub_inv (one_le_inv_iff₀.mpr ⟨hv, hv1⟩)
    rw [Real.log_inv, inv_inv] at h
    have h1 : (v ^ 2 - 1) / 2 ≤ v * Real.log v := by
      have : v * (-Real.log v) ≤ v * ((v⁻¹ - v) / 2) := mul_le_mul_of_nonneg_left h hv.le
      have e : v * ((v⁻¹ - v) / 2) = (1 - v ^ 2) / 2 := by field_simp
      linarith
    have h2 : (v - 1) ^ 2 / (2 * B) ≤ (v - 1) ^ 2 / 2 := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by linarith)
    nlinarith
  · -- `v > 1`: use the bound at `y = 1 - v⁻¹`
    have hy0 : 0 ≤ 1 - v⁻¹ := by
      have : v⁻¹ < 1 := inv_lt_one_of_one_lt₀ hv1
      linarith
    have hy1 : 1 - v⁻¹ < 1 := by
      have : 0 < v⁻¹ := inv_pos.mpr hv
      linarith
    have h := ks_add_sq_le_neg_log hy0 hy1
    rw [sub_sub_cancel, Real.log_inv, neg_neg] at h
    have h1 : (v - 1) + (v - 1) ^ 2 / (2 * v) ≤ v * Real.log v := by
      have : v * ((1 - v⁻¹) + (1 - v⁻¹) ^ 2 / 2) ≤ v * Real.log v :=
        mul_le_mul_of_nonneg_left h hv.le
      have e : v * ((1 - v⁻¹) + (1 - v⁻¹) ^ 2 / 2) = (v - 1) + (v - 1) ^ 2 / (2 * v) := by
        field_simp
      linarith
    have h2 : (v - 1) ^ 2 / (2 * B) ≤ (v - 1) ^ 2 / (2 * v) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
    linarith

/-- Upper bound: `v log v ≤ (v-1) + (v-1)²/(2m)` for `0 < m ≤ 1`, `m ≤ v`. -/
theorem ks_mulLog_le {v m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) (hmv : m ≤ v) :
    v * Real.log v ≤ (v - 1) + (v - 1) ^ 2 / (2 * m) := by
  have hv : 0 < v := lt_of_lt_of_le hm0 hmv
  rcases le_or_gt 1 v with hv1 | hv1
  · have h := ks_log_le_half_sub_inv hv1
    have h1 : v * Real.log v ≤ (v ^ 2 - 1) / 2 := by
      have : v * Real.log v ≤ v * ((v - v⁻¹) / 2) := mul_le_mul_of_nonneg_left h hv.le
      have e : v * ((v - v⁻¹) / 2) = (v ^ 2 - 1) / 2 := by field_simp
      linarith
    have h2 : (v - 1) ^ 2 / 2 ≤ (v - 1) ^ 2 / (2 * m) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
    nlinarith
  · set y := 1 - v with hy
    have hy0 : 0 ≤ y := by linarith
    have hy1 : y < 1 := by linarith
    have h := ks_add_sq_le_neg_log hy0 hy1
    have hv' : v = 1 - y := by linarith
    rw [show 1 - y = v by linarith] at h
    have h1 : v * Real.log v ≤ -v * (y + y ^ 2 / 2) := by
      have : v * Real.log v ≤ v * (-(y + y ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) hv.le
      linarith
    -- `-v(y + y²/2) = -y + y²(1+y)/2` and `m(1+y) ≤ (1-y)(1+y) ≤ 1`
    have h2 : y ^ 2 * (1 + y) / 2 ≤ y ^ 2 / (2 * m) := by
      have hmy : m * (1 + y) ≤ 1 := by nlinarith
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      have : y ^ 2 * (1 + y) * (2 * m) = 2 * y ^ 2 * (m * (1 + y)) := by ring
      rw [this]
      nlinarith [sq_nonneg y]
    have e : -v * (y + y ^ 2 / 2) = -y + y ^ 2 * (1 + y) / 2 := by rw [hv']; ring
    have e2 : (v - 1) + (v - 1) ^ 2 / (2 * m) = -y + y ^ 2 / (2 * m) := by
      rw [hv']; ring
    linarith

/-- Binomial bound: `C(k,2)(q-1)y² ≤ ((1+(q-1)y)^k + (q-1)(1-y)^k)/q - 1`. -/
theorem ks_binom {Q y : ℝ} (hQ : 2 ≤ Q) (hy : 0 ≤ y) (k : ℕ) :
    (k.choose 2 : ℝ) * (Q - 1) * y ^ 2 ≤
      ((1 + (Q - 1) * y) ^ k + (Q - 1) * (1 - y) ^ k) / Q - 1 := by
  have hQ0 : 0 < Q := by linarith
  set g : ℕ → ℝ := fun m => y ^ m * (k.choose m : ℝ) * ((Q - 1) ^ m + (Q - 1) * (-1) ^ m) with hg
  have hsum : (1 + (Q - 1) * y) ^ k + (Q - 1) * (1 - y) ^ k = ∑ m ∈ Finset.range (k + 1), g m := by
    rw [show 1 + (Q - 1) * y = (Q - 1) * y + 1 by ring, show 1 - y = -y + 1 by ring, add_pow,
      add_pow, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hg]
    simp only [one_pow, mul_one]
    rw [mul_pow, neg_pow]
    ring
  have hg0 : g 0 = Q := by rw [hg]; simp
  have hg1 : g 1 = 0 := by rw [hg]; simp
  have hg2 : g 2 = (k.choose 2 : ℝ) * (Q - 1) * Q * y ^ 2 := by rw [hg]; simp; ring
  have hgpos : ∀ m, 1 ≤ m → 0 ≤ g m := by
    intro m hm
    rw [hg]
    have h1 : Q - 1 ≤ (Q - 1) ^ m := le_self_pow₀ (by linarith) (by omega)
    have h2 : -1 ≤ ((-1 : ℝ)) ^ m := by
      rcases neg_one_pow_eq_or ℝ m with h | h <;> simp [h]
    have h3 : 0 ≤ (Q - 1) ^ m + (Q - 1) * (-1) ^ m := by nlinarith
    exact mul_nonneg (mul_nonneg (pow_nonneg hy _) (Nat.cast_nonneg _)) h3
  have hmain : Q + (k.choose 2 : ℝ) * (Q - 1) * Q * y ^ 2 ≤ ∑ m ∈ Finset.range (k + 1), g m := by
    rcases lt_or_ge k 2 with hk | hk
    · have hc : k.choose 2 = 0 := Nat.choose_eq_zero_of_lt hk
      rw [hc, Nat.cast_zero, zero_mul, zero_mul, zero_mul, add_zero, ← hg0]
      exact Finset.single_le_sum (fun m _ => (show 0 ≤ g m from by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h, hg0]; exact hQ0.le
        · exact hgpos m h)) (Finset.mem_range.mpr (by omega))
    · have hsub : ({0, 2} : Finset ℕ) ⊆ Finset.range (k + 1) := by
        intro m hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl
        · simp
        · simp only [Finset.mem_range]; omega
      have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ hm => by
        have : m ≠ 0 := by intro h; apply hm; simp [h]
        exact hgpos m (by omega))
      rw [Finset.sum_pair (by norm_num), hg0, hg2] at this
      exact this
  rw [hsum]
  rw [le_sub_iff_add_le, le_div_iff₀ hQ0]
  nlinarith

/-- The Poisson generating function `∑_k Pois(λ)(k) y^k = e^{λ(y-1)}`. -/
theorem ks_hasSum_poisPMF_mul_pow (lam y : ℝ) :
    HasSum (fun k => poisPMF lam k * y ^ k) (Real.exp (lam * (y - 1))) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (lam * y)
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (Real.exp (-lam))
  have e1 : (fun k : ℕ => poisPMF lam k * y ^ k) =
      fun k : ℕ => Real.exp (-lam) * ((lam * y) ^ k / (k.factorial : ℝ)) := by
    funext k
    unfold poisPMF
    rw [mul_pow]
    ring
  have e2 : Real.exp (lam * (y - 1)) = Real.exp (-lam) * Real.exp (lam * y) := by
    rw [← Real.exp_add]
    ring_nf
  rw [e1, e2]
  exact h2

/-- `∑_k Pois(s)(k) C(k,2) z^k = (sz)² e^{s(z-1)}/2`. -/
theorem ks_hasSum_pois_choose (s z : ℝ) :
    HasSum (fun k : ℕ => poisPMF s k * ((k.choose 2 : ℝ) * z ^ k))
      ((s * z) ^ 2 * Real.exp (s * (z - 1)) / 2) := by
  have h := (ks_hasSum_poisPMF_mul_pow s z).mul_left ((s * z) ^ 2 / 2)
  have e : ∀ n : ℕ, poisPMF s (n + 2) * ((((n + 2).choose 2 : ℕ) : ℝ) * z ^ (n + 2)) =
      (s * z) ^ 2 / 2 * (poisPMF s n * z ^ n) := by
    intro n
    unfold poisPMF
    rw [Nat.cast_choose_two, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have h' : HasSum (fun n : ℕ => poisPMF s (n + 2) * ((((n + 2).choose 2 : ℕ) : ℝ) * z ^ (n + 2)))
      ((s * z) ^ 2 * Real.exp (s * (z - 1)) / 2) := by
    rw [funext e, show (s * z) ^ 2 * Real.exp (s * (z - 1)) / 2 =
      (s * z) ^ 2 / 2 * Real.exp (s * (z - 1)) by ring]
    exact h
  have h0 : ∑ i ∈ Finset.range 2, poisPMF s i * ((i.choose 2 : ℝ) * z ^ i) = 0 := by
    simp [Finset.sum_range_succ]
  refine (hasSum_nat_add_iff' 2).mp ?_
  rw [h0, sub_zero]
  exact h'

/-- A sum over `Fin 2 → Fin q` is a double sum. -/
theorem ks_sum_fin_two {q : ℕ} (h : Fin q → Fin q → ℝ) :
    ∑ a : Fin 2 → Fin q, h (a 0) (a 1) = ∑ c, ∑ d, h c d := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (finTwoArrowEquiv (Fin q)) _ _ (fun a => rfl)

/-- For `t ∈ [-1/(q-1), 0]` and `ε ≥ 0`: `1 - ε ≤ 1 + εt A_{bc} ≤ 1 + ε`. -/
theorem ks_factor_bounds {q : ℕ} (hq : 2 ≤ q) {ε t : ℝ} (hε0 : 0 ≤ ε)
    (ht0 : -1 ≤ t * ((q : ℝ) - 1)) (ht1 : t ≤ 0) (b c : Fin q) :
    1 - ε ≤ 1 + ε * t * ((rsA q b c : ℤ) : ℝ) ∧ 1 + ε * t * ((rsA q b c : ℤ) : ℝ) ≤ 1 + ε := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  unfold rsA
  split_ifs
  · push_cast
    have h1 : -ε ≤ ε * (t * ((q : ℝ) - 1)) := by nlinarith
    have h2 : ε * (t * ((q : ℝ) - 1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hε0 (mul_nonpos_of_nonpos_of_nonneg ht1 (by linarith))
    constructor <;> nlinarith
  · push_cast
    have h1 : -t ≤ 1 := by nlinarith
    constructor <;> nlinarith

/-- `0 ≤ Y(a) ≤ (1+ε)^k` for `w = εt`. -/
theorem ks_Y_bounds {q : ℕ} (hq : 2 ≤ q) {ε t : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ht0 : -1 ≤ t * ((q : ℝ) - 1)) (ht1 : t ≤ 0) {k : ℕ} (a : Fin k → Fin q) :
    0 ≤ ksY q (ε * t) a ∧ ksY q (ε * t) a ≤ (1 + ε) ^ k := by
  have hq0 : (0 : ℝ) < q := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hf := fun b c => ks_factor_bounds hq hε0 ht0 ht1 b c
  have hp0 : ∀ b : Fin q, 0 ≤ ∏ i, (1 + ε * t * ((rsA q b (a i) : ℤ) : ℝ)) :=
    fun b => Finset.prod_nonneg fun i _ => by linarith [(hf b (a i)).1]
  have hp1 : ∀ b : Fin q, ∏ i, (1 + ε * t * ((rsA q b (a i) : ℤ) : ℝ)) ≤ (1 + ε) ^ k := by
    intro b
    calc ∏ i, (1 + ε * t * ((rsA q b (a i) : ℤ) : ℝ)) ≤ ∏ _i : Fin k, (1 + ε) :=
          Finset.prod_le_prod (fun i _ => by linarith [(hf b (a i)).1]) (fun i _ => (hf b (a i)).2)
      _ = (1 + ε) ^ k := by simp
  unfold ksY
  simp only [mul_assoc] at hp0 hp1 ⊢
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hq0.le) (Finset.sum_nonneg fun b _ => hp0 b)
  · rw [inv_mul_le_iff₀ hq0]
    calc ∑ b : Fin q, ∏ i, (1 + ε * (t * ((rsA q b (a i) : ℤ) : ℝ)))
        ≤ ∑ _b : Fin q, (1 + ε) ^ k := Finset.sum_le_sum fun b _ => hp1 b
      _ = (q : ℝ) * (1 + ε) ^ k := by simp

/-- `∑_a (Y(a) - 1)² = q^k (((1 + (q-1)w²)^k + (q-1)(1 - w²)^k)/q - 1)`. -/
theorem ks_sum_Y_sub_sq {q : ℕ} (hq : q ≠ 0) (w : ℝ) (k : ℕ) :
    ∑ a : Fin k → Fin q, (ksY q w a - 1) ^ 2 =
      (q : ℝ) ^ k *
        (((1 + ((q : ℝ) - 1) * w ^ 2) ^ k + ((q : ℝ) - 1) * (1 - w ^ 2) ^ k) / q - 1) := by
  have e : ∀ a : Fin k → Fin q, (ksY q w a - 1) ^ 2 = ksY q w a ^ 2 - 2 * ksY q w a + 1 :=
    fun a => by ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ks_sum_Y_sq hq, ks_sum_Y hq, Finset.sum_const, Finset.card_univ, Fintype.card_pi,
    Fintype.card_fin, Finset.prod_const, nsmul_eq_mul]
  push_cast
  ring

/-- Lower bound for `E[V_k log V_k]` under `ν_ε`, written as the finite average
`q^{-k} ∑_a Y(a) log Y(a)` (`ks_integral_V`): it is at least `(q-1)(εt)⁴ C(k,2) (1+ε)^{-k}/2`. -/
theorem ks_V_ge {q : ℕ} (hq : 2 ≤ q) {ε t : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ht0 : -1 ≤ t * ((q : ℝ) - 1)) (ht1 : t ≤ 0) (k : ℕ) :
    ((q : ℝ) - 1) * (ε * t) ^ 4 / 2 * ((k.choose 2 : ℝ) * (1 / (1 + ε)) ^ k) ≤
      ((q : ℝ) ^ k)⁻¹ * ∑ a : Fin k → Fin q, ksY q (ε * t) a * Real.log (ksY q (ε * t) a) := by
  have hq0 : q ≠ 0 := by omega
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqk : (0 : ℝ) < (q : ℝ) ^ k := by positivity
  have hB1 : 1 ≤ (1 + ε) ^ k := one_le_pow₀ (by linarith)
  have hB0 : 0 < (1 + ε) ^ k := by linarith
  set F := ((1 + ((q : ℝ) - 1) * (ε * t) ^ 2) ^ k + ((q : ℝ) - 1) * (1 - (ε * t) ^ 2) ^ k) / q
    with hF
  have hYb := fun a : Fin k → Fin q => ks_Y_bounds hq hε0 hε1 ht0 ht1 a
  have h1 : ∑ a : Fin k → Fin q,
      ((ksY q (ε * t) a - 1) + (ksY q (ε * t) a - 1) ^ 2 / (2 * (1 + ε) ^ k)) ≤
        ∑ a : Fin k → Fin q, ksY q (ε * t) a * Real.log (ksY q (ε * t) a) :=
    Finset.sum_le_sum fun a _ => ks_mulLog_ge (hYb a).1 (hYb a).2 hB1
  have h2 : ∑ a : Fin k → Fin q,
      ((ksY q (ε * t) a - 1) + (ksY q (ε * t) a - 1) ^ 2 / (2 * (1 + ε) ^ k)) =
        (q : ℝ) ^ k * ((F - 1) / (2 * (1 + ε) ^ k)) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ks_sum_Y_sub_sq hq0, Finset.sum_sub_distrib,
      ks_sum_Y hq0]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_fin,
      Finset.prod_const, nsmul_eq_mul, mul_one]
    push_cast
    ring
  have h3 : (k.choose 2 : ℝ) * ((q : ℝ) - 1) * ((ε * t) ^ 2) ^ 2 ≤ F - 1 :=
    ks_binom hqR (sq_nonneg _) k
  have h4 : (F - 1) / (2 * (1 + ε) ^ k) ≤
      ((q : ℝ) ^ k)⁻¹ * ∑ a : Fin k → Fin q, ksY q (ε * t) a * Real.log (ksY q (ε * t) a) := by
    rw [le_inv_mul_iff₀ hqk]
    linarith
  have h5 : ((q : ℝ) - 1) * (ε * t) ^ 4 / 2 * ((k.choose 2 : ℝ) * (1 / (1 + ε)) ^ k) =
      (k.choose 2 : ℝ) * ((q : ℝ) - 1) * ((ε * t) ^ 2) ^ 2 / (2 * (1 + ε) ^ k) := by
    rw [one_div_pow]
    field_simp
  rw [h5]
  exact le_trans (div_le_div_of_nonneg_right h3 (by positivity)) h4

/-- Crude upper bound `E[V_k log V_k] ≤ 4^k` under `ν_ε` (summability of the `k`-series). -/
theorem ks_V_le {q : ℕ} (hq : 2 ≤ q) {ε t : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ht0 : -1 ≤ t * ((q : ℝ) - 1)) (ht1 : t ≤ 0) (k : ℕ) :
    ((q : ℝ) ^ k)⁻¹ * ∑ a : Fin k → Fin q, ksY q (ε * t) a * Real.log (ksY q (ε * t) a) ≤
      4 ^ k := by
  have hq0 : q ≠ 0 := by omega
  have hqk : (0 : ℝ) < (q : ℝ) ^ k := by positivity
  have h1 : ∀ a : Fin k → Fin q, ksY q (ε * t) a * Real.log (ksY q (ε * t) a) ≤ 4 ^ k := by
    intro a
    obtain ⟨h0, hB⟩ := ks_Y_bounds hq hε0 hε1 ht0 ht1 a
    have hlog : ksY q (ε * t) a * Real.log (ksY q (ε * t) a) ≤
        ksY q (ε * t) a * (ksY q (ε * t) a - 1) := by
      rcases h0.eq_or_lt with h | h
      · rw [← h]; simp
      · exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos h) h0
    have hB2 : ksY q (ε * t) a ^ 2 ≤ 4 ^ k := by
      calc ksY q (ε * t) a ^ 2 ≤ ((1 + ε) ^ k) ^ 2 := pow_le_pow_left₀ h0 hB 2
        _ = ((1 + ε) ^ 2) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ 4 ^ k := pow_le_pow_left₀ (by positivity) (by nlinarith) k
    nlinarith
  rw [inv_mul_le_iff₀ hqk]
  calc ∑ a : Fin k → Fin q, ksY q (ε * t) a * Real.log (ksY q (ε * t) a)
      ≤ ∑ _a : Fin k → Fin q, (4 : ℝ) ^ k := Finset.sum_le_sum fun a _ => h1 a
    _ = (q : ℝ) ^ k * 4 ^ k := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_fin,
        Finset.prod_const, nsmul_eq_mul]
      push_cast
      ring

/-- Upper bound for `E[E log E]` under `ν_ε`, written as the finite average over `a, c`
(`ks_integral_E`): it is at most `(q-1)ε⁴t²/(2(1-ε²))`. -/
theorem ks_E_le {q : ℕ} (hq : 2 ≤ q) {ε t : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (ht0 : -1 ≤ t * ((q : ℝ) - 1)) (ht1 : t ≤ 0) :
    ((q : ℝ) ^ 2)⁻¹ * ∑ a : Fin q, ∑ c : Fin q, (1 + ε ^ 2 * t * ((rsA q a c : ℤ) : ℝ)) *
        Real.log (1 + ε ^ 2 * t * ((rsA q a c : ℤ) : ℝ)) ≤
      ((q : ℝ) - 1) * ε ^ 4 * t ^ 2 / (2 * (1 - ε ^ 2)) := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  have hε2 : ε ^ 2 < 1 := by nlinarith
  have hm0 : 0 < 1 - ε ^ 2 := by linarith
  have hm1 : 1 - ε ^ 2 ≤ 1 := by nlinarith
  have hEm : ∀ a c : Fin q, 1 - ε ^ 2 ≤ 1 + ε ^ 2 * t * ((rsA q a c : ℤ) : ℝ) :=
    fun a c => (ks_factor_bounds hq (sq_nonneg ε) ht0 ht1 a c).1
  have h1 : ∑ a : Fin q, ∑ c : Fin q, (1 + ε ^ 2 * t * ((rsA q a c : ℤ) : ℝ)) *
        Real.log (1 + ε ^ 2 * t * ((rsA q a c : ℤ) : ℝ)) ≤
      ∑ a : Fin q, ∑ c : Fin q, (((1 + ε ^ 2 * t * ((rsA q a c : ℤ) : ℝ)) - 1) +
        ((1 + ε ^ 2 * t * ((rsA q a c : ℤ) : ℝ)) - 1) ^ 2 / (2 * (1 - ε ^ 2))) :=
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ => ks_mulLog_le hm0 hm1 (hEm a c)
  have h2 : ∑ a : Fin q, ∑ c : Fin q, (((1 + ε ^ 2 * t * ((rsA q a c : ℤ) : ℝ)) - 1) +
        ((1 + ε ^ 2 * t * ((rsA q a c : ℤ) : ℝ)) - 1) ^ 2 / (2 * (1 - ε ^ 2))) =
      (q : ℝ) ^ 2 * (((q : ℝ) - 1) * ε ^ 4 * t ^ 2 / (2 * (1 - ε ^ 2))) := by
    have e : ∀ a c : Fin q, (((1 + ε ^ 2 * t * ((rsA q a c : ℤ) : ℝ)) - 1) +
        ((1 + ε ^ 2 * t * ((rsA q a c : ℤ) : ℝ)) - 1) ^ 2 / (2 * (1 - ε ^ 2))) =
        ε ^ 2 * t * ((rsA q a c : ℤ) : ℝ) +
          ε ^ 4 * t ^ 2 / (2 * (1 - ε ^ 2)) * ((rsA q a c : ℤ) : ℝ) ^ 2 := by
      intro a c; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, rs_sum_rsA, mul_zero, zero_add]
    rw [ks_sum_rsA_sq]
    ring
  rw [inv_mul_le_iff₀ hq2]
  linarith

/-- `u + ε(e_a - u)` as a point of the simplex. -/
def ksPt (q : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (a : Fin q) : rsSimplex q :=
  ⟨ksVecT q ε a, ksVecT_mem hε0 hε1 a⟩

theorem ksPt_coe (q : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (a : Fin q) :
    ((ksPt q hε0 hε1 a : rsSimplex q) : Fin q → ℝ) = ksVecT q ε a := rfl

/-- `ν_ε = q⁻¹ ∑_a δ_{u + ε(e_a - u)}`. -/
def ksProb (q : ℕ) (hq : q ≠ 0) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ProbabilityMeasure (rsSimplex q) :=
  ⟨(q : ℝ≥0∞)⁻¹ • ∑ a : Fin q, Measure.dirac (ksPt q hε0 hε1 a), ks_isProb hq _⟩

/-- `∑_a (u + ε(e_a - u))_b = 1`. -/
theorem ks_sum_ksVecT {q : ℕ} (hq : q ≠ 0) (ε : ℝ) (b : Fin q) :
    ∑ a : Fin q, ksVecT q ε a b = 1 := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  unfold ksVecT
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_ite_eq Finset.univ b (fun _ => ε)]
  simp only [Finset.mem_univ, if_true, nsmul_eq_mul]
  field_simp
  ring

/-- `ν_ε ∈ 𝒫_u`. -/
theorem ksProb_mem {q : ℕ} (hq : q ≠ 0) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ksProb q hq hε0 hε1 ∈ rsPu q := by
  intro b
  have e := ks_integral_one (ksPt q hε0 hε1) (fun μ : rsSimplex q => (μ : Fin q → ℝ) b)
  refine e.trans ?_
  simp only [ksPt_coe, ks_sum_ksVecT hq, mul_one]

/-- `E_{ν_ε}[V_k log V_k]` as a finite average. -/
theorem ks_integral_V {q : ℕ} (hq : q ≠ 0) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t : ℝ)
    (k : ℕ) :
    ∫ μ : Fin k → rsSimplex q, betheV q t (fun i => (μ i : Fin q → ℝ)) *
        Real.log (betheV q t (fun i => (μ i : Fin q → ℝ)))
      ∂(Measure.pi fun _ => (ksProb q hq hε0 hε1 : Measure (rsSimplex q))) =
      ((q : ℝ) ^ k)⁻¹ * ∑ a : Fin k → Fin q, ksY q (ε * t) a * Real.log (ksY q (ε * t) a) := by
  have e := ks_integral (X := rsSimplex q) hq (ksPt q hε0 hε1) k
    (fun μ => betheV q t (fun i => (μ i : Fin q → ℝ)) *
      Real.log (betheV q t (fun i => (μ i : Fin q → ℝ))))
  refine e.trans ?_
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [ksPt_coe, ks_V hq]

/-- `E_{ν_ε}[E log E]` as a finite average. -/
theorem ks_integral_E {q : ℕ} (hq : q ≠ 0) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t : ℝ) :
    ∫ μ : Fin 2 → rsSimplex q, betheE q t (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ) *
        Real.log (betheE q t (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ))
      ∂(Measure.pi fun _ => (ksProb q hq hε0 hε1 : Measure (rsSimplex q))) =
      ((q : ℝ) ^ 2)⁻¹ * ∑ a : Fin q, ∑ c : Fin q, (1 + ε ^ 2 * t * ((rsA q a c : ℤ) : ℝ)) *
        Real.log (1 + ε ^ 2 * t * ((rsA q a c : ℤ) : ℝ)) := by
  have e := ks_integral (X := rsSimplex q) hq (ksPt q hε0 hε1) 2
    (fun μ => betheE q t (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ) *
      Real.log (betheE q t (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ)))
  refine e.trans ?_
  congr 1
  simp only [ksPt_coe, ks_E hq]
  exact ks_sum_fin_two (fun a c => (1 + ε ^ 2 * t * ((rsA q a c : ℤ) : ℝ)) *
    Real.log (1 + ε ^ 2 * t * ((rsA q a c : ℤ) : ℝ)))

end RSBetheKSAux

open RSBetheKSAux

/-- **Explicit lower bound.** For `x ∈ [0,1]`, `s ≥ 0` and `ε ∈ (0,1)`, the measure
`ν_ε = q⁻¹ ∑_a δ_{u + ε(e_a - u)} ∈ 𝒫_u` satisfies, with `t = t(x)` and `z = 1/(1+ε)`,
`Ψ_{s,x}(ν_ε) ≥ (q-1) ε⁴ t²/4 · (t² (sz)² e^{s(z-1)} - s/(1-ε²))` (stated as the existence of
such a `ν ∈ 𝒫_u`). -/
theorem rs_ks_lower_bound {q : ℕ} (hq : 3 ≤ q) {x s ε : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hs : 0 ≤ s) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ ν ∈ rsPu q,
      ((q : ℝ) - 1) * ε ^ 4 * tRe q x ^ 2 / 4 *
          (tRe q x ^ 2 * (s / (1 + ε)) ^ 2 * Real.exp (s * (1 / (1 + ε) - 1)) -
            s / (1 - ε ^ 2)) ≤
        bethePsi q s x ν := by
  have hq0 : q ≠ 0 := by omega
  have hq2 : 2 ≤ q := by omega
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  set ν := ksProb q hq0 hε0.le hε1.le with hν
  refine ⟨ν, ksProb_mem hq0 hε0.le hε1.le, ?_⟩
  have ht0 : -1 ≤ tRe q x * ((q : ℝ) - 1) := by
    have := rs_tRe_ge hq2 hx0
    rwa [div_le_iff₀ (by linarith)] at this
  have ht1 : tRe q x ≤ 0 := rs_tRe_nonpos hq2 hx0 hx1
  -- the `V`-series
  have hI : ∀ k : ℕ,
      ((q : ℝ) - 1) * (ε * tRe q x) ^ 4 / 2 * ((k.choose 2 : ℝ) * (1 / (1 + ε)) ^ k) ≤
        ∫ μ : Fin k → rsSimplex q, betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)) *
            Real.log (betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)))
          ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q))) := by
    intro k
    rw [hν, ks_integral_V]
    exact ks_V_ge hq2 hε0.le hε1.le ht0 ht1 k
  have hL : HasSum (fun k : ℕ => poisPMF s k *
      (((q : ℝ) - 1) * (ε * tRe q x) ^ 4 / 2 * ((k.choose 2 : ℝ) * (1 / (1 + ε)) ^ k)))
      (((q : ℝ) - 1) * (ε * tRe q x) ^ 4 / 2 *
        ((s * (1 / (1 + ε))) ^ 2 * Real.exp (s * (1 / (1 + ε) - 1)) / 2)) := by
    have h := (ks_hasSum_pois_choose s (1 / (1 + ε))).mul_left
      (((q : ℝ) - 1) * (ε * tRe q x) ^ 4 / 2)
    have e : (fun k : ℕ => poisPMF s k *
        (((q : ℝ) - 1) * (ε * tRe q x) ^ 4 / 2 * ((k.choose 2 : ℝ) * (1 / (1 + ε)) ^ k))) =
        fun k : ℕ => ((q : ℝ) - 1) * (ε * tRe q x) ^ 4 / 2 *
          (poisPMF s k * ((k.choose 2 : ℝ) * (1 / (1 + ε)) ^ k)) :=
      funext fun k => by ring
    rw [e]
    exact h
  have hL0 : ∀ k : ℕ,
      0 ≤ ((q : ℝ) - 1) * (ε * tRe q x) ^ 4 / 2 * ((k.choose 2 : ℝ) * (1 / (1 + ε)) ^ k) := by
    intro k
    have : (0 : ℝ) ≤ (q : ℝ) - 1 := by linarith
    positivity
  have hsumm : Summable fun k : ℕ => poisPMF s k *
      ∫ μ : Fin k → rsSimplex q, betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)) *
          Real.log (betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)))
        ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q))) := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (poisPMF_nonneg hs k)
      ((hL0 k).trans (hI k))) (fun k => mul_le_mul_of_nonneg_left ?_ (poisPMF_nonneg hs k))
      (ks_hasSum_poisPMF_mul_pow s 4).summable
    rw [hν, ks_integral_V]
    exact ks_V_le hq2 hε0.le hε1.le ht0 ht1 k
  have hsum := hsumm.hasSum
  have h1 := hasSum_le (fun k => mul_le_mul_of_nonneg_left (hI k) (poisPMF_nonneg hs k)) hL hsum
  -- the `E`-term
  have hJ : ∫ μ : Fin 2 → rsSimplex q,
        betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ) *
          Real.log (betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ))
        ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q))) ≤
      ((q : ℝ) - 1) * ε ^ 4 * tRe q x ^ 2 / (2 * (1 - ε ^ 2)) := by
    rw [hν, ks_integral_E]
    exact ks_E_le hq2 hε0.le hε1 ht0 ht1
  have hJ' := mul_le_mul_of_nonneg_left hJ (by positivity : (0 : ℝ) ≤ s / 2)
  have hε2 : (1 : ℝ) - ε ^ 2 ≠ 0 := by nlinarith
  have hε3 : (1 : ℝ) + ε ≠ 0 := by linarith
  have e : ((q : ℝ) - 1) * ε ^ 4 * tRe q x ^ 2 / 4 *
          (tRe q x ^ 2 * (s / (1 + ε)) ^ 2 * Real.exp (s * (1 / (1 + ε) - 1)) -
            s / (1 - ε ^ 2)) =
      ((q : ℝ) - 1) * (ε * tRe q x) ^ 4 / 2 *
          ((s * (1 / (1 + ε))) ^ 2 * Real.exp (s * (1 / (1 + ε) - 1)) / 2) -
        s / 2 * (((q : ℝ) - 1) * ε ^ 4 * tRe q x ^ 2 / (2 * (1 - ε ^ 2))) := by
    field_simp
    ring
  unfold bethePsi
  rw [e]
  linarith

/-- **Kesten–Stigum certificate** (Lemma C.3): for `x ∈ [0,1)` and `s > t(x)^{-2}`, some
`ν ∈ 𝒫_u` has `Ψ_{s,x}(ν) > 0`. -/
theorem rs_ks_certificate {q : ℕ} (hq : 3 ≤ q) {x s : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hs : (tRe q x ^ 2)⁻¹ < s) : ∃ ν ∈ rsPu q, 0 < bethePsi q s x ν := by
  have hq2 : 2 ≤ q := by omega
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have ht : tRe q x < 0 := rs_tRe_neg hq2 hx0 hx1
  have ht2 : 0 < tRe q x ^ 2 := by nlinarith
  have hs0 : 0 < s := lt_trans (inv_pos.mpr ht2) hs
  have hst : 1 < s * tRe q x ^ 2 := by
    have := mul_lt_mul_of_pos_right hs ht2
    rwa [inv_mul_cancel₀ ht2.ne'] at this
  -- The bracket `g` of `rs_ks_lower_bound` is continuous at `ε = 0`, where it equals
  -- `s (s t² - 1) > 0`; hence `g(ε) > 0` for all small `ε > 0`.
  set g : ℝ → ℝ := fun ε => tRe q x ^ 2 * (s / (1 + ε)) ^ 2 * Real.exp (s * (1 / (1 + ε) - 1)) -
    s / (1 - ε ^ 2) with hg
  have hg0 : g 0 = s * (s * tRe q x ^ 2 - 1) := by
    simp only [hg]
    norm_num
    ring
  have hg0pos : 0 < g 0 := by
    rw [hg0]
    exact mul_pos hs0 (by linarith)
  have hcont : ContinuousAt g 0 := by
    simp only [hg]
    fun_prop (disch := norm_num)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < g ε ∧ ε ∈ Set.Ioo (0 : ℝ) 1 :=
    ((hcont.eventually (lt_mem_nhds hg0pos)).filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsGT one_pos)
  obtain ⟨ε, hgε, hε0, hε1⟩ := hev.exists
  obtain ⟨ν, hν, hle⟩ := rs_ks_lower_bound hq hx0 hx1.le hs0.le hε0 hε1
  refine ⟨ν, hν, lt_of_lt_of_le ?_ hle⟩
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  exact mul_pos (div_pos (mul_pos (mul_pos hq1 (pow_pos hε0 4)) ht2) (by norm_num)) hgε

/-- **Lemma C.3, Kesten–Stigum bound.** `d_cond(q,x) ≤ t(x)^{-2}` for `x ∈ [0,1)`. -/
theorem rs_dCond_le_inv_sq {q : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    dCond q x ≤ (tRe q x ^ 2)⁻¹ := by
  refine le_of_forall_gt_imp_ge_of_dense fun s hs => ?_
  obtain ⟨ν, hν, hpos⟩ := rs_ks_certificate hq hx0 hx1 hs
  have hs0 : 0 < s := lt_of_le_of_lt (inv_nonneg.2 (sq_nonneg _)) hs
  exact rs_dCond_le_of_pos hs0 hν hpos

end

end ERZeroFreeness
