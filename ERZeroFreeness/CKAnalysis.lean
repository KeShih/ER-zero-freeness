/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.CKDefs
import ERZeroFreeness.CKMatrix
import ERZeroFreeness.RSPoisPi
import ERZeroFreeness.RSModel
import ERZeroFreeness.RSBetheBasic
import ERZeroFreeness.RSPoisSplit
import ERZeroFreeness.Poisson

/-!
# Proof of [CKPZ, Prop. 3.6]: Lemmas 1.1 and 1.2 (`Λ`, `kl` and Poisson facts)

Part of the self-contained proof of `CKPZProp36 q`, the Potts case of the planted free-energy
bound of Coja-Oghlan, Krzakala, Perkins and Zdeborová [CKPZ, Prop. 3.6], which Lemma C.3
(`lem:rs-ckpz`) cites.  Appendix C is formalized in two layers: the `RS*` modules prove
Theorem C.1 from `CKPZProp36 q` as an explicit hypothesis, and the `CK*` modules prove
`CKPZProp36 q`.  Lemma numbers refer to `docs/ckpz-proof.md`, which gives the mathematics with
every constant.

* Lemma 1.1 (`Λ(y) = y log y` and `kl(y) = Λ(y) - y + 1`): Lipschitz bounds (`ck_lam_lip`,
  `ck_klFun_lip`), size bounds (`ck_lam_abs_le`, `ck_klFun_mem`) and Jensen's inequality for
  countable convex combinations (`ck_lam_tsum_le`).
* Lemma 1.2 (Poisson facts): tail and moment bounds (`ck_pois_tail_two`, `ck_pois_abs_sub_le`,
  `ck_pois_moment_le`), superposition for signed test functions (`ck_poisPi_superpose`) and
  splitting with uniform weights over an arbitrary finite type (`ck_poisson_split_unif`).
-/

open Filter Topology MeasureTheory

namespace ERZeroFreeness

open scoped Classical

noncomputable section


/-! ### Lemma 1.1 and Lemma 1.2(c) -/

/-- Elementary consequences of `CKPar`: `0 < m₋`, `1 ≤ m₊`, `0 ≤ ℓ₀`, `log m₊ ≤ ℓ₀`. -/
private lemma CKAnalysisA_bounds {q : ℕ} {t : ℝ} (hp : CKPar q t) :
    0 < ckMm q t ∧ 1 ≤ ckMp t ∧ 0 ≤ ckEll q t ∧ Real.log (ckMp t) ≤ ckEll q t := by
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast hp.two_le
  have hneg := hp.neg
  have hgt := hp.gt
  have hmm : 0 < ckMm q t := by unfold ckMm; linarith
  have hmm1 : ckMm q t ≤ 1 := by
    unfold ckMm
    nlinarith
  have hmp : 1 ≤ ckMp t := by unfold ckMp; linarith
  have hprod : ckMm q t * ckMp t ≤ 1 := by
    unfold ckMm ckMp
    nlinarith [mul_pos_of_neg_of_neg hneg hneg]
  refine ⟨hmm, hmp, ?_, ?_⟩
  · unfold ckEll
    have := Real.log_nonpos hmm.le hmm1
    linarith
  · unfold ckEll
    have h1 : Real.log (ckMm q t * ckMp t) ≤ 0 :=
      Real.log_nonpos (mul_pos hmm (by linarith)).le hprod
    rw [Real.log_mul hmm.ne' (by linarith)] at h1
    linarith

/-- Tangent line of `Λ(y) = y log y` at `x > 0`. -/
private lemma CKAnalysisA_lam_tangent {x z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    ckLam x + (1 + Real.log x) * (z - x) ≤ ckLam z := by
  unfold ckLam
  have h := Real.log_le_sub_one_of_pos (div_pos hx hz)
  rw [Real.log_div hx.ne' hz.ne'] at h
  have h2 : z * (Real.log x - Real.log z) ≤ z * (x / z - 1) := mul_le_mul_of_nonneg_left h hz.le
  have h3 : z * (x / z - 1) = x - z := by field_simp
  nlinarith [h2, h3]

/-- `|Λ| ≤ b₂ (|log b₁| + |log b₂|)` on `[b₁, b₂] ⊂ (0, ∞)`. -/
private lemma CKAnalysisA_abs_lam_le {b₁ b₂ y : ℝ} (hb : 0 < b₁) (hy : y ∈ Set.Icc b₁ b₂) :
    |ckLam y| ≤ b₂ * (|Real.log b₁| + |Real.log b₂|) := by
  have hy0 : 0 < y := lt_of_lt_of_le hb hy.1
  have h1 : Real.log b₁ ≤ Real.log y := Real.log_le_log hb hy.1
  have h2 : Real.log y ≤ Real.log b₂ := Real.log_le_log hy0 hy.2
  have habs : |Real.log y| ≤ |Real.log b₁| + |Real.log b₂| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log b₁), abs_nonneg (Real.log b₂)]
    · linarith [le_abs_self (Real.log b₂), abs_nonneg (Real.log b₁)]
  unfold ckLam
  rw [abs_mul, abs_of_pos hy0]
  exact mul_le_mul hy.2 habs (abs_nonneg _) (by linarith [hy.1, hy.2])

/-- `Pois(λ)(j+2) ≤ (λ²/2) Pois(λ)(j)`. -/
private lemma CKAnalysisA_poisPMF_add_two_le {lam : ℝ} (hlam : 0 ≤ lam) (j : ℕ) :
    poisPMF lam (j + 2) ≤ lam ^ 2 / 2 * poisPMF lam j := by
  unfold poisPMF
  have hj : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have h2 : (2 : ℝ) * j.factorial ≤ ((j + 2).factorial : ℝ) := by
    have : 2 * j.factorial ≤ (j + 2).factorial := by
      rw [Nat.factorial_succ, Nat.factorial_succ]
      exact Nat.mul_le_mul (by omega) (Nat.le_mul_of_pos_left _ (by omega))
    exact_mod_cast this
  have hnum : 0 ≤ Real.exp (-lam) * lam ^ j * lam ^ 2 := by positivity
  calc Real.exp (-lam) * lam ^ (j + 2) / ((j + 2).factorial : ℝ)
      = (Real.exp (-lam) * lam ^ j * lam ^ 2) / ((j + 2).factorial : ℝ) := by
        rw [pow_add]; ring
    _ ≤ (Real.exp (-lam) * lam ^ j * lam ^ 2) / (2 * j.factorial) :=
        div_le_div_of_nonneg_left hnum (by positivity) h2
    _ = lam ^ 2 / 2 * (Real.exp (-lam) * lam ^ j / j.factorial) := by
        field_simp

/-- `(1 + k)^j ≤ (2^j)^k`, from `1 + k ≤ 2^k`. -/
private lemma CKAnalysisA_one_add_pow_le (k j : ℕ) : (1 + (k : ℝ)) ^ j ≤ ((2 : ℝ) ^ j) ^ k := by
  have h1 : (1 + (k : ℝ)) ≤ 2 ^ k := by
    have h : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    have h' : ((k + 1 : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  calc (1 + (k : ℝ)) ^ j ≤ ((2 : ℝ) ^ k) ^ j := pow_le_pow_left₀ (by positivity) h1 j
    _ = ((2 : ℝ) ^ j) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm]


/-- Lemma 1.1(b): `Λ` is `(1 + a)`-Lipschitz on `[e^{-a}, e^a]`. -/
theorem ck_lam_lip {a y y' : ℝ} (ha : 0 ≤ a) (hy : y ∈ Set.Icc (Real.exp (-a)) (Real.exp a))
    (hy' : y' ∈ Set.Icc (Real.exp (-a)) (Real.exp a)) :
    |ckLam y - ckLam y'| ≤ (1 + a) * |y - y'| := by
  -- `ha` is not needed (for `a < 0` the interval is empty); `1 + a ≥ 1` below.
  have _h1a : (1 : ℝ) ≤ 1 + a := by linarith [ha]
  have hpos : ∀ x ∈ Set.Icc (Real.exp (-a)) (Real.exp a), 0 < x :=
    fun x hx => lt_of_lt_of_le (Real.exp_pos _) hx.1
  have hderiv : ∀ x ∈ Set.Icc (Real.exp (-a)) (Real.exp a),
      HasDerivWithinAt ckLam (Real.log x + 1) (Set.Icc (Real.exp (-a)) (Real.exp a)) x :=
    fun x hx => (Real.hasDerivAt_mul_log (hpos x hx).ne').hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Icc (Real.exp (-a)) (Real.exp a), ‖Real.log x + 1‖ ≤ 1 + a := by
    intro x hx
    have h1 : -a ≤ Real.log x := (Real.le_log_iff_exp_le (hpos x hx)).mpr hx.1
    have h2 : Real.log x ≤ a := (Real.log_le_iff_le_exp (hpos x hx)).mpr hx.2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have := (convex_Icc _ _).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hy' hy
  simpa [Real.norm_eq_abs] using this

/-- Lemma 1.1(b): `kl` is `L`-Lipschitz on `[b₁, b₂] ⊂ (0, ∞)` when `|log b₁|, |log b₂| ≤ L`. -/
theorem ck_klFun_lip {b₁ b₂ L y y' : ℝ} (hb₁ : 0 < b₁) (h₁ : |Real.log b₁| ≤ L)
    (h₂ : |Real.log b₂| ≤ L) (hy : y ∈ Set.Icc b₁ b₂) (hy' : y' ∈ Set.Icc b₁ b₂) :
    |InformationTheory.klFun y - InformationTheory.klFun y'| ≤ L * |y - y'| := by
  have hpos : ∀ x ∈ Set.Icc b₁ b₂, 0 < x := fun x hx => lt_of_lt_of_le hb₁ hx.1
  have hderiv : ∀ x ∈ Set.Icc b₁ b₂,
      HasDerivWithinAt InformationTheory.klFun (Real.log x) (Set.Icc b₁ b₂) x :=
    fun x hx => (InformationTheory.hasDerivAt_klFun (hpos x hx).ne').hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Icc b₁ b₂, ‖Real.log x‖ ≤ L := by
    intro x hx
    have h1 : Real.log b₁ ≤ Real.log x := Real.log_le_log hb₁ hx.1
    have h2 : Real.log x ≤ Real.log b₂ := Real.log_le_log (hpos x hx) hx.2
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [(abs_le.mp h₁).1]
    · linarith [le_abs_self (Real.log b₂)]
  have := (convex_Icc b₁ b₂).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hy' hy
  simpa [Real.norm_eq_abs] using this

/-- Lemma 1.1(d): `|Λ(v)| ≤ (1 + ℓ₀)(2m₊)^d` for `v ∈ [m₋^d, m₊^d]`. -/
theorem ck_lam_abs_le {q : ℕ} {t : ℝ} (hp : CKPar q t) {d : ℕ} {v : ℝ}
    (hv : v ∈ Set.Icc (ckMm q t ^ d) (ckMp t ^ d)) :
    |ckLam v| ≤ (1 + ckEll q t) * (2 * ckMp t) ^ d := by
  obtain ⟨hmm, hmp, hell, hlogmp⟩ := CKAnalysisA_bounds hp
  have hv0 : 0 < v := lt_of_lt_of_le (pow_pos hmm d) hv.1
  have hd0 : (0 : ℝ) ≤ d := d.cast_nonneg
  have hlog1 : -((d : ℝ) * ckEll q t) ≤ Real.log v := by
    have h := Real.log_le_log (pow_pos hmm d) hv.1
    rw [Real.log_pow] at h
    unfold ckEll
    linarith
  have hlog2 : Real.log v ≤ (d : ℝ) * ckEll q t := by
    have h := Real.log_le_log hv0 hv.2
    rw [Real.log_pow] at h
    have h' : (d : ℝ) * Real.log (ckMp t) ≤ (d : ℝ) * ckEll q t :=
      mul_le_mul_of_nonneg_left hlogmp hd0
    linarith
  have habs : |Real.log v| ≤ (d : ℝ) * ckEll q t := abs_le.mpr ⟨hlog1, hlog2⟩
  have hd : (d : ℝ) ≤ 2 ^ d := by exact_mod_cast (Nat.lt_two_pow_self (n := d)).le
  have hmpd : 0 ≤ ckMp t ^ d := pow_nonneg (by linarith) d
  calc |ckLam v| = v * |Real.log v| := by unfold ckLam; rw [abs_mul, abs_of_pos hv0]
    _ ≤ ckMp t ^ d * ((d : ℝ) * ckEll q t) :=
        mul_le_mul hv.2 habs (abs_nonneg _) hmpd
    _ ≤ ckMp t ^ d * (2 ^ d * ckEll q t) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hd hell) hmpd
    _ = ckEll q t * (2 * ckMp t) ^ d := by rw [mul_pow]; ring
    _ ≤ (1 + ckEll q t) * (2 * ckMp t) ^ d :=
        mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (by linarith) d)

/-- `0 ≤ kl(v) ≤ κ₀ = 1 + ℓ₀ m₊` for `v ∈ [m₋, m₊]` (Lemma 1.1(a); the upper bound is used in the
proof of Lemma 5.3). -/
theorem ck_klFun_mem {q : ℕ} {t : ℝ} (hp : CKPar q t) {v : ℝ}
    (hv : v ∈ Set.Icc (ckMm q t) (ckMp t)) :
    0 ≤ InformationTheory.klFun v ∧ InformationTheory.klFun v ≤ 1 + ckEll q t * ckMp t := by
  obtain ⟨hmm, hmp, hell, hlogmp⟩ := CKAnalysisA_bounds hp
  have hv0 : 0 < v := lt_of_lt_of_le hmm hv.1
  refine ⟨InformationTheory.klFun_nonneg hv0.le, ?_⟩
  have hlog2 : Real.log v ≤ ckEll q t := by
    have h := Real.log_le_log hv0 hv.2
    linarith
  have hvl : v * Real.log v ≤ ckMp t * ckEll q t :=
    calc v * Real.log v ≤ v * ckEll q t := mul_le_mul_of_nonneg_left hlog2 hv0.le
      _ ≤ ckMp t * ckEll q t := mul_le_mul_of_nonneg_right hv.2 hell
  rw [InformationTheory.klFun_apply]
  nlinarith

/-- Lemma 1.1(c), Jensen's inequality for countable convex combinations: if `w ≥ 0`, `∑ w = 1`
and every `y i ∈ [b₁, b₂] ⊂ (0, ∞)`, then both series converge and `Λ(∑ w y) ≤ ∑ w Λ(y)`.
Proof: sum the tangent line of `Λ` at the mean (`CKAnalysisA_lam_tangent`). -/
theorem ck_lam_tsum_le {ι : Type*} {w y : ι → ℝ} {b₁ b₂ : ℝ} (hb : 0 < b₁)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : HasSum w 1) (hy : ∀ i, y i ∈ Set.Icc b₁ b₂) :
    Summable (fun i => w i * y i) ∧ Summable (fun i => w i * ckLam (y i)) ∧
      ckLam (∑' i, w i * y i) ≤ ∑' i, w i * ckLam (y i) := by
  have hy0 : ∀ i, 0 < y i := fun i => lt_of_lt_of_le hb (hy i).1
  have hs1 : Summable (fun i => w i * y i) := by
    refine Summable.of_norm_bounded (hw1.summable.mul_left b₂) (fun i => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 i), abs_of_pos (hy0 i), mul_comm]
    exact mul_le_mul_of_nonneg_right (hy i).2 (hw0 i)
  have hs2 : Summable (fun i => w i * ckLam (y i)) := by
    refine Summable.of_norm_bounded
      (hw1.summable.mul_left (b₂ * (|Real.log b₁| + |Real.log b₂|))) (fun i => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 i), mul_comm]
    exact mul_le_mul_of_nonneg_right (CKAnalysisA_abs_lam_le hb (hy i)) (hw0 i)
  refine ⟨hs1, hs2, ?_⟩
  obtain ⟨Y, hY⟩ := hs1
  rw [hY.tsum_eq]
  have hYpos : 0 < Y := by
    have h : HasSum (fun i => w i * b₁) b₁ := by simpa using hw1.mul_right b₁
    have := hasSum_le (fun i => mul_le_mul_of_nonneg_left (hy i).1 (hw0 i)) h hY
    linarith
  have htan : ∀ i, w i * (ckLam Y + (1 + Real.log Y) * (y i - Y)) ≤ w i * ckLam (y i) :=
    fun i => mul_le_mul_of_nonneg_left (CKAnalysisA_lam_tangent hYpos (hy0 i)) (hw0 i)
  have hsum : HasSum (fun i => w i * (ckLam Y + (1 + Real.log Y) * (y i - Y))) (ckLam Y) := by
    have h := (hw1.mul_right (ckLam Y - (1 + Real.log Y) * Y)).add
      (hY.mul_left (1 + Real.log Y))
    rw [show 1 * (ckLam Y - (1 + Real.log Y) * Y) + (1 + Real.log Y) * Y = ckLam Y by ring] at h
    have hfun : (fun i => w i * (ckLam Y + (1 + Real.log Y) * (y i - Y))) =
        fun i => w i * (ckLam Y - (1 + Real.log Y) * Y) + (1 + Real.log Y) * (w i * y i) := by
      funext i
      ring
    rw [hfun]
    exact h
  exact hasSum_le htan hsum hs2.hasSum

/-- Lemma 1.2(c): `P(N ≥ 2) ≤ λ²/2` for `N ∼ Pois(λ)`. -/
theorem ck_pois_tail_two {lam : ℝ} (hlam : 0 ≤ lam) :
    ∑' k : ℕ, (if 2 ≤ k then poisPMF lam k else 0) ≤ lam ^ 2 / 2 := by
  set f : ℕ → ℝ := fun k => if 2 ≤ k then poisPMF lam k else 0 with hf
  have hshift : ∀ j, f (j + 2) = poisPMF lam (j + 2) := fun j => by simp [hf]
  have hbound : ∀ j, f (j + 2) ≤ lam ^ 2 / 2 * poisPMF lam j := fun j => by
    rw [hshift]
    exact CKAnalysisA_poisPMF_add_two_le hlam j
  have hnn : ∀ j, 0 ≤ f (j + 2) := fun j => by
    rw [hshift]
    exact poisPMF_nonneg hlam _
  have hS : HasSum (fun j => lam ^ 2 / 2 * poisPMF lam j) (lam ^ 2 / 2 * 1) :=
    (hasSum_poisPMF hlam).mul_left _
  have hsum2 : Summable (fun j => f (j + 2)) := hS.summable.of_nonneg_of_le hnn hbound
  have hsum : Summable f := (summable_nat_add_iff 2).mp hsum2
  rw [← hsum.sum_add_tsum_nat_add 2]
  have h01 : ∑ i ∈ Finset.range 2, f i = 0 := by simp [hf, Finset.sum_range_succ]
  rw [h01, zero_add]
  calc ∑' j, f (j + 2) ≤ ∑' j, lam ^ 2 / 2 * poisPMF lam j :=
        hsum2.tsum_le_tsum hbound hS.summable
    _ = lam ^ 2 / 2 := by rw [hS.tsum_eq, mul_one]

/-- Lemma 1.2(c): `E|N - λ| ≤ √λ` for `N ∼ Pois(λ)`, the series being summable. -/
theorem ck_pois_abs_sub_le {lam : ℝ} (hlam : 0 ≤ lam) :
    Summable (fun k : ℕ => poisPMF lam k * |(k : ℝ) - lam|) ∧
      ∑' k : ℕ, poisPMF lam k * |(k : ℝ) - lam| ≤ Real.sqrt lam :=
  ⟨summable_poisPMF_mul_abs_sub hlam, poisExp_abs_sub_le hlam⟩

/-- Lemma 1.2(c): `E[(1 + N)^j y^N] ≤ e^{λ(2^j y - 1)}` for `N ∼ Pois(λ)` and `y ≥ 0`, the series
being summable.  Proof: `1 + k ≤ 2^k` and `E[z^N] = e^{λ(z - 1)}`
(`RSPoisPiAux.hasSum_poisPMF_mul_pow`). -/
theorem ck_pois_moment_le {lam y : ℝ} (hlam : 0 ≤ lam) (hy : 0 ≤ y) (j : ℕ) :
    Summable (fun k : ℕ => poisPMF lam k * ((1 + (k : ℝ)) ^ j * y ^ k)) ∧
      ∑' k : ℕ, poisPMF lam k * ((1 + (k : ℝ)) ^ j * y ^ k) ≤
        Real.exp (lam * (2 ^ j * y - 1)) := by
  have hH := RSPoisPiAux.hasSum_poisPMF_mul_pow (lam := lam) ((2 : ℝ) ^ j * y)
  have hle : ∀ k : ℕ, poisPMF lam k * ((1 + (k : ℝ)) ^ j * y ^ k) ≤
      poisPMF lam k * ((2 : ℝ) ^ j * y) ^ k := by
    intro k
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (CKAnalysisA_one_add_pow_le k j) (pow_nonneg hy k))
      (poisPMF_nonneg hlam k)
  have hnn : ∀ k : ℕ, 0 ≤ poisPMF lam k * ((1 + (k : ℝ)) ^ j * y ^ k) := fun k =>
    mul_nonneg (poisPMF_nonneg hlam k) (mul_nonneg (by positivity) (pow_nonneg hy k))
  have hs : Summable (fun k : ℕ => poisPMF lam k * ((1 + (k : ℝ)) ^ j * y ^ k)) :=
    hH.summable.of_nonneg_of_le hnn hle
  exact ⟨hs, hasSum_le hle hs.hasSum hH⟩

/-! ### Lemma 1.2(b): superposition for signed test functions -/

/-- `Φ = Φ⁺ - Φ⁻` with `Φ⁺ = max Φ 0`, `Φ⁻ = max (-Φ) 0`. -/
private theorem CKAnalysisB_pos_sub_neg (x : ℝ) : x = max x 0 - max (-x) 0 := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), sub_neg_eq_add, zero_add]

/-- Superposition as a `HasSum` on pairs, for a signed `Φ` with the domination `|Φ N| ≤ A c^{∑ N}`:
apply the nonnegative `rs_hasSum_poisPi_superpose` to `Φ⁺` and `Φ⁻` and subtract. -/
private theorem CKAnalysisB_hasSum_superpose {ι : Type*} [Fintype ι] {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) {Φ : (ι → ℕ) → ℝ} {A c : ℝ} (hc : 0 ≤ c)
    (hΦ : ∀ N, |Φ N| ≤ A * c ^ (∑ i, N i)) :
    HasSum (fun z : (ι → ℕ) × (ι → ℕ) => poisPi a z.1 * poisPi b z.2 * Φ (z.1 + z.2))
      (∑' M, poisPi (a + b) M * Φ M) := by
  have hab : ∀ i, 0 ≤ (a + b) i := fun i => add_nonneg (ha i) (hb i)
  have hp0 : ∀ N, 0 ≤ max (Φ N) 0 := fun N => le_max_right _ _
  have hm0 : ∀ N, 0 ≤ max (-Φ N) 0 := fun N => le_max_right _ _
  have hpb : ∀ N, |max (Φ N) 0| ≤ A * c ^ (∑ i, N i) := fun N => by
    rw [abs_of_nonneg (hp0 N)]
    exact le_trans (max_le (le_abs_self _) (abs_nonneg _)) (hΦ N)
  have hmb : ∀ N, |max (-Φ N) 0| ≤ A * c ^ (∑ i, N i) := fun N => by
    rw [abs_of_nonneg (hm0 N)]
    exact le_trans (max_le (neg_le_abs _) (abs_nonneg _)) (hΦ N)
  have hsp := rs_summable_poisPi_of_abs_le hab hc hpb
  have hsm := rs_summable_poisPi_of_abs_le hab hc hmb
  have HP := rs_hasSum_poisPi_superpose ha hb hp0 hsp
  have HM := rs_hasSum_poisPi_superpose ha hb hm0 hsm
  have hS : ∑' M, poisPi (a + b) M * Φ M =
      ∑' M, poisPi (a + b) M * max (Φ M) 0 - ∑' M, poisPi (a + b) M * max (-Φ M) 0 := by
    rw [← hsp.tsum_sub hsm]
    exact tsum_congr fun M => by rw [← mul_sub, ← CKAnalysisB_pos_sub_neg]
  rw [hS]
  refine (HP.sub HM).congr_fun fun z => ?_
  rw [← mul_sub, ← CKAnalysisB_pos_sub_neg]

/-! ### Lemma 1.2(d): Poisson splitting with uniform weights -/

/-- The count vector `i ↦ #{j : y j = i}` of a word `y : Fin d → ι`. -/
private def CKAnalysisB_count {ι : Type*} {d : ℕ} (y : Fin d → ι) : ι → ℕ :=
  fun i => (Finset.univ.filter fun j => y j = i).card

/-- `∑_i count(y)_i = d`. -/
private theorem CKAnalysisB_sum_count {ι : Type*} [Fintype ι] {d : ℕ} (y : Fin d → ι) :
    ∑ i, CKAnalysisB_count y i = d := by
  unfold CKAnalysisB_count
  rw [← Finset.card_eq_sum_card_fiberwise (fun j _ => Finset.mem_univ (y j))]
  simp

private theorem CKAnalysisB_count_mem {ι : Type*} [Fintype ι] {d : ℕ} (y : Fin d → ι) :
    CKAnalysisB_count y ∈ Finset.piAntidiag Finset.univ d := by
  rw [Finset.mem_piAntidiag]
  exact ⟨CKAnalysisB_sum_count y, fun _ _ => Finset.mem_univ _⟩

/-- In `ℝ[ι → ℕ]`: `(∑_i x_i)^d = ∑_{y : Fin d → ι} single(count y) 1`, `x_i = single δ_i 1`. -/
private theorem CKAnalysisB_pow_sum_single {ι : Type*} [Fintype ι] {d : ℕ} :
    (∑ i : ι, AddMonoidAlgebra.single (Pi.single i 1 : ι → ℕ) (1 : ℝ)) ^ d =
      ∑ y : Fin d → ι, AddMonoidAlgebra.single (CKAnalysisB_count y) (1 : ℝ) := by
  rw [Finset.sum_pow', Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [AddMonoidAlgebra.prod_single]
  congr 1
  · funext i
    simp only [CKAnalysisB_count, Finset.sum_apply, Pi.single_apply, Finset.sum_boole,
      Nat.cast_id]
    exact congrArg Finset.card (Finset.filter_congr fun j _ => eq_comm)
  · simp

/-- The multinomial theorem in `ℝ[ι → ℕ]`:
`(∑_i x_i)^d = ∑_{N ∈ piAntidiag univ d} single N multinomial(N)`. -/
private theorem CKAnalysisB_pow_sum_single' {ι : Type*} [Fintype ι] {d : ℕ} :
    (∑ i : ι, AddMonoidAlgebra.single (Pi.single i 1 : ι → ℕ) (1 : ℝ)) ^ d =
      ∑ k ∈ Finset.piAntidiag Finset.univ d,
        AddMonoidAlgebra.single k (Nat.multinomial Finset.univ k : ℝ) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [AddMonoidAlgebra.single_pow, one_pow, AddMonoidAlgebra.prod_single,
    Finset.prod_const_one]
  rw [AddMonoidAlgebra.natCast_def, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
  congr 1
  funext i
  simp [Finset.sum_apply, Pi.single_apply]

/-- **Multinomial fibre count.** `#{y : Fin d → ι | count(y) = N} = multinomial(N)` if
`∑_i N_i = d`, and `0` otherwise. -/
private theorem CKAnalysisB_card_fiber {ι : Type*} [Fintype ι] (d : ℕ) (N : ι → ℕ) :
    (((Finset.univ.filter fun y : Fin d → ι => CKAnalysisB_count y = N).card : ℕ) : ℝ) =
      if N ∈ Finset.piAntidiag Finset.univ d then (Nat.multinomial Finset.univ N : ℝ) else 0 := by
  have h := congrArg (fun z => z.coeff N)
    ((CKAnalysisB_pow_sum_single (ι := ι) (d := d)).symm.trans
      (CKAnalysisB_pow_sum_single' (d := d)))
  simp only [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.single_apply] at h
  rw [Finset.sum_boole] at h
  rw [h, Finset.sum_ite_eq']

/-- For `∑_i N_i = d`: `P_{r/K}(N) = Pois(r)(d) · K^{-d} · multinomial(N)`, `K = |ι|`. -/
private theorem CKAnalysisB_poisPi_eq {ι : Type*} [Fintype ι] [Nonempty ι] {d : ℕ} (r : ℝ)
    (N : ι → ℕ) (hN : N ∈ Finset.piAntidiag Finset.univ d) :
    poisPi (fun _ => r / Fintype.card ι) N =
      poisPMF r d * (((Fintype.card ι : ℝ) ^ d)⁻¹ * (Nat.multinomial Finset.univ N : ℝ)) := by
  rw [Finset.mem_piAntidiag] at hN
  have hsum : ∑ i, N i = d := hN.1
  have hspec := Nat.multinomial_spec Finset.univ N
  rw [hsum] at hspec
  have hspecR : (∏ i, ((N i).factorial : ℝ)) * (Nat.multinomial Finset.univ N : ℝ) =
      (d.factorial : ℝ) := by
    exact_mod_cast hspec
  have hmult_pos : (0:ℝ) < Nat.multinomial Finset.univ N := by
    exact_mod_cast Nat.multinomial_pos _ _
  have hK : (Fintype.card ι : ℝ) ≠ 0 := by
    have := Fintype.card_pos (α := ι)
    positivity
  unfold poisPi poisPMF
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_pow_eq_pow_sum, hsum, Finset.card_univ]
  rw [← hspecR]
  have hexp : Real.exp (-(r / Fintype.card ι)) ^ (Fintype.card ι) = Real.exp (-r) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have hpow : (r / Fintype.card ι) ^ d = r ^ d * ((Fintype.card ι : ℝ) ^ d)⁻¹ := by
    rw [div_pow, div_eq_mul_inv]
  rw [hexp, hpow]
  field_simp

/-- The `d`-slice: `∑_{∑ N = d} P_{r/K}(N) Φ(N) = Pois(r)(d) K^{-d} ∑_y Φ(count y)`. -/
private theorem CKAnalysisB_sum_piAntidiag_eq {ι : Type*} [Fintype ι] [Nonempty ι] (r : ℝ)
    (Φ : (ι → ℕ) → ℝ) (d : ℕ) :
    ∑ N ∈ Finset.piAntidiag Finset.univ d, poisPi (fun _ => r / Fintype.card ι) N * Φ N =
      poisPMF r d * (((Fintype.card ι : ℝ) ^ d)⁻¹ *
        ∑ y : Fin d → ι, Φ (CKAnalysisB_count y)) := by
  have hfib : ∑ y : Fin d → ι, Φ (CKAnalysisB_count y) =
      ∑ N ∈ Finset.piAntidiag Finset.univ d, (Nat.multinomial Finset.univ N : ℝ) * Φ N := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := CKAnalysisB_count)
      (t := Finset.piAntidiag Finset.univ d) (fun y _ => CKAnalysisB_count_mem y)]
    refine Finset.sum_congr rfl fun N hN => ?_
    rw [Finset.sum_congr rfl (fun y hy => by rw [(Finset.mem_filter.1 hy).2]), Finset.sum_const,
      nsmul_eq_mul, CKAnalysisB_card_fiber, if_pos hN]
  rw [hfib, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun N hN => ?_
  rw [CKAnalysisB_poisPi_eq r N hN]
  ring

/-- The same slice as a `HasSum` over the fibre `{N // ∑_i N_i = d}`. -/
private theorem CKAnalysisB_hasSum_fiber {ι : Type*} [Fintype ι] [Nonempty ι] (r : ℝ)
    (Φ : (ι → ℕ) → ℝ) (d : ℕ) :
    HasSum (fun y : {N : ι → ℕ // (∑ i, N i) = d} =>
        poisPi (fun _ => r / Fintype.card ι) y.1 * Φ y.1)
      (poisPMF r d * (((Fintype.card ι : ℝ) ^ d)⁻¹ *
        ∑ y : Fin d → ι, Φ (CKAnalysisB_count y))) := by
  rw [← CKAnalysisB_sum_piAntidiag_eq r Φ d]
  have H := (Finset.piAntidiag Finset.univ d).hasSum
    (fun N => poisPi (fun _ => r / Fintype.card ι) N * Φ N)
  let E : {N : ι → ℕ // (∑ i, N i) = d} ≃
      ((Finset.piAntidiag Finset.univ d : Finset (ι → ℕ)) : Set (ι → ℕ)) :=
    Equiv.subtypeEquivRight fun N => by
      simp [Finset.mem_piAntidiag]
  rw [← E.hasSum_iff] at H
  exact H

/-- Lemma 1.2(b) for product-Poisson fields and a signed `Φ` with `|Φ(N)| ≤ A c^{∑ N}`:
`E Φ(N) = E Φ(N₁ + N₂)` for `N ∼ Pois(a + b)` and independent `N₁ ∼ Pois(a)`, `N₂ ∼ Pois(b)`,
the right side as an iterated sum.  Proof: `rs_hasSum_poisPi_superpose` for the positive and
negative parts of `Φ`. -/
theorem ck_poisPi_superpose {ι : Type*} [Fintype ι] {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 ≤ b i) {Φ : (ι → ℕ) → ℝ} {A c : ℝ} (hc : 0 ≤ c)
    (hΦ : ∀ N, |Φ N| ≤ A * c ^ (∑ i, N i)) :
    ∑' N, poisPi (a + b) N * Φ N = ∑' N, poisPi a N * ∑' N', poisPi b N' * Φ (N + N') := by
  have H := CKAnalysisB_hasSum_superpose ha hb hc hΦ
  rw [← H.tsum_eq, H.summable.tsum_prod]
  refine tsum_congr fun N => ?_
  rw [← tsum_mul_left]
  exact tsum_congr fun N' => by dsimp only; ring

/-- Lemma 1.2(d) with uniform weights on a nonempty finite type `ι`, `K = |ι|`: if
`|Φ(D)| ≤ A c^{∑ D}`, then
`E_{D ∼ Pois(r/K)^ι} Φ(D) = ∑_d Pois(r)(d) K^{-d} ∑_{y : Fin d → ι} Φ(count(y))`, where
`count(y)_i = #{j : y j = i}`.  The argument is that of `rs_poisson_split`: the multinomial fibre
count, then regrouping by `d = ∑_i D_i`. -/
theorem ck_poisson_split_unif {ι : Type*} [Fintype ι] [Nonempty ι] {r : ℝ} (hr : 0 ≤ r)
    {Φ : (ι → ℕ) → ℝ} {A c : ℝ} (hc : 0 ≤ c) (hΦ : ∀ D, |Φ D| ≤ A * c ^ (∑ i, D i)) :
    ∑' D, poisPi (fun _ => r / Fintype.card ι) D * Φ D =
      ∑' d : ℕ, poisPMF r d * (((Fintype.card ι : ℝ) ^ d)⁻¹ *
        ∑ y : Fin d → ι, Φ fun i => (Finset.univ.filter fun j => y j = i).card) := by
  have hlam : ∀ i : ι, 0 ≤ (fun _ => r / Fintype.card ι) i :=
    fun _ => div_nonneg hr (Nat.cast_nonneg _)
  have hFsum := rs_summable_poisPi_of_abs_le hlam hc hΦ
  have h1 := (Equiv.sigmaFiberEquiv (fun N : ι → ℕ => ∑ i, N i)).hasSum_iff.mpr hFsum.hasSum
  exact (h1.sigma fun d => CKAnalysisB_hasSum_fiber r Φ d).tsum_eq.symm

end

end ERZeroFreeness
