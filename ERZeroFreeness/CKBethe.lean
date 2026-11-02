/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.CKDefs
import ERZeroFreeness.CKMatrix
import ERZeroFreeness.CKAnalysis
import ERZeroFreeness.RSPoisPi
import ERZeroFreeness.RSModel
import ERZeroFreeness.RSBetheBasic
import ERZeroFreeness.RSPoisSplit
import ERZeroFreeness.Poisson

/-!
# Proof of [CKPZ, Prop. 3.6]: Lemmas 2.1(a), 2.2 and 2.3 (the Bethe functional at finite laws)

Part of the self-contained proof of `CKPZProp36 q`, the Potts case of the planted free-energy
bound of Coja-Oghlan, Krzakala, Perkins and Zdeborová [CKPZ, Prop. 3.6], which Lemma C.3
(`lem:rs-ckpz`) cites.  Appendix C is formalized in two layers: the `RS*` modules prove
Theorem C.1 from `CKPZProp36 q` as an explicit hypothesis, and the `CK*` modules prove
`CKPZProp36 q`.  Lemma numbers refer to `docs/ckpz-proof.md`.

A finitely supported law `ν = ∑_j w_j δ_{μ_j}` on the simplex is given by its weights and atoms
(`ckFinLaw`), and `Ψ_r(ν) = BV_r(ν) - (r/2) BE(ν)` by the finite sums `ckPsi`, `ckBV`, `ckBE`.

## Route

* Lemma 2.1(a) (`ck_BV_emp`): `ck_poisson_split_unif` with `ι = Fin n`; `V_d` of the tuple
  `(m (y i))_i` is rewritten through the occupation numbers of `y` (`Finset.prod_fiberwise'`).
* Lemma 2.2 (`ck_psi_rate`): in place of the rate coupling of Lemma 1.2(e), the proof uses the
  pointwise bound `|Pois(s)(d) - Pois(r)(d)| ≤ (s - r) · 2 (2(s+1))^d / d!` (from
  `|e^{-s} - e^{-r}| ≤ s - r` and `abs_pow_sub_pow_le`), giving
  `C = 2(1+ℓ₀) ∑_d (2(s+1)·2m₊)^d/d! + (1+ℓ₀)m₊`.
* Lemma 2.3 (`ck_mean_fix`): the new atom is the index `0` (`Fin.cons`), with
  `α = min{1, q ‖m̄ - u‖₂}`, the Euclidean norm in place of the sup norm; for `α = 0` the new
  atom is `ζ = u`, with weight `0`.  The coupling bound `ckBethe_mix` splits the tuples
  `Fin d → Fin (K+1)` into those avoiding `0` (weight `(1-α)^d` times the old average) and those
  hitting it (weight `1 - (1-α)^d ≤ dα`); the edge term is the case `d = 2`.  The constant is
  `C = q (2(1+ℓ₀) ∑_d (4 s m₊)^d/d! + 4 s (1+ℓ₀) m₊)`.
-/

open Filter Topology MeasureTheory

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-! ### Elementary bounds on the Bethe quantities -/

/-- An average of `q > 0` numbers in `[L, U]` lies in `[L, U]`. -/
private lemma ckBethe_avg_mem {q : ℕ} (hq : 0 < q) {f : Fin q → ℝ} {L U : ℝ}
    (hf : ∀ a, f a ∈ Set.Icc L U) : (q : ℝ)⁻¹ * ∑ a, f a ∈ Set.Icc L U := by
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  constructor
  · have h : ∑ _a : Fin q, L ≤ ∑ a, f a := Finset.sum_le_sum fun a _ => (hf a).1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    rw [le_inv_mul_iff₀ hq']
    exact h
  · have h : ∑ a, f a ≤ ∑ _a : Fin q, U := Finset.sum_le_sum fun a _ => (hf a).2
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    rw [inv_mul_le_iff₀ hq']
    exact h

/-- `∏_i b_i^{D_i} ∈ [L^{|D|}, U^{|D|}]` when every `b_i ∈ [L, U]`, `L ≥ 0`. -/
private lemma ckBethe_prod_pow_mem {ι : Type*} [Fintype ι] {b : ι → ℝ} {L U : ℝ} (hL : 0 ≤ L)
    (hb : ∀ i, b i ∈ Set.Icc L U) (D : ι → ℕ) :
    ∏ i, b i ^ D i ∈ Set.Icc (L ^ (∑ i, D i)) (U ^ (∑ i, D i)) := by
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
  constructor
  · exact Finset.prod_le_prod (fun i _ => pow_nonneg hL _)
      (fun i _ => pow_le_pow_left₀ hL (hb i).1 _)
  · exact Finset.prod_le_prod (fun i _ => pow_nonneg (hL.trans (hb i).1) _)
      (fun i _ => pow_le_pow_left₀ (hL.trans (hb i).1) (hb i).2 _)

/-- `Y_μ(D) ∈ [m₋^{|D|}, m₊^{|D|}]` (Lemma 1.4(b)). -/
private lemma ckBethe_Y_mem {q : ℕ} {t : ℝ} (hp : CKPar q t) {ι : Type*} [Fintype ι]
    {m : ι → Fin q → ℝ} (hm : ∀ v, m v ∈ stdSimplex ℝ (Fin q)) (D : ι → ℕ) :
    (q : ℝ)⁻¹ * ∑ c, ∏ v, betheMvec q t (m v) c ^ D v ∈
      Set.Icc (ckMm q t ^ (∑ v, D v)) (ckMp t ^ (∑ v, D v)) := by
  have hq : 0 < q := by have := hp.two_le; omega
  have hmm := (ck_const_bounds hp).1
  exact ckBethe_avg_mem hq fun c =>
    ckBethe_prod_pow_mem hmm.le (fun v => ck_betheMvec_mem hp (hm v) c) D

/-- `V_d ∈ [m₋^d, m₊^d]`. -/
private lemma ckBethe_V_mem {q : ℕ} {t : ℝ} (hp : CKPar q t) {d : ℕ}
    {ρ : Fin d → Fin q → ℝ} (hρ : ∀ i, ρ i ∈ stdSimplex ℝ (Fin q)) :
    betheV q t ρ ∈ Set.Icc (ckMm q t ^ d) (ckMp t ^ d) := by
  have h := ckBethe_Y_mem hp hρ (fun _ => 1)
  simpa only [pow_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one, betheV] using h

/-- `|Λ(V_d)| ≤ (1 + ℓ₀)(2 m₊)^d` (Lemma 1.1(d)). -/
private lemma ckBethe_lamV_abs_le {q : ℕ} {t : ℝ} (hp : CKPar q t) {d : ℕ}
    {ρ : Fin d → Fin q → ℝ} (hρ : ∀ i, ρ i ∈ stdSimplex ℝ (Fin q)) :
    |ckLam (betheV q t ρ)| ≤ (1 + ckEll q t) * (2 * ckMp t) ^ d :=
  ck_lam_abs_le hp (ckBethe_V_mem hp hρ)

/-- `|Λ(E)| ≤ (1 + ℓ₀)(2 m₊)` (Lemma 1.1(d)). -/
private lemma ckBethe_lamE_abs_le {q : ℕ} {t : ℝ} (hp : CKPar q t) {μ ν : Fin q → ℝ}
    (hμ : μ ∈ stdSimplex ℝ (Fin q)) (hν : ν ∈ stdSimplex ℝ (Fin q)) :
    |ckLam (betheE q t μ ν)| ≤ (1 + ckEll q t) * (2 * ckMp t) := by
  have h := ck_betheE_mem hp hμ hν
  have h1 : betheE q t μ ν ∈ Set.Icc (ckMm q t ^ 1) (ckMp t ^ 1) := by
    rw [pow_one, pow_one]; exact h
  simpa only [pow_one] using ck_lam_abs_le hp h1

/-- `V_d` of the tuple `(m (y i))_i`, written with the occupation numbers of `y`. -/
private lemma ckBethe_betheV_comp {q n d : ℕ} (t : ℝ) (m : Fin n → Fin q → ℝ)
    (y : Fin d → Fin n) :
    betheV q t (fun i => m (y i)) =
      (q : ℝ)⁻¹ * ∑ c, ∏ v, betheMvec q t (m v) c ^ (Finset.univ.filter fun j => y j = v).card := by
  unfold betheV
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.prod_fiberwise' Finset.univ y (fun v => betheMvec q t (m v) c)]
  simp only [Finset.prod_const]

/-- Lemma 2.1(a): for the empirical law `ρ = n⁻¹ ∑_v δ_{m_v}` of `n ≥ 1` points of the simplex,
`BV_r(ρ) = ∑_{D ∈ ℕ^n} ∏_v Pois(r/n)(D_v) · Λ(Y(D))` with `Y(D) = q⁻¹ ∑_c ∏_v (M m_v)_c^{D_v}`. -/
theorem ck_BV_emp {q n : ℕ} {t : ℝ} (hp : CKPar q t) (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r)
    {m : Fin n → Fin q → ℝ} (hm : ∀ v, m v ∈ stdSimplex ℝ (Fin q)) :
    ckBV q t r (fun _ => (n : ℝ)⁻¹) m =
      ∑' D : Fin n → ℕ, poisPi (fun _ => r / n) D *
        ckLam ((q : ℝ)⁻¹ * ∑ c, ∏ v, betheMvec q t (m v) c ^ D v) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hc : (0 : ℝ) ≤ 2 * ckMp t := by
    have := (ck_const_bounds hp).2.2.1
    linarith
  have hΦ : ∀ D : Fin n → ℕ,
      |ckLam ((q : ℝ)⁻¹ * ∑ c, ∏ v, betheMvec q t (m v) c ^ D v)| ≤
        (1 + ckEll q t) * (2 * ckMp t) ^ (∑ i, D i) :=
    fun D => ck_lam_abs_le hp (ckBethe_Y_mem hp hm D)
  have H := ck_poisson_split_unif (ι := Fin n)
    (Φ := fun D => ckLam ((q : ℝ)⁻¹ * ∑ c, ∏ v, betheMvec q t (m v) c ^ D v)) hr hc hΦ
  simp only [Fintype.card_fin] at H
  rw [H]
  simp only [ckBV]
  refine tsum_congr fun d => ?_
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow, ckBethe_betheV_comp]
  congr!

/-! ### Finite laws: bounds on the vertex and edge terms -/

/-- A `w^{⊗d}`-average of a function bounded by `B` is bounded by `B`. -/
private lemma ckBethe_wsum_abs_le {K d : ℕ} {w : Fin K → ℝ} (hw0 : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) {G : (Fin d → Fin K) → ℝ} {B : ℝ} (hG : ∀ y, |G y| ≤ B) :
    |∑ y : Fin d → Fin K, (∏ i, w (y i)) * G y| ≤ B := by
  calc |∑ y : Fin d → Fin K, (∏ i, w (y i)) * G y|
      ≤ ∑ y : Fin d → Fin K, |(∏ i, w (y i)) * G y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y : Fin d → Fin K, (∏ i, w (y i)) * B := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [abs_mul, abs_of_nonneg (Finset.prod_nonneg fun i _ => hw0 (y i))]
        exact mul_le_mul_of_nonneg_left (hG y) (Finset.prod_nonneg fun i _ => hw0 (y i))
    _ = B := by rw [← Finset.sum_mul, ← Fintype.sum_pow, hw1, one_pow, one_mul]

/-- `|∫ Λ(V_d) dν^{⊗d}| ≤ (1 + ℓ₀)(2 m₊)^d` for a finitely supported law `ν`. -/
private lemma ckBethe_g_abs_le {q : ℕ} {t : ℝ} (hp : CKPar q t) {K : ℕ} {w : Fin K → ℝ}
    {μ : Fin K → Fin q → ℝ} (h : ckFinLaw q w μ) (d : ℕ) :
    |∑ y : Fin d → Fin K, (∏ i, w (y i)) * ckLam (betheV q t fun i => μ (y i))| ≤
      (1 + ckEll q t) * (2 * ckMp t) ^ d :=
  ckBethe_wsum_abs_le h.1 h.2.1 fun y => ckBethe_lamV_abs_le hp fun i => h.2.2 (y i)

/-- `BE(ν)` as a `w^{⊗2}`-average over pairs `y : Fin 2 → Fin K`. -/
private lemma ckBethe_BE_eq {q : ℕ} {t : ℝ} {K : ℕ} (w : Fin K → ℝ) (μ : Fin K → Fin q → ℝ) :
    ckBE q t w μ =
      ∑ y : Fin 2 → Fin K, (∏ i, w (y i)) * ckLam (betheE q t (μ (y 0)) (μ (y 1))) := by
  unfold ckBE
  rw [← Fintype.sum_prod_type']
  refine (Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin K) _ _ fun y => ?_).symm
  simp [Fin.prod_univ_two, piFinTwoEquiv_apply]

/-- `|BE(ν)| ≤ (1 + ℓ₀)(2 m₊)`. -/
private lemma ckBethe_BE_abs_le {q : ℕ} {t : ℝ} (hp : CKPar q t) {K : ℕ} {w : Fin K → ℝ}
    {μ : Fin K → Fin q → ℝ} (h : ckFinLaw q w μ) :
    |ckBE q t w μ| ≤ (1 + ckEll q t) * (2 * ckMp t) := by
  rw [ckBethe_BE_eq]
  exact ckBethe_wsum_abs_le h.1 h.2.1 fun y => ckBethe_lamE_abs_le hp (h.2.2 _) (h.2.2 _)

/-! ### Poisson series -/

/-- Domination: `|g d| ≤ A c^d` makes `d ↦ Pois(r)(d) g d` summable. -/
private lemma ckBethe_pois_summable {r : ℝ} (hr : 0 ≤ r) {g : ℕ → ℝ} {A c : ℝ}
    (hg : ∀ d, |g d| ≤ A * c ^ d) : Summable (fun d => poisPMF r d * g d) := by
  refine Summable.of_norm_bounded
    ((RSPoisPiAux.hasSum_poisPMF_mul_pow (lam := r) c).summable.mul_left A) fun d => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poisPMF_nonneg hr d)]
  calc poisPMF r d * |g d| ≤ poisPMF r d * (A * c ^ d) :=
        mul_le_mul_of_nonneg_left (hg d) (poisPMF_nonneg hr d)
    _ = A * (poisPMF r d * c ^ d) := by ring

/-- `|e^{-s} - e^{-r}| ≤ s - r` for `0 ≤ r ≤ s`. -/
private lemma ckBethe_exp_diff_le {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    |Real.exp (-s) - Real.exp (-r)| ≤ s - r := by
  have hexp : Real.exp (-s) = Real.exp (-r) * Real.exp (-(s - r)) := by
    rw [← Real.exp_add]; ring_nf
  have he1 : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he2 := Real.add_one_le_exp (-(s - r))
  have he3 : 0 < Real.exp (-r) := Real.exp_pos _
  have he4 : Real.exp (-(s - r)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [abs_sub_comm, abs_of_nonneg (by rw [hexp]; nlinarith), hexp]
  nlinarith

/-- `|Pois(s)(d) - Pois(r)(d)| ≤ (s - r) · 2 (2(s+1))^d / d!` for `0 ≤ r ≤ s`. -/
private lemma ckBethe_pois_diff_le {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (d : ℕ) :
    |poisPMF s d - poisPMF r d| ≤ (s - r) * (2 * (2 * (s + 1)) ^ d / d.factorial) := by
  have hs : 0 ≤ s := hr.trans hrs
  have hf : (0 : ℝ) < d.factorial := by positivity
  unfold poisPMF
  rw [← sub_div, abs_div, abs_of_pos hf, ← mul_div_assoc, div_le_div_iff_of_pos_right hf]
  have h1 := ckBethe_exp_diff_le hr hrs
  have h2 : |s ^ d - r ^ d| ≤ (s - r) * (d * s ^ (d - 1)) := by
    have := abs_pow_sub_pow_le s r d
    rwa [abs_of_nonneg (by linarith : 0 ≤ s - r), abs_of_nonneg hs, abs_of_nonneg hr,
      max_eq_left hrs, mul_assoc] at this
  have h3 : s ^ d ≤ (2 * (s + 1)) ^ d := pow_le_pow_left₀ hs (by linarith) d
  have h4 : (d : ℝ) * s ^ (d - 1) ≤ (2 * (s + 1)) ^ d := by
    have hd : (d : ℝ) ≤ 2 ^ d := by exact_mod_cast Nat.lt_two_pow_self.le
    have h5 : s ^ (d - 1) ≤ (s + 1) ^ d :=
      (pow_le_pow_left₀ hs (by linarith) (d - 1)).trans
        (pow_le_pow_right₀ (by linarith) (Nat.sub_le d 1))
    rw [mul_pow]
    exact mul_le_mul hd h5 (by positivity) (by positivity)
  have he1 : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have he0 : 0 ≤ Real.exp (-r) := (Real.exp_pos _).le
  have hsr : 0 ≤ s - r := by linarith
  calc |Real.exp (-s) * s ^ d - Real.exp (-r) * r ^ d|
      = |(Real.exp (-s) - Real.exp (-r)) * s ^ d + Real.exp (-r) * (s ^ d - r ^ d)| := by
        ring_nf
    _ ≤ |Real.exp (-s) - Real.exp (-r)| * s ^ d + Real.exp (-r) * |s ^ d - r ^ d| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hs d), abs_of_nonneg he0]
    _ ≤ (s - r) * s ^ d + 1 * ((s - r) * (d * s ^ (d - 1))) := by
        gcongr
    _ ≤ (s - r) * (2 * (s + 1)) ^ d + 1 * ((s - r) * (2 * (s + 1)) ^ d) := by
        gcongr
    _ = (s - r) * (2 * (2 * (s + 1)) ^ d) := by ring

/-- Rate change of a Poisson series with a geometrically dominated summand. -/
private lemma ckBethe_BV_rate {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) {g : ℕ → ℝ} {A c : ℝ}
    (hg : ∀ d, |g d| ≤ A * c ^ d) :
    |∑' d, poisPMF s d * g d - ∑' d, poisPMF r d * g d| ≤
      (s - r) * (2 * A * ∑' d : ℕ, (2 * (s + 1) * c) ^ d / d.factorial) := by
  have hs : 0 ≤ s := hr.trans hrs
  rw [← (ckBethe_pois_summable hs hg).tsum_sub (ckBethe_pois_summable hr hg)]
  have hX := Real.summable_pow_div_factorial (2 * (s + 1) * c)
  have key : ∀ d : ℕ, ‖poisPMF s d * g d - poisPMF r d * g d‖ ≤
      (s - r) * (2 * A) * ((2 * (s + 1) * c) ^ d / d.factorial) := by
    intro d
    rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
    calc |poisPMF s d - poisPMF r d| * |g d|
        ≤ ((s - r) * (2 * (2 * (s + 1)) ^ d / d.factorial)) * (A * c ^ d) :=
          mul_le_mul (ckBethe_pois_diff_le hr hrs d) (hg d) (abs_nonneg _)
            (mul_nonneg (by linarith) (by positivity))
      _ = (s - r) * (2 * A) * ((2 * (s + 1) * c) ^ d / d.factorial) := by
          rw [mul_pow, mul_pow, mul_pow]; ring
  have H := tsum_of_norm_bounded (hX.hasSum.mul_left ((s - r) * (2 * A))) key
  rw [Real.norm_eq_abs] at H
  calc _ ≤ (s - r) * (2 * A) * ∑' d : ℕ, (2 * (s + 1) * c) ^ d / d.factorial := H
    _ = _ := by ring

/-- Lemma 2.2, rate change: for some `C`, `|Ψ_s(ν) - Ψ_r(ν)| ≤ C (s - r)` for every finitely
supported law `ν` and all `0 ≤ r ≤ s`. -/
theorem ck_psi_rate {q : ℕ} {t : ℝ} (hp : CKPar q t) {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, ∀ (K : ℕ) (w : Fin K → ℝ) (μ : Fin K → Fin q → ℝ), ckFinLaw q w μ →
      ∀ r : ℝ, 0 ≤ r → r ≤ s → |ckPsi q t s w μ - ckPsi q t r w μ| ≤ C * (s - r) := by
  refine ⟨2 * (1 + ckEll q t) *
      ∑' d : ℕ, (2 * (s + 1) * (2 * ckMp t)) ^ d / d.factorial +
      (1 + ckEll q t) * (2 * ckMp t) / 2, ?_⟩
  intro K w μ h r hr hrs
  have hBV : |ckBV q t s w μ - ckBV q t r w μ| ≤
      (s - r) * (2 * (1 + ckEll q t) *
        ∑' d : ℕ, (2 * (s + 1) * (2 * ckMp t)) ^ d / d.factorial) :=
    ckBethe_BV_rate hr hrs (ckBethe_g_abs_le hp h)
  have hBE := ckBethe_BE_abs_le hp h
  have e1 : ckPsi q t s w μ - ckPsi q t r w μ =
      (ckBV q t s w μ - ckBV q t r w μ) - (s - r) / 2 * ckBE q t w μ := by
    unfold ckPsi; ring
  rw [e1]
  have hsr : 0 ≤ (s - r) / 2 := by linarith
  calc |(ckBV q t s w μ - ckBV q t r w μ) - (s - r) / 2 * ckBE q t w μ|
      ≤ |ckBV q t s w μ - ckBV q t r w μ| + |(s - r) / 2 * ckBE q t w μ| := abs_sub _ _
    _ ≤ (s - r) * (2 * (1 + ckEll q t) *
          ∑' d : ℕ, (2 * (s + 1) * (2 * ckMp t)) ^ d / d.factorial) +
          (s - r) / 2 * ((1 + ckEll q t) * (2 * ckMp t)) := by
        rw [abs_mul, abs_of_nonneg hsr]
        exact add_le_add hBV (mul_le_mul_of_nonneg_left hBE hsr)
    _ = _ := by ring

/-! ### One extra atom (Lemma 2.3) -/

/-- Split a sum over `y : Fin d → Fin (K+1)` into the tuples avoiding the new atom `0`
(the tuples `succ ∘ y₀`) and those hitting it. -/
private lemma ckBethe_sum_split {K d : ℕ} (Φ : (Fin d → Fin (K + 1)) → ℝ) :
    ∑ y, Φ y = ∑ y₀ : Fin d → Fin K, Φ (fun i => (y₀ i).succ) +
      ∑ y ∈ Finset.univ.filter (fun y : Fin d → Fin (K + 1) => ∃ i, y i = 0), Φ y := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun y : Fin d → Fin (K + 1) => ∃ i, y i = 0), add_comm]
  congr 1
  symm
  refine Finset.sum_nbij (fun y₀ i => (y₀ i).succ) ?_ ?_ ?_ ?_
  · intro y₀ _
    simp [Fin.succ_ne_zero]
  · intro y₁ _ y₂ _ h
    funext i
    exact Fin.succ_injective _ (congrFun h i)
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      not_exists] at hy
    refine ⟨fun i => (y i).pred (hy i), by simp, ?_⟩
    funext i
    simp
  · intro y₀ _
    rfl

/-- **Coupling bound.** Mixing a new atom of weight `α` into a law changes a `w^{⊗d}`-average of
a function bounded by `B` by at most `2 B (1 - (1-α)^d) ≤ 2 B d α`. -/
private lemma ckBethe_mix {K d : ℕ} {w : Fin K → ℝ} (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {w' : Fin (K + 1) → ℝ} (hw'0 : w' 0 = α)
    (hw'S : ∀ j, w' j.succ = (1 - α) * w j)
    (G : (Fin d → Fin (K + 1)) → ℝ) {B : ℝ} (hG : ∀ y, |G y| ≤ B) :
    |∑ y : Fin d → Fin (K + 1), (∏ i, w' (y i)) * G y -
      ∑ y : Fin d → Fin K, (∏ i, w (y i)) * G (fun i => (y i).succ)| ≤ 2 * B * (d * α) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hG fun _ => 0)
  have hw'nn : ∀ j, 0 ≤ w' j := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [hw'0]; exact hα0
    · rw [hw'S]; exact mul_nonneg (by linarith) (hw0 j)
  have hw'1 : ∑ j, w' j = 1 := by
    rw [Fin.sum_univ_succ, hw'0]
    simp_rw [hw'S]
    rw [← Finset.mul_sum, hw1]
    ring
  have havoid : ∀ y₀ : Fin d → Fin K, ∏ i, w' (y₀ i).succ = (1 - α) ^ d * ∏ i, w (y₀ i) := by
    intro y₀
    simp_rw [hw'S]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have htot : ∑ y : Fin d → Fin (K + 1), ∏ i, w' (y i) = 1 := by
    rw [← Fintype.sum_pow, hw'1, one_pow]
  have htot0 : ∑ y : Fin d → Fin K, ∏ i, w (y i) = 1 := by
    rw [← Fintype.sum_pow, hw1, one_pow]
  obtain ⟨T, hT⟩ : ∃ T, T = ∑ y : Fin d → Fin K, (∏ i, w (y i)) * G (fun i => (y i).succ) :=
    ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = Finset.univ.filter (fun y : Fin d → Fin (K + 1) => ∃ i, y i = 0) :=
    ⟨_, rfl⟩
  have hsplit : ∑ y : Fin d → Fin (K + 1), (∏ i, w' (y i)) * G y =
      (1 - α) ^ d * T + ∑ y ∈ S, (∏ i, w' (y i)) * G y := by
    rw [ckBethe_sum_split, hT, hS, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun y₀ _ => ?_
    rw [havoid]
    ring
  have hsplit1 : (1 : ℝ) = (1 - α) ^ d + ∑ y ∈ S, ∏ i, w' (y i) := by
    have h1 := ckBethe_sum_split (K := K) (d := d) (fun y => ∏ i, w' (y i))
    simp only [havoid] at h1
    rw [htot, ← Finset.mul_sum, htot0, mul_one] at h1
    rw [hS]
    exact h1
  have hTabs : |T| ≤ B := by
    rw [hT]
    exact ckBethe_wsum_abs_le hw0 hw1 (fun y => hG _)
  have hHabs : |∑ y ∈ S, (∏ i, w' (y i)) * G y| ≤ B * ∑ y ∈ S, ∏ i, w' (y i) := by
    calc |∑ y ∈ S, (∏ i, w' (y i)) * G y| ≤ ∑ y ∈ S, |(∏ i, w' (y i)) * G y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y ∈ S, (∏ i, w' (y i)) * B := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [abs_mul, abs_of_nonneg (Finset.prod_nonneg fun i _ => hw'nn (y i))]
          exact mul_le_mul_of_nonneg_left (hG y) (Finset.prod_nonneg fun i _ => hw'nn (y i))
      _ = B * ∑ y ∈ S, ∏ i, w' (y i) := by rw [← Finset.sum_mul, mul_comm]
  have hPval : ∑ y ∈ S, ∏ i, w' (y i) = 1 - (1 - α) ^ d := by linarith
  rw [hPval] at hHabs
  have hpow1 : (1 - α) ^ d ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hbern : 1 - (1 - α) ^ d ≤ d * α := by
    have h1 := one_add_mul_le_pow (a := -α) (by linarith) d
    rw [← sub_eq_add_neg] at h1
    nlinarith
  rw [hsplit, ← hT]
  set H := ∑ y ∈ S, (∏ i, w' (y i)) * G y with hH
  calc |(1 - α) ^ d * T + H - T| = |H - (1 - (1 - α) ^ d) * T| := by ring_nf
    _ ≤ |H| + |(1 - (1 - α) ^ d) * T| := abs_sub _ _
    _ ≤ B * (1 - (1 - α) ^ d) + (1 - (1 - α) ^ d) * B := by
        rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - (1 - α) ^ d)]
        exact add_le_add hHabs (mul_le_mul_of_nonneg_left hTabs (by linarith))
    _ = 2 * B * (1 - (1 - α) ^ d) := by ring
    _ ≤ 2 * B * (d * α) := mul_le_mul_of_nonneg_left hbern (by linarith)

/-- Summing the coupling bound against `Pois(r)`, uniformly in `0 ≤ r ≤ s`. -/
private lemma ckBethe_BV_mix {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) {g g' : ℕ → ℝ} {A c α : ℝ}
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hα : 0 ≤ α)
    (hg : ∀ d, |g d| ≤ A * c ^ d) (hg' : ∀ d, |g' d| ≤ A * c ^ d)
    (hgg : ∀ d : ℕ, |g' d - g d| ≤ 2 * (A * c ^ d) * (d * α)) :
    |∑' d, poisPMF r d * g' d - ∑' d, poisPMF r d * g d| ≤
      α * (2 * A * ∑' d : ℕ, (2 * s * c) ^ d / d.factorial) := by
  have hs : 0 ≤ s := hr.trans hrs
  rw [← (ckBethe_pois_summable hr hg').tsum_sub (ckBethe_pois_summable hr hg)]
  have hX := Real.summable_pow_div_factorial (2 * s * c)
  have key : ∀ d : ℕ, ‖poisPMF r d * g' d - poisPMF r d * g d‖ ≤
      α * (2 * A) * ((2 * s * c) ^ d / d.factorial) := by
    intro d
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (poisPMF_nonneg hr d)]
    have hf : (0 : ℝ) < d.factorial := by positivity
    have hP : poisPMF r d ≤ s ^ d / d.factorial := by
      unfold poisPMF
      rw [div_le_div_iff_of_pos_right hf]
      calc Real.exp (-r) * r ^ d ≤ 1 * s ^ d :=
            mul_le_mul (Real.exp_le_one_iff.mpr (by linarith)) (pow_le_pow_left₀ hr hrs d)
              (by positivity) zero_le_one
        _ = s ^ d := one_mul _
    have hd : (d : ℝ) ≤ 2 ^ d := by exact_mod_cast Nat.lt_two_pow_self.le
    have hgg' : |g' d - g d| ≤ 2 * (A * c ^ d) * (2 ^ d * α) :=
      (hgg d).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hd hα)
        (by positivity))
    calc poisPMF r d * |g' d - g d| ≤ (s ^ d / d.factorial) * (2 * (A * c ^ d) * (2 ^ d * α)) :=
          mul_le_mul hP hgg' (abs_nonneg _) (by positivity)
      _ = α * (2 * A) * ((2 * s * c) ^ d / d.factorial) := by
          rw [mul_pow, mul_pow]; ring
  have H := tsum_of_norm_bounded (hX.hasSum.mul_left (α * (2 * A))) key
  rw [Real.norm_eq_abs] at H
  calc _ ≤ α * (2 * A) * ∑' d : ℕ, (2 * s * c) ^ d / d.factorial := H
    _ = _ := by ring

/-- The mixed law `(1-α)ν + α δ_ζ` is again a finitely supported law on the simplex. -/
private lemma ckBethe_finLaw_cons {q K : ℕ} {w : Fin K → ℝ} {μ : Fin K → Fin q → ℝ}
    (h : ckFinLaw q w μ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {ζ : Fin q → ℝ}
    (hζ : ζ ∈ stdSimplex ℝ (Fin q))
    {w' : Fin (K + 1) → ℝ} (hw'0 : w' 0 = α) (hw'S : ∀ j, w' j.succ = (1 - α) * w j)
    {μ' : Fin (K + 1) → Fin q → ℝ} (hμ'0 : μ' 0 = ζ) (hμ'S : ∀ j, μ' j.succ = μ j) :
    ckFinLaw q w' μ' := by
  refine ⟨fun j => ?_, ?_, fun j => ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [hw'0]; exact hα0
    · rw [hw'S]; exact mul_nonneg (by linarith) (h.1 j)
  · rw [Fin.sum_univ_succ, hw'0]
    simp_rw [hw'S]
    rw [← Finset.mul_sum, h.2.1]
    ring
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [hμ'0]; exact hζ
    · rw [hμ'S]; exact h.2.2 j

/-- **Lemma 2.3, quantitative core.** Replacing `ν` by `(1-α)ν + α δ_ζ` changes `Ψ_r` by at most
`C_mf α`, uniformly in `0 ≤ r ≤ s`, with `C_mf = 2(1+ℓ₀) ∑_d (4 s m₊)^d/d! + 4 s (1+ℓ₀) m₊`. -/
private lemma ckBethe_extra_atom {q : ℕ} {t : ℝ} (hp : CKPar q t) {s : ℝ}
    {K : ℕ} {w : Fin K → ℝ} {μ : Fin K → Fin q → ℝ} (h : ckFinLaw q w μ)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {ζ : Fin q → ℝ} (hζ : ζ ∈ stdSimplex ℝ (Fin q))
    {w' : Fin (K + 1) → ℝ} (hw'0 : w' 0 = α) (hw'S : ∀ j, w' j.succ = (1 - α) * w j)
    {μ' : Fin (K + 1) → Fin q → ℝ} (hμ'0 : μ' 0 = ζ) (hμ'S : ∀ j, μ' j.succ = μ j)
    {r : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    |ckPsi q t r w' μ' - ckPsi q t r w μ| ≤
      α * (2 * (1 + ckEll q t) * ∑' d : ℕ, (2 * s * (2 * ckMp t)) ^ d / d.factorial +
        2 * s * ((1 + ckEll q t) * (2 * ckMp t))) := by
  obtain ⟨-, -, hp1, -, -, hl0, -⟩ := ck_const_bounds hp
  have hA0 : (0 : ℝ) ≤ 1 + ckEll q t := by linarith
  have hc0 : (0 : ℝ) ≤ 2 * ckMp t := by linarith
  have hs : 0 ≤ s := hr.trans hrs
  have hw0 := h.1
  have hw1 := h.2.1
  have h' : ckFinLaw q w' μ' := ckBethe_finLaw_cons h hα0 hα1 hζ hw'0 hw'S hμ'0 hμ'S
  -- vertex part
  have hV : ∀ d : ℕ,
      |(∑ y : Fin d → Fin (K + 1), (∏ i, w' (y i)) * ckLam (betheV q t fun i => μ' (y i))) -
        ∑ y : Fin d → Fin K, (∏ i, w (y i)) * ckLam (betheV q t fun i => μ (y i))| ≤
        2 * ((1 + ckEll q t) * (2 * ckMp t) ^ d) * (d * α) := by
    intro d
    have := ckBethe_mix (d := d) hw0 hw1 hα0 hα1 hw'0 hw'S
      (fun y => ckLam (betheV q t fun i => μ' (y i)))
      (fun y => ckBethe_lamV_abs_le hp fun i => h'.2.2 (y i))
    simpa only [hμ'S] using this
  have hBV : |ckBV q t r w' μ' - ckBV q t r w μ| ≤
      α * (2 * (1 + ckEll q t) * ∑' d : ℕ, (2 * s * (2 * ckMp t)) ^ d / d.factorial) :=
    ckBethe_BV_mix hr hrs hA0 hc0 hα0 (ckBethe_g_abs_le hp h) (ckBethe_g_abs_le hp h') hV
  -- edge part
  have hE : |ckBE q t w' μ' - ckBE q t w μ| ≤
      2 * ((1 + ckEll q t) * (2 * ckMp t)) * ((2 : ℕ) * α) := by
    rw [ckBethe_BE_eq, ckBethe_BE_eq]
    have := ckBethe_mix (d := 2) hw0 hw1 hα0 hα1 hw'0 hw'S
      (fun y => ckLam (betheE q t (μ' (y 0)) (μ' (y 1))))
      (fun y => ckBethe_lamE_abs_le hp (h'.2.2 _) (h'.2.2 _))
    simpa only [hμ'S] using this
  have e1 : ckPsi q t r w' μ' - ckPsi q t r w μ =
      (ckBV q t r w' μ' - ckBV q t r w μ) - r / 2 * (ckBE q t w' μ' - ckBE q t w μ) := by
    unfold ckPsi; ring
  rw [e1]
  have hr2 : 0 ≤ r / 2 := by linarith
  calc |(ckBV q t r w' μ' - ckBV q t r w μ) - r / 2 * (ckBE q t w' μ' - ckBE q t w μ)|
      ≤ |ckBV q t r w' μ' - ckBV q t r w μ| + |r / 2 * (ckBE q t w' μ' - ckBE q t w μ)| :=
        abs_sub _ _
    _ ≤ α * (2 * (1 + ckEll q t) * ∑' d : ℕ, (2 * s * (2 * ckMp t)) ^ d / d.factorial) +
          s / 2 * (2 * ((1 + ckEll q t) * (2 * ckMp t)) * ((2 : ℕ) * α)) := by
        rw [abs_mul, abs_of_nonneg hr2]
        exact add_le_add hBV (mul_le_mul (by linarith) hE (abs_nonneg _) (by linarith))
    _ = _ := by push_cast; ring

/-- Lemma 2.3, mean fixing: for some `C`, every finitely supported law `ν` with mean `m̄` has a
finitely supported `ν' ∈ 𝒫_u` with one more atom such that `|Ψ_r(ν') - Ψ_r(ν)| ≤ C ‖m̄ - u‖₂`
for all `0 ≤ r ≤ s`. -/
theorem ck_mean_fix {q : ℕ} {t : ℝ} (hp : CKPar q t) {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, ∀ (K : ℕ) (w : Fin K → ℝ) (μ : Fin K → Fin q → ℝ), ckFinLaw q w μ →
      ∃ (w' : Fin (K + 1) → ℝ) (μ' : Fin (K + 1) → Fin q → ℝ), ckFinPu q w' μ' ∧
        ∀ r : ℝ, 0 ≤ r → r ≤ s → |ckPsi q t r w' μ' - ckPsi q t r w μ| ≤
          C * Real.sqrt (∑ a, (∑ j, w j * μ j a - (q : ℝ)⁻¹) ^ 2) := by
  obtain ⟨-, -, hp1, -, -, hl0, -⟩ := ck_const_bounds hp
  have hq : 0 < q := by have := hp.two_le; omega
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  obtain ⟨Cmf, hCmf⟩ : ∃ Cmf : ℝ, Cmf = 2 * (1 + ckEll q t) *
      ∑' d : ℕ, (2 * s * (2 * ckMp t)) ^ d / d.factorial +
        2 * s * ((1 + ckEll q t) * (2 * ckMp t)) := ⟨_, rfl⟩
  have hCmf0 : 0 ≤ Cmf := by
    have hE : 0 ≤ ∑' d : ℕ, (2 * s * (2 * ckMp t)) ^ d / d.factorial :=
      tsum_nonneg fun d => by positivity
    rw [hCmf]
    have hA0 : (0 : ℝ) ≤ 1 + ckEll q t := by linarith
    have hc0 : (0 : ℝ) ≤ 2 * ckMp t := by linarith
    positivity
  refine ⟨Cmf * q, fun K w μ h => ?_⟩
  -- the mean `m̄` and its distance `δ = ‖m̄ - u‖₂` to `u`
  obtain ⟨mb, hmb⟩ : ∃ mb : Fin q → ℝ, mb = fun a => ∑ j, w j * μ j a := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = Real.sqrt (∑ a, (∑ j, w j * μ j a - (q : ℝ)⁻¹) ^ 2) :=
    ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by rw [hδ]; exact Real.sqrt_nonneg _
  have hdev : ∀ a, |mb a - (q : ℝ)⁻¹| ≤ δ := by
    intro a
    rw [hδ, hmb]
    apply Real.abs_le_sqrt
    exact Finset.single_le_sum (f := fun b => (∑ j, w j * μ j b - (q : ℝ)⁻¹) ^ 2)
      (fun b _ => sq_nonneg _) (Finset.mem_univ a)
  have hmb1 : ∑ a, mb a = 1 := by
    rw [hmb, Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [← h.2.1]
    exact Finset.sum_congr rfl fun j _ => by rw [(h.2.2 j).2, mul_one]
  -- the weight `α` of the new atom
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = min 1 ((q : ℝ) * δ) := ⟨_, rfl⟩
  have hα0 : 0 ≤ α := by rw [hαdef]; exact le_min zero_le_one (mul_nonneg hq'.le hδ0)
  have hα1 : α ≤ 1 := by rw [hαdef]; exact min_le_left _ _
  have hαδ : α ≤ q * δ := by rw [hαdef]; exact min_le_right _ _
  have hαcase : α = 1 ∨ α = q * δ := by rw [hαdef]; exact min_choice _ _
  -- the new atom `ζ = (u - (1-α) m̄) / α`
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : Fin q → ℝ, ζ = fun a =>
      if α = 0 then (q : ℝ)⁻¹ else ((q : ℝ)⁻¹ - (1 - α) * mb a) / α := ⟨_, rfl⟩
  have hmean : ∀ a, α * ζ a + (1 - α) * mb a = (q : ℝ)⁻¹ := by
    intro a
    by_cases hα : α = 0
    · have hqδ : (q : ℝ) * δ = 0 := by
        rcases hαcase with h1 | h1
        · rw [hα] at h1; norm_num at h1
        · rw [← h1, hα]
      have hδz : δ = 0 := by
        rcases mul_eq_zero.mp hqδ with h1 | h1
        · exact absurd h1 hq'.ne'
        · exact h1
      have h2 := hdev a
      rw [hδz] at h2
      have h3 : mb a - (q : ℝ)⁻¹ = 0 := abs_nonpos_iff.mp h2
      rw [hα]
      linarith
    · rw [hζdef]
      simp only [if_neg hα]
      rw [mul_div_cancel₀ _ hα]
      ring
  have hζ : ζ ∈ stdSimplex ℝ (Fin q) := by
    by_cases hα : α = 0
    · have hζc : ζ = fun _ => (q : ℝ)⁻¹ := by rw [hζdef]; simp only [if_pos hα]
      rw [hζc]
      refine ⟨fun _ => inv_nonneg.mpr hq'.le, ?_⟩
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_inv_cancel₀ hq'.ne']
    · have hαpos : 0 < α := lt_of_le_of_ne hα0 (Ne.symm hα)
      have hζc : ζ = fun a => ((q : ℝ)⁻¹ - (1 - α) * mb a) / α := by
        rw [hζdef]; simp only [if_neg hα]
      rw [hζc]
      refine ⟨fun a => ?_, ?_⟩
      · refine div_nonneg ?_ hα0
        rcases hαcase with h1 | h1
        · rw [h1, sub_self, zero_mul, sub_zero]
          exact inv_nonneg.mpr hq'.le
        · have hb : mb a ≤ (q : ℝ)⁻¹ + δ := by
            linarith [(abs_le.mp (hdev a)).2]
          have hδ' : δ = α * (q : ℝ)⁻¹ := by
            rw [h1]; field_simp
          have h2 : (1 - α) * mb a ≤ (1 - α) * ((q : ℝ)⁻¹ + δ) :=
            mul_le_mul_of_nonneg_left hb (by linarith)
          have h3 : (1 - α) * ((q : ℝ)⁻¹ + δ) = (q : ℝ)⁻¹ - α ^ 2 * (q : ℝ)⁻¹ := by
            rw [hδ']; ring
          have h4 : 0 ≤ α ^ 2 * (q : ℝ)⁻¹ := mul_nonneg (sq_nonneg α) (inv_nonneg.mpr hq'.le)
          linarith
      · rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hmb1,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_inv_cancel₀ hq'.ne', mul_one, sub_sub_cancel, div_self hα]
  refine ⟨Fin.cons α (fun j => (1 - α) * w j), Fin.cons ζ μ, ⟨?_, ?_⟩, ?_⟩
  · exact ckBethe_finLaw_cons h hα0 hα1 hζ (by simp) (fun j => by simp) (by simp)
      (fun j => by simp)
  · intro a
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hmean a, hmb]
    simp only [Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  · intro r hr hrs
    have H := ckBethe_extra_atom hp h hα0 hα1 hζ
      (w' := Fin.cons α (fun j => (1 - α) * w j)) (μ' := Fin.cons ζ μ)
      (by simp) (fun j => by simp) (by simp) (fun j => by simp) hr hrs
    rw [← hδ]
    calc _ ≤ α * Cmf := by rw [hCmf]; exact H
      _ ≤ (q * δ) * Cmf := mul_le_mul_of_nonneg_right hαδ hCmf0
      _ = Cmf * q * δ := by ring

end

end ERZeroFreeness
