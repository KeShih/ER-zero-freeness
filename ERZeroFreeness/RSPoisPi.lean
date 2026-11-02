/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSDefs
import ERZeroFreeness.Poisson

/-!
# Appendix C: product Poisson laws (infrastructure)

Facts about the product Poisson mass function `poisPi lam` on `ι → ℕ` (`ι` any finite type; the
ordered Poisson multigraphs of Appendix C are the case `ι = Fin n × Fin n`) used throughout
Appendix C:

* `rs_hasSum_poisPi_mul_prod`: `E ∏_i φ_i(N_i) = ∏_i E φ_i(N_i)` for nonnegative `φ_i`
  (product of series: the case `ι = Fin r`, `RSPoisPiAux.hasSum_fin_pi_prod`, transported along
  `Fintype.equivFin`);
* `rs_hasSum_poisPi`: total mass one;
* `rs_poisPi_mul_prod_pow`: the pointwise Poisson tilt
  `P_lam(N) ∏ y_i^{N_i} = exp(∑ lam_i (y_i - 1)) P_{lam·y}(N)`, which yields every tilting identity
  of `app:rs-poisson` without integrability side conditions;
* `rs_hasSum_poisPi_mul_prod_pow_complex`: the complex generating function
  `E ∏ y_i^{N_i} = exp(∑ lam_i (y_i - 1))` (`eq:rs-two-tilt`);
* `rs_summable_poisPi_of_abs_le`: the single domination lemma (`|f(N)| ≤ A c^{∑ N_i}` gives
  summability) which makes every expectation of Appendix C a genuine sum;
* `rs_hasSum_poisPi_superpose`: superposition, `N ∼ P_a`, `N' ∼ P_b` independent ⇒
  `N + N' ∼ P_{a+b}` (used in Lemma C.7, Step 3);
* the elementary expectation API for `poisPiExp` and `cpExp`.

## Proofs

Product of series: induction on `Fin r` with `Fin.consEquiv`, `HasSum.mul`,
`Summable.mul_of_nonneg` (real) / `summable_mul_of_summable_norm` (complex); transport along
`Fintype.equivFin ι` with `Equiv.arrowCongr` and `Equiv.hasSum_iff`.  One-dimensional generating
function: `NormedSpace.expSeries_div_hasSum_exp` with `Real.exp_eq_exp_ℝ` / `Complex.exp_eq_exp_ℂ`.
Superposition: the one-dimensional convolution
`∑_{i+j=k} Pois(α)(i) Pois(β)(j) = Pois(α+β)(k)` (`add_pow`), the fibre
`{(N,N') : N + N' = M} = ∏_i antidiagonal(M_i)` (`Finset.prod_univ_sum`), and regrouping a
nonnegative family along `Equiv.sigmaFiberEquiv` (`HasSum.sigma_of_hasSum`,
`summable_sigma_of_nonneg`).
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

namespace RSPoisPiAux

/-- Product of nonnegative series indexed by `Fin r`:
`∑_{x : Fin r → ℕ} ∏_i F_i(x_i) = ∏_i ∑_k F_i(k)`. -/
theorem hasSum_fin_pi_prod {r : ℕ} (F : Fin r → ℕ → ℝ) (hF : ∀ i k, 0 ≤ F i k)
    (s : Fin r → ℝ) (h : ∀ i, HasSum (F i) (s i)) :
    HasSum (fun x : Fin r → ℕ => ∏ i, F i (x i)) (∏ i, s i) := by
  induction r with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact hasSum_unique (fun _ : Fin 0 → ℕ => (1 : ℝ))
  | succ r ih =>
    have h0 := h 0
    have ht := ih (fun i => F i.succ) (fun i k => hF i.succ k) (fun i => s i.succ)
      (fun i => h i.succ)
    have hsumm : Summable fun p : ℕ × (Fin r → ℕ) => F 0 p.1 * ∏ i : Fin r, F i.succ (p.2 i) :=
      Summable.mul_of_nonneg (f := F 0) (g := fun x : Fin r → ℕ => ∏ i : Fin r, F i.succ (x i))
        h0.summable ht.summable (fun k => hF 0 k)
        (fun x => Finset.prod_nonneg fun i _ => hF i.succ (x i))
    have hmul := h0.mul ht hsumm
    have hfun : (fun x : Fin (r + 1) → ℕ => ∏ i, F i (x i)) ∘ (Fin.consEquiv (fun _ => ℕ)) =
        fun p : ℕ × (Fin r → ℕ) => F 0 p.1 * ∏ i : Fin r, F i.succ (p.2 i) := by
      funext ⟨k, y⟩
      simp [Fin.consEquiv_apply, Fin.prod_univ_succ]
    have hcomp : HasSum ((fun x : Fin (r + 1) → ℕ => ∏ i, F i (x i)) ∘
        (Fin.consEquiv (fun _ => ℕ))) (∏ i, s i) := by
      rw [hfun, Fin.prod_univ_succ]
      exact hmul
    exact (Fin.consEquiv (fun _ => ℕ)).hasSum_iff.mp hcomp

/-- `hasSum_fin_pi_prod` for an arbitrary finite index type. -/
theorem hasSum_fintype_pi_prod {ι : Type*} [Fintype ι] (F : ι → ℕ → ℝ)
    (hF : ∀ i k, 0 ≤ F i k) (s : ι → ℝ) (h : ∀ i, HasSum (F i) (s i)) :
    HasSum (fun x : ι → ℕ => ∏ i, F i (x i)) (∏ i, s i) := by
  let e := Fintype.equivFin ι
  have H := hasSum_fin_pi_prod (fun j => F (e.symm j)) (fun j k => hF _ k)
    (fun j => s (e.symm j)) (fun j => h _)
  have hs : ∏ j, s (e.symm j) = ∏ i, s i := Fintype.prod_equiv e.symm _ _ (fun _ => rfl)
  rw [hs] at H
  let E : (ι → ℕ) ≃ (Fin (Fintype.card ι) → ℕ) := e.arrowCongr (Equiv.refl ℕ)
  rw [← E.hasSum_iff] at H
  convert H using 1
  funext x
  simp only [Function.comp, E, Equiv.arrowCongr_apply, Equiv.refl_apply]
  exact Fintype.prod_equiv e _ _ (fun i => by simp)

/-- The generating function of `Pois(lam)`: `∑_k Pois(lam)(k) y^k = exp(lam (y - 1))`. -/
theorem hasSum_poisPMF_mul_pow {lam : ℝ} (y : ℝ) :
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

/-- Complex version of `hasSum_fin_pi_prod`, for absolutely summable factors. -/
theorem hasSum_fin_pi_prod_complex {r : ℕ} (F : Fin r → ℕ → ℂ)
    (hF : ∀ i, Summable fun k => ‖F i k‖) (s : Fin r → ℂ) (h : ∀ i, HasSum (F i) (s i)) :
    HasSum (fun x : Fin r → ℕ => ∏ i, F i (x i)) (∏ i, s i) := by
  induction r with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact hasSum_unique (fun _ : Fin 0 → ℕ => (1 : ℂ))
  | succ r ih =>
    have h0 := h 0
    have ht := ih (fun i => F i.succ) (fun i => hF i.succ) (fun i => s i.succ)
      (fun i => h i.succ)
    have htn : Summable fun x : Fin r → ℕ => ‖∏ i : Fin r, F i.succ (x i)‖ := by
      have := hasSum_fin_pi_prod (fun i k => ‖F i.succ k‖) (fun i k => norm_nonneg _)
        (fun i => ∑' k, ‖F i.succ k‖) (fun i => (hF i.succ).hasSum)
      simpa [norm_prod] using this.summable
    have hsumm : Summable fun p : ℕ × (Fin r → ℕ) => F 0 p.1 * ∏ i : Fin r, F i.succ (p.2 i) :=
      summable_mul_of_summable_norm (R := ℂ) (f := F 0)
        (g := fun x : Fin r → ℕ => ∏ i : Fin r, F i.succ (x i)) (hF 0) htn
    have hmul := h0.mul ht hsumm
    have hfun : (fun x : Fin (r + 1) → ℕ => ∏ i, F i (x i)) ∘ (Fin.consEquiv (fun _ => ℕ)) =
        fun p : ℕ × (Fin r → ℕ) => F 0 p.1 * ∏ i : Fin r, F i.succ (p.2 i) := by
      funext ⟨k, y⟩
      simp [Fin.consEquiv_apply, Fin.prod_univ_succ]
    have hcomp : HasSum ((fun x : Fin (r + 1) → ℕ => ∏ i, F i (x i)) ∘
        (Fin.consEquiv (fun _ => ℕ))) (∏ i, s i) := by
      rw [hfun, Fin.prod_univ_succ]
      exact hmul
    exact (Fin.consEquiv (fun _ => ℕ)).hasSum_iff.mp hcomp

/-- `hasSum_fin_pi_prod_complex` for an arbitrary finite index type. -/
theorem hasSum_fintype_pi_prod_complex {ι : Type*} [Fintype ι] (F : ι → ℕ → ℂ)
    (hF : ∀ i, Summable fun k => ‖F i k‖) (s : ι → ℂ) (h : ∀ i, HasSum (F i) (s i)) :
    HasSum (fun x : ι → ℕ => ∏ i, F i (x i)) (∏ i, s i) := by
  let e := Fintype.equivFin ι
  have H := hasSum_fin_pi_prod_complex (fun j => F (e.symm j)) (fun j => hF _)
    (fun j => s (e.symm j)) (fun j => h _)
  have hs : ∏ j, s (e.symm j) = ∏ i, s i := Fintype.prod_equiv e.symm _ _ (fun _ => rfl)
  rw [hs] at H
  let E : (ι → ℕ) ≃ (Fin (Fintype.card ι) → ℕ) := e.arrowCongr (Equiv.refl ℕ)
  rw [← E.hasSum_iff] at H
  convert H using 1
  funext x
  simp only [Function.comp, E, Equiv.arrowCongr_apply, Equiv.refl_apply]
  exact Fintype.prod_equiv e _ _ (fun i => by simp)

/-- One-dimensional Poisson convolution: `Pois(α) * Pois(β) = Pois(α + β)` (`add_pow`). -/
theorem poisPMF_add_conv (a b : ℝ) (m : ℕ) :
    poisPMF (a + b) m =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, poisPMF a x.1 * poisPMF b x.2 := by
  unfold poisPMF
  rw [(Commute.all a b).add_pow' m, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  subst hx
  rw [nsmul_eq_mul, Nat.cast_add_choose, neg_add, Real.exp_add]
  field_simp

/-- The fibre `{(N, N') : N + N' = M}` of addition, identified with the tuples of antidiagonal
pairs `∏_i antidiagonal(M_i)` (via `Equiv.arrowProdEquivProdArrow`). -/
def addFiberEquiv {ι : Type*} [Fintype ι] (M : ι → ℕ) :
    ↥((Fintype.piFinset fun i => Finset.HasAntidiagonal.antidiagonal (M i) :
      Finset (ι → ℕ × ℕ)) : Set (ι → ℕ × ℕ)) ≃ {z : (ι → ℕ) × (ι → ℕ) // z.1 + z.2 = M} :=
  (Equiv.arrowProdEquivProdArrow ι (fun _ => ℕ) (fun _ => ℕ)).subtypeEquiv fun x => by
    simp [funext_iff, Finset.HasAntidiagonal.mem_antidiagonal]

/-- Product Poisson convolution, as a finite sum over the fibre of addition. -/
theorem poisPi_add_eq_sum {ι : Type*} [Fintype ι] (a b : ι → ℝ) (M : ι → ℕ) :
    poisPi (a + b) M =
      ∑ x ∈ Fintype.piFinset (fun i => Finset.HasAntidiagonal.antidiagonal (M i)),
        poisPi a (fun i => (x i).1) * poisPi b (fun i => (x i).2) := by
  unfold poisPi
  simp_rw [Pi.add_apply, poisPMF_add_conv, Finset.prod_univ_sum, ← Finset.prod_mul_distrib]

end RSPoisPiAux

open RSPoisPiAux

theorem rs_poisPi_nonneg {ι : Type*} [Fintype ι] {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (N : ι → ℕ) : 0 ≤ poisPi lam N :=
  Finset.prod_nonneg fun i _ => poisPMF_nonneg (hlam i) (N i)

/-- `E_{P_lam} ∏_i φ_i(N_i) = ∏_i E φ_i(N_i)` for nonnegative `φ_i` (independence). -/
theorem rs_hasSum_poisPi_mul_prod {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (φ : ι → ℕ → ℝ) (hφ : ∀ i k, 0 ≤ φ i k) (s : ι → ℝ)
    (hs : ∀ i, HasSum (fun k => poisPMF (lam i) k * φ i k) (s i)) :
    HasSum (fun N : ι → ℕ => poisPi lam N * ∏ i, φ i (N i)) (∏ i, s i) := by
  have H := hasSum_fintype_pi_prod (fun i k => poisPMF (lam i) k * φ i k)
    (fun i k => mul_nonneg (poisPMF_nonneg (hlam i) k) (hφ i k)) s hs
  refine H.congr_fun fun N => ?_
  simp only [poisPi, Finset.prod_mul_distrib]

/-- The product Poisson law has total mass one. -/
theorem rs_hasSum_poisPi {ι : Type*} [Fintype ι] {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) :
    HasSum (poisPi lam) 1 := by
  have H := hasSum_fintype_pi_prod (fun i k => poisPMF (lam i) k)
    (fun i k => poisPMF_nonneg (hlam i) k) (fun _ => 1) (fun i => hasSum_poisPMF (hlam i))
  rw [Finset.prod_const_one] at H
  exact H

/-- **Pointwise Poisson tilt.** `P_lam(N) ∏_i y_i^{N_i} = exp(∑_i lam_i (y_i - 1)) P_{lam·y}(N)`
(no sign conditions). -/
theorem rs_poisPi_mul_prod_pow {ι : Type*} [Fintype ι] (lam y : ι → ℝ) (N : ι → ℕ) :
    poisPi lam N * ∏ i, y i ^ N i =
      Real.exp (∑ i, lam i * (y i - 1)) * poisPi (fun i => lam i * y i) N := by
  have h1 : ∀ (l w : ℝ) (k : ℕ),
      poisPMF l k * w ^ k = Real.exp (l * (w - 1)) * poisPMF (l * w) k := by
    intro l w k
    unfold poisPMF
    have h : Real.exp (-l) = Real.exp (l * (w - 1)) * Real.exp (-(l * w)) := by
      rw [← Real.exp_add]; ring_nf
    rw [h, mul_pow]; ring
  unfold poisPi
  rw [← Finset.prod_mul_distrib, Real.exp_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => h1 _ _ _

/-- **Complex generating function** of the product Poisson law:
`E ∏_i y_i^{N_i} = exp(∑_i lam_i (y_i - 1))` for every `y : ι → ℂ` (absolutely convergent). -/
theorem rs_hasSum_poisPi_mul_prod_pow_complex {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (y : ι → ℂ) :
    HasSum (fun N : ι → ℕ => (poisPi lam N : ℂ) * ∏ i, y i ^ N i)
      (Complex.exp (∑ i, (lam i : ℂ) * (y i - 1))) := by
  set F : ι → ℕ → ℂ := fun i k => (poisPMF (lam i) k : ℂ) * y i ^ k with hFdef
  have hF1 : ∀ i, HasSum (F i) (Complex.exp ((lam i : ℂ) * (y i - 1))) := by
    intro i
    have hexp := NormedSpace.expSeries_div_hasSum_exp ((lam i : ℂ) * y i)
    rw [← Complex.exp_eq_exp_ℂ] at hexp
    have := hexp.mul_left (Complex.exp (-(lam i : ℂ)))
    have hval : Complex.exp ((lam i : ℂ) * (y i - 1)) =
        Complex.exp (-(lam i : ℂ)) * Complex.exp ((lam i : ℂ) * y i) := by
      rw [← Complex.exp_add]; ring_nf
    rw [hval]
    refine this.congr_fun fun k => ?_
    simp only [hFdef, poisPMF]; push_cast; ring
  have hF2 : ∀ i, Summable fun k => ‖F i k‖ := by
    intro i
    have hs := (hasSum_poisPMF_mul_pow (lam := lam i) ‖y i‖).summable
    refine hs.congr fun k => ?_
    simp only [F, norm_mul, Complex.norm_real, norm_pow, Real.norm_eq_abs,
      abs_of_nonneg (poisPMF_nonneg (hlam i) k)]
  have H := hasSum_fintype_pi_prod_complex F hF2 _ hF1
  rw [← Complex.exp_sum] at H
  refine H.congr_fun fun N => ?_
  simp only [hFdef, poisPi, Complex.ofReal_prod, Finset.prod_mul_distrib]

/-- **Domination.** If `|f N| ≤ A c^{∑_i N_i}` with `c ≥ 0`, then `N ↦ P_lam(N) f(N)` is summable.
-/
theorem rs_summable_poisPi_of_abs_le {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) {f : (ι → ℕ) → ℝ} {A c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ N, |f N| ≤ A * c ^ (∑ i, N i)) :
    Summable (fun N => poisPi lam N * f N) := by
  have H := rs_hasSum_poisPi_mul_prod hlam (fun _ k => c ^ k) (fun _ k => pow_nonneg hc k)
    (fun i => Real.exp (lam i * (c - 1))) (fun i => hasSum_poisPMF_mul_pow c)
  refine Summable.of_norm_bounded (H.summable.mul_left A) fun N => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rs_poisPi_nonneg hlam N),
    Finset.prod_pow_eq_pow_sum]
  calc poisPi lam N * |f N| ≤ poisPi lam N * (A * c ^ (∑ i, N i)) :=
        mul_le_mul_of_nonneg_left (hf N) (rs_poisPi_nonneg hlam N)
    _ = A * (poisPi lam N * c ^ (∑ i, N i)) := by ring

/-- **Superposition.** If `N ∼ P_a` and `N' ∼ P_b` are independent, then `N + N' ∼ P_{a+b}`:
for nonnegative `Φ`, `∑_{N,N'} P_a(N) P_b(N') Φ(N + N') = E_{P_{a+b}} Φ`. -/
theorem rs_hasSum_poisPi_superpose {ι : Type*} [Fintype ι] {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) {Φ : (ι → ℕ) → ℝ} (hΦ : ∀ N, 0 ≤ Φ N)
    (hs : Summable fun M => poisPi (a + b) M * Φ M) :
    HasSum (fun z : (ι → ℕ) × (ι → ℕ) => poisPi a z.1 * poisPi b z.2 * Φ (z.1 + z.2))
      (∑' M, poisPi (a + b) M * Φ M) := by
  set F : (ι → ℕ) × (ι → ℕ) → ℝ := fun z => poisPi a z.1 * poisPi b z.2 * Φ (z.1 + z.2)
    with hFdef
  have hF0 : ∀ z, 0 ≤ F z := fun z =>
    mul_nonneg (mul_nonneg (rs_poisPi_nonneg ha _) (rs_poisPi_nonneg hb _)) (hΦ _)
  -- regroup along the fibres of `(N, N') ↦ N + N'`
  set e := Equiv.sigmaFiberEquiv (fun z : (ι → ℕ) × (ι → ℕ) => z.1 + z.2) with he
  -- each fibre is finite and carries mass `P_{a+b}(M) Φ(M)`
  have hfib : ∀ M : ι → ℕ, HasSum (fun c : {z : (ι → ℕ) × (ι → ℕ) // z.1 + z.2 = M} => F c.1)
      (poisPi (a + b) M * Φ M) := by
    intro M
    rw [← (addFiberEquiv M).hasSum_iff]
    have H := Finset.hasSum (Fintype.piFinset fun i => Finset.HasAntidiagonal.antidiagonal (M i))
      (fun x => poisPi a (fun i => (x i).1) * poisPi b (fun i => (x i).2) * Φ M)
    rw [← Finset.sum_mul, ← poisPi_add_eq_sum] at H
    refine H.congr_fun ?_
    rintro ⟨x, hx⟩
    have hx' : (fun i => (x i).1) + (fun i => (x i).2) = M := by
      have := ((addFiberEquiv M) ⟨x, hx⟩).2
      simpa [addFiberEquiv] using this
    simp only [Function.comp, addFiberEquiv, Equiv.subtypeEquiv_apply, hFdef,
      Equiv.arrowProdEquivProdArrow_apply]
    rw [hx']
  have hsumm : Summable (F ∘ e) := by
    refine (summable_sigma_of_nonneg (f := F ∘ e) (fun _ => hF0 _)).mpr
      ⟨fun M => (hfib M).summable, ?_⟩
    refine hs.congr fun M => ?_
    exact ((hfib M).tsum_eq).symm
  have H : HasSum (F ∘ e) (∑' M, poisPi (a + b) M * Φ M) :=
    HasSum.sigma_of_hasSum hs.hasSum (fun M => hfib M) hsumm
  exact e.hasSum_iff.mp H

/-! ### Expectation API -/

theorem rs_poisPiExp_const_mul {ι : Type*} [Fintype ι] (lam : ι → ℝ) (c : ℝ)
    (f : (ι → ℕ) → ℝ) : poisPiExp lam (fun N => c * f N) = c * poisPiExp lam f := by
  unfold poisPiExp
  rw [← tsum_mul_left]
  exact tsum_congr fun N => by ring

theorem rs_poisPiExp_add {ι : Type*} [Fintype ι] {lam : ι → ℝ} {f g : (ι → ℕ) → ℝ}
    (hf : Summable fun N => poisPi lam N * f N) (hg : Summable fun N => poisPi lam N * g N) :
    poisPiExp lam (fun N => f N + g N) = poisPiExp lam f + poisPiExp lam g := by
  unfold poisPiExp
  rw [← hf.tsum_add hg]
  exact tsum_congr fun N => by ring

theorem rs_poisPiExp_mono {ι : Type*} [Fintype ι] {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    {f g : (ι → ℕ) → ℝ} (hf : Summable fun N => poisPi lam N * f N)
    (hg : Summable fun N => poisPi lam N * g N) (hfg : ∀ N, f N ≤ g N) :
    poisPiExp lam f ≤ poisPiExp lam g :=
  Summable.tsum_le_tsum (fun N => mul_le_mul_of_nonneg_left (hfg N) (rs_poisPi_nonneg hlam N))
    hf hg

theorem rs_poisPiExp_const {ι : Type*} [Fintype ι] {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (c : ℝ) : poisPiExp lam (fun _ => c) = c := by
  unfold poisPiExp
  rw [tsum_mul_right, (rs_hasSum_poisPi hlam).tsum_eq, one_mul]

theorem rs_cpExp_mono {n : ℕ} {S : Type*} [Fintype S] {p : Fin n → S → ℝ}
    (hp0 : ∀ v a, 0 ≤ p v a) {K : S → S → ℝ} (hK0 : ∀ a b, 0 ≤ K a b)
    {F G : (Fin n → S) → RSGraph n → ℝ}
    (hF : ∀ ξ, Summable fun N => poisPi (cpMean K ξ) N * F ξ N)
    (hG : ∀ ξ, Summable fun N => poisPi (cpMean K ξ) N * G ξ N)
    (hFG : ∀ ξ N, F ξ N ≤ G ξ N) : cpExp p K F ≤ cpExp p K G := by
  unfold cpExp
  refine Finset.sum_le_sum fun ξ _ => mul_le_mul_of_nonneg_left ?_
    (Finset.prod_nonneg fun v _ => hp0 v (ξ v))
  have hm : ∀ e, 0 ≤ cpMean K ξ e := fun e => div_nonneg (hK0 _ _) (by positivity)
  exact rs_poisPiExp_mono hm (hF ξ) (hG ξ) (hFG ξ)

theorem rs_cpExp_const {n : ℕ} {S : Type*} [Fintype S] {p : Fin n → S → ℝ}
    (hp1 : ∀ v, ∑ a, p v a = 1) {K : S → S → ℝ} (hK0 : ∀ a b, 0 ≤ K a b) (c : ℝ) :
    cpExp p K (fun _ _ => c) = c := by
  unfold cpExp
  have hm : ∀ ξ : Fin n → S, ∀ e, 0 ≤ cpMean K ξ e :=
    fun ξ e => div_nonneg (hK0 _ _) (by positivity)
  simp_rw [rs_poisPiExp_const (hm _) c]
  rw [← Finset.sum_mul, ← Fintype.prod_sum (fun v a => p v a)]
  simp [hp1]

end

end ERZeroFreeness
