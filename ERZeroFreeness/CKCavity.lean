/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.CKDefs
import ERZeroFreeness.CKAnalysis
import ERZeroFreeness.CKPlanted
import ERZeroFreeness.CKEdge
import ERZeroFreeness.RSPoisPi
import ERZeroFreeness.RSModel
import ERZeroFreeness.RSBetheBasic
import ERZeroFreeness.RSPoisSplit
import ERZeroFreeness.Poisson

/-!
# Proof of [CKPZ, Prop. 3.6]: the cavity step (Lemmas 7.1, 7.2 and (7.1))

Part of the self-contained proof of `CKPZProp36 q`, the Potts case of the planted free-energy
bound of Coja-Oghlan, Krzakala, Perkins and Zdeborová [CKPZ, Prop. 3.6].  Appendix C is
formalized in two layers: the RS* modules prove Theorem C.1 from `CKPZProp36 q` as an explicit
hypothesis, and the CK* modules prove that hypothesis.  Lemma numbers refer to
`docs/ckpz-proof.md`, which gives the mathematics with every constant.

## Main statements

* `ck_cavity` (Lemma 7.1): adding a cavity vertex raises the pinned planted free energy `𝒦` by
  at most the expected vertex term `E_𝖰 Vert(post)`, at every rate `ϱ ≥ 0` and pin probability
  `π ∈ [0, 1]`.  Only the inequality is formalized; the equality case `π = 0` is not needed.
* `ck_step_decomp` (the step bound (7.1)): `a_{n+1}(k) - a_n(k)` is at most the expected vertex
  term minus the edge term, plus the pin cost `ks log q/(n+1)`.  Lemma 7.2 is used inside its
  proof and is not stated separately.

## Proof structure

The cavity vertex is `0 : Fin (n+1)`; the old vertices are `Fin.succ v`.

* (i) `ckcSplit : RSGraph (n+1) ≃ RSGraph n × ((Fin n → ℕ) × ((Fin n → ℕ) × ℕ))` (the old
  block, the counts `G_{vo}` and `G_{ov}`, and the loop count `G_{oo}`), `ckc_poisPi_split` and
  `ckc_L_split`; colourings split via `Fin.cons` (`ckc_sum_cons`), pins via `ckcUSplit`
  (`ckc_bern_marg`).
* (ii) `ckc_Ft_le` and `ckc_log_Ft_le`: `F̃(G⁺,U⁺,σ⁺) ≤ F̃(G,U,σ) X_{post}(D,N₀)`.
* (iii) `ckc_tsum_split` (with the superposition `ckc_superpose_loop`, from
  `ck_poisPi_superpose`) and `ckc_factor`: `𝖰_{n+1}` factorizes into `𝖰_n`, a uniform cavity
  colour and `P^{σ,c}`.
* (iv) `ckc_R_avg` and `ck_predictive` (Lemma 4.4(c)) turn `E log X` into `E Vert(post)`.
* Integrability uses `B = ϱ(2n+1) + (|D|+N₀)ℓ₀` in place of the `Γ` of Lemma 7.3:
  `ckc_X_mem` gives `X ∈ [e^{-B}, e^{B}]`, and `ckc_abs_vert_le` bounds `Vert` uniformly over
  probability vectors, via `|Λ(X)| ≤ e^{2B}`.

`ck_step_decomp` combines `ck_cavity` at rate `ϱ'' = s/(2(n+1))` with the two steps of
Lemma 7.2: `ck_pin_cost` (Lemma 4.6, with `π_x = 1 - e^{-ks/(n(n+1))}` and `n π_x ≤ ks/(n+1)`)
and `ck_edge_lower` (Lemma 5.3, with `β = s/(2n(n+1))`).
-/

open Filter Topology MeasureTheory

namespace ERZeroFreeness

open scoped Classical

noncomputable section


/-! ### Elementary facts about `M` -/

private lemma ckc_M_symm (q : ℕ) (t : ℝ) (a b : Fin q) : rsM q t a b = rsM q t b a := by
  unfold rsM rsA
  by_cases h : a = b
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

private lemma ckc_M_self (q : ℕ) (t : ℝ) (a : Fin q) : rsM q t a a = ckMm q t := by
  unfold rsM rsA ckMm
  simp

private lemma ckc_M_pos {q : ℕ} {t : ℝ} (hp : CKPar q t) (a b : Fin q) : 0 < rsM q t a b :=
  lt_of_lt_of_le (ck_const_bounds hp).1 (ck_rsM_mem hp a b).1

private lemma ckc_abs_M_sub_one {q : ℕ} {t : ℝ} (hp : CKPar q t) (a b : Fin q) :
    |rsM q t a b - 1| ≤ 1 := by
  have h1 := ck_rsM_mem hp a b
  have h2 := ck_const_bounds hp
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2.2.2.1]

private lemma ckc_q_pos {q : ℕ} {t : ℝ} (hp : CKPar q t) : (0 : ℝ) < q := by
  have := hp.two_le
  exact_mod_cast (by omega : 0 < q)

/-! ### Bounds on the cavity ratio `X` (Lemma 7.1, Integrability) -/

/-- The exponent bound `B = ϱ(2n+1) + m ℓ₀`, with `m = |D| + N₀`. -/
private def ckcBd (q : ℕ) (t ϱ : ℝ) (n m : ℕ) : ℝ := ϱ * (2 * n + 1) + m * ckEll q t

private lemma ckc_Bd_nonneg {q : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (n m : ℕ) :
    0 ≤ ckcBd q t ϱ n m := by
  have := (ck_const_bounds hp).2.2.2.2.2.1
  unfold ckcBd
  positivity

/-- One summand of `X`, written as a single exponential. -/
private lemma ckc_term_eq_exp {q n : ℕ} {t : ℝ} (hp : CKPar q t) (ϱ : ℝ)
    (τ : Fin n → Fin q) (c : Fin q) (D : Fin n → ℕ) (N0 : ℕ) :
    Real.exp (ϱ * (1 - ckMm q t)) * ckMm q t ^ N0 *
        (Real.exp (-(2 * ϱ) * ∑ v, (rsM q t (τ v) c - 1)) * ∏ v, rsM q t (τ v) c ^ D v) =
      Real.exp (ϱ * (1 - ckMm q t) + N0 * Real.log (ckMm q t) +
        -(2 * ϱ) * ∑ v, (rsM q t (τ v) c - 1) +
          ∑ v, (D v : ℝ) * Real.log (rsM q t (τ v) c)) := by
  have hm := (ck_const_bounds hp).1
  have hb : Real.exp ((N0 : ℝ) * Real.log (ckMm q t)) = ckMm q t ^ N0 := by
    rw [Real.exp_nat_mul, Real.exp_log hm]
  have hd : Real.exp (∑ v, (D v : ℝ) * Real.log (rsM q t (τ v) c)) =
      ∏ v, rsM q t (τ v) c ^ D v := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun v _ => by rw [Real.exp_nat_mul, Real.exp_log (ckc_M_pos hp _ _)]
  rw [Real.exp_add, Real.exp_add, Real.exp_add, hb, hd]
  ring

private lemma ckc_exponent_bound {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (τ : Fin n → Fin q) (c : Fin q) (D : Fin n → ℕ) (N0 : ℕ) :
    |ϱ * (1 - ckMm q t) + N0 * Real.log (ckMm q t) +
        -(2 * ϱ) * ∑ v, (rsM q t (τ v) c - 1) +
          ∑ v, (D v : ℝ) * Real.log (rsM q t (τ v) c)| ≤ ckcBd q t ϱ n (∑ v, D v + N0) := by
  have hc := ck_const_bounds hp
  have h1 : |ϱ * (1 - ckMm q t)| ≤ ϱ := by
    rw [abs_of_nonneg (mul_nonneg hϱ (by linarith [hc.2.1]))]
    nlinarith [hc.1]
  have h2 : |(N0 : ℝ) * Real.log (ckMm q t)| ≤ N0 * ckEll q t := by
    have : Real.log (ckMm q t) = -ckEll q t := by unfold ckEll; ring
    rw [this, abs_mul, abs_neg, abs_of_pos hc.2.2.2.2.2.1, Nat.abs_cast]
  have h3 : |-(2 * ϱ) * ∑ v, (rsM q t (τ v) c - 1)| ≤ 2 * ϱ * n := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ϱ)]
    have : |∑ v, (rsM q t (τ v) c - 1)| ≤ n := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ v, |rsM q t (τ v) c - 1| ≤ ∑ _v : Fin n, (1 : ℝ) :=
            Finset.sum_le_sum fun v _ => ckc_abs_M_sub_one hp _ _
        _ = n := by simp
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have h4 : |∑ v, (D v : ℝ) * Real.log (rsM q t (τ v) c)| ≤ (∑ v, (D v : ℝ)) * ckEll q t := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun v _ => ?_
    rw [abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left (ck_abs_log_rsM_le hp _ _) (Nat.cast_nonneg _)
  have h5 := abs_add_le (ϱ * (1 - ckMm q t) + N0 * Real.log (ckMm q t) +
        -(2 * ϱ) * ∑ v, (rsM q t (τ v) c - 1)) (∑ v, (D v : ℝ) * Real.log (rsM q t (τ v) c))
  have h6 := abs_add_le (ϱ * (1 - ckMm q t) + N0 * Real.log (ckMm q t))
        (-(2 * ϱ) * ∑ v, (rsM q t (τ v) c - 1))
  have h7 := abs_add_le (ϱ * (1 - ckMm q t)) (N0 * Real.log (ckMm q t))
  unfold ckcBd
  push_cast
  nlinarith

/-- `X_μ(D, N₀) ∈ [e^{-B}, e^{B}]` for every probability vector `μ`. -/
private lemma ckc_X_mem {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (D : Fin n → ℕ) (N0 : ℕ) :
    Real.exp (-ckcBd q t ϱ n (∑ v, D v + N0)) ≤ ckX q t ϱ μ D N0 ∧
      ckX q t ϱ μ D N0 ≤ Real.exp (ckcBd q t ϱ n (∑ v, D v + N0)) := by
  set B := ckcBd q t ϱ n (∑ v, D v + N0) with hB
  set K : (Fin n → Fin q) → Fin q → ℝ := fun τ c =>
    Real.exp (ϱ * (1 - ckMm q t)) * ckMm q t ^ N0 *
      (Real.exp (-(2 * ϱ) * ∑ v, (rsM q t (τ v) c - 1)) * ∏ v, rsM q t (τ v) c ^ D v) with hK
  have hKb : ∀ τ c, Real.exp (-B) ≤ K τ c ∧ K τ c ≤ Real.exp B := by
    intro τ c
    simp only [hK]
    rw [ckc_term_eq_exp hp ϱ τ c D N0]
    have := abs_le.mp (ckc_exponent_bound hp hϱ τ c D N0)
    exact ⟨Real.exp_le_exp.mpr this.1, Real.exp_le_exp.mpr this.2⟩
  have hX : ckX q t ϱ μ D N0 = (q : ℝ)⁻¹ * ∑ c : Fin q, ∑ τ, μ τ * K τ c := by
    unfold ckX
    simp only [hK, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun τ _ => ?_
    ring
  have hq := ckc_q_pos hp
  have hsum : ∀ y : ℝ, (q : ℝ)⁻¹ * ∑ _c : Fin q, ∑ τ, μ τ * y = y := by
    intro y
    rw [← Finset.sum_mul, hμ.2, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  rw [hX]
  constructor
  · exact le_trans (hsum _).ge (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ =>
      Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (hKb τ c).1 (hμ.1 τ))
      (by positivity))
  · exact le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ =>
      Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (hKb τ c).2 (hμ.1 τ))
      (by positivity)) (hsum _).le

private lemma ckc_X_pos {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (D : Fin n → ℕ) (N0 : ℕ) :
    0 < ckX q t ϱ μ D N0 :=
  lt_of_lt_of_le (Real.exp_pos _) (ckc_X_mem hp hϱ hμ D N0).1

private lemma ckc_abs_log_X_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (D : Fin n → ℕ) (N0 : ℕ) :
    |Real.log (ckX q t ϱ μ D N0)| ≤ ckcBd q t ϱ n (∑ v, D v + N0) := by
  have h := ckc_X_mem hp hϱ hμ D N0
  have hpos := ckc_X_pos hp hϱ hμ D N0
  rw [abs_le]
  constructor
  · have := Real.log_le_log (Real.exp_pos _) h.1
    rwa [Real.log_exp] at this
  · have := Real.log_le_log hpos h.2
    rwa [Real.log_exp] at this

/-- `|Λ(X)| ≤ e^{2B}`. -/
private lemma ckc_abs_lam_X_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (D : Fin n → ℕ) (N0 : ℕ) :
    |ckLam (ckX q t ϱ μ D N0)| ≤ Real.exp (2 * ckcBd q t ϱ n (∑ v, D v + N0)) := by
  have h := ckc_X_mem hp hϱ hμ D N0
  have hpos := ckc_X_pos hp hϱ hμ D N0
  have hl := ckc_abs_log_X_le hp hϱ hμ D N0
  set B := ckcBd q t ϱ n (∑ v, D v + N0)
  have hB : B ≤ Real.exp B := by linarith [Real.add_one_le_exp B]
  unfold ckLam
  rw [abs_mul, abs_of_pos hpos, two_mul, Real.exp_add]
  exact mul_le_mul h.2 (hl.trans hB) (abs_nonneg _) (Real.exp_pos _).le

/-! ### Poisson weights with geometric factors -/

private lemma ckc_hasSum_poisPi_pow {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) {y : ℝ} (hy : 0 ≤ y) :
    HasSum (fun N : ι → ℕ => poisPi lam N * y ^ (∑ i, N i))
      (Real.exp ((∑ i, lam i) * (y - 1))) := by
  have H := rs_hasSum_poisPi_mul_prod hlam (fun _ k => y ^ k) (fun _ k => pow_nonneg hy k)
    (fun i => Real.exp (lam i * (y - 1))) (fun i => RSPoisPiAux.hasSum_poisPMF_mul_pow y)
  rw [← Real.exp_sum, ← Finset.sum_mul] at H
  refine H.congr_fun fun N => ?_
  rw [Finset.prod_pow_eq_pow_sum]

private lemma ckc_poisPi_pow_nonneg {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) {y : ℝ} (hy : 0 ≤ y) (N : ι → ℕ) :
    0 ≤ poisPi lam N * y ^ (∑ i, N i) :=
  mul_nonneg (rs_poisPi_nonneg hlam N) (pow_nonneg hy _)

private lemma ckc_poisPMF_pow_nonneg {lam : ℝ} (hlam : 0 ≤ lam) {y : ℝ} (hy : 0 ≤ y) (k : ℕ) :
    0 ≤ poisPMF lam k * y ^ k :=
  mul_nonneg (poisPMF_nonneg hlam k) (pow_nonneg hy _)

/-- Product of two nonnegative `HasSum`s on a product type. -/
private lemma ckc_hasSum_prod {α β : Type*} {u : α → ℝ} {v : β → ℝ} {a b : ℝ}
    (hu : HasSum u a) (hv : HasSum v b) (hu0 : ∀ x, 0 ≤ u x) (hv0 : ∀ y, 0 ≤ v y) :
    HasSum (fun p : α × β => u p.1 * v p.2) (a * b) :=
  hu.mul hv (hu.summable.mul_of_nonneg hv.summable (fun x => hu0 x) (fun y => hv0 y))

/-- Domination by a product of nonnegative summable families gives summability. -/
private lemma ckc_summable_of_dom {α β : Type*} {f : α × β → ℝ} {u : α → ℝ} {v : β → ℝ}
    (hu : Summable u) (hv : Summable v) (hu0 : ∀ x, 0 ≤ u x) (hv0 : ∀ y, 0 ≤ v y)
    (hf : ∀ p, |f p| ≤ u p.1 * v p.2) : Summable f :=
  Summable.of_norm_bounded (hu.mul_of_nonneg hv (fun x => hu0 x) (fun y => hv0 y))
    (fun p => by rw [Real.norm_eq_abs]; exact hf p)

/-- The null cavity weights `P⁰(D, N₀) e^{2B}` have a finite sum. -/
private lemma ckc_hasSum_vert_dom {q n : ℕ} {t : ℝ} {ϱ : ℝ} (hϱ : 0 ≤ ϱ) :
    HasSum (fun z : (Fin n → ℕ) × ℕ => poisPi (fun _ => 2 * ϱ) z.1 * poisPMF ϱ z.2 *
        Real.exp (2 * ckcBd q t ϱ n (∑ v, z.1 v + z.2)))
      (Real.exp (2 * (ϱ * (2 * n + 1))) *
        (Real.exp ((∑ _v : Fin n, 2 * ϱ) * (Real.exp (2 * ckEll q t) - 1)) *
          Real.exp (ϱ * (Real.exp (2 * ckEll q t) - 1)))) := by
  set y := Real.exp (2 * ckEll q t)
  have hy : 0 ≤ y := (Real.exp_pos _).le
  have H := ckc_hasSum_prod (ckc_hasSum_poisPi_pow (fun _ => by positivity : ∀ _ : Fin n,
    0 ≤ 2 * ϱ) hy) (RSPoisPiAux.hasSum_poisPMF_mul_pow (lam := ϱ) y)
    (ckc_poisPi_pow_nonneg (fun _ => by positivity) hy) (ckc_poisPMF_pow_nonneg hϱ hy)
  have H2 := H.mul_left (Real.exp (2 * (ϱ * (2 * n + 1))))
  refine H2.congr_fun fun z => ?_
  unfold ckcBd
  have e1 : Real.exp (2 * (ϱ * (2 * n + 1) + ((∑ v, z.1 v + z.2 : ℕ) : ℝ) * ckEll q t)) =
      Real.exp (2 * (ϱ * (2 * n + 1))) * (y ^ (∑ v, z.1 v) * y ^ z.2) := by
    rw [← pow_add, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [e1]
  ring

/-- `Vert` is bounded uniformly over probability vectors (Lemma 7.1, Integrability). -/
private lemma ckc_abs_vert_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) :
    ∃ V : ℝ, ∀ μ : (Fin n → Fin q) → ℝ, IsPMF μ → |ckVert q t ϱ μ| ≤ V := by
  refine ⟨Real.exp (2 * (ϱ * (2 * n + 1))) *
        (Real.exp ((∑ _v : Fin n, 2 * ϱ) * (Real.exp (2 * ckEll q t) - 1)) *
          Real.exp (ϱ * (Real.exp (2 * ckEll q t) - 1))), fun μ hμ => ?_⟩
  unfold ckVert
  rw [← Real.norm_eq_abs]
  refine tsum_of_norm_bounded (ckc_hasSum_vert_dom (q := q) (t := t) hϱ) fun z => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (rs_poisPi_nonneg
    (fun _ => by positivity) _) (poisPMF_nonneg hϱ _))]
  exact mul_le_mul_of_nonneg_left (ckc_abs_lam_X_le hp hϱ hμ z.1 z.2)
    (mul_nonneg (rs_poisPi_nonneg (fun _ => by positivity) _) (poisPMF_nonneg hϱ _))

/-! ### Splitting off the cavity vertex `0` (Lemma 7.1(i)) -/

/-- The old block `G|_{V×V}` (old vertices are `Fin.succ v`, the cavity vertex is `0`). -/
private def ckcG {n : ℕ} (G : RSGraph (n + 1)) : RSGraph n := fun e => G (e.1.succ, e.2.succ)

/-- The counts `G_{vo}` of the edges from old vertices to the cavity vertex. -/
private def ckcA {n : ℕ} (G : RSGraph (n + 1)) : Fin n → ℕ := fun v => G (v.succ, 0)

/-- The counts `G_{ov}`. -/
private def ckcB {n : ℕ} (G : RSGraph (n + 1)) : Fin n → ℕ := fun v => G (0, v.succ)

/-- The loop count `G_{oo}`. -/
private def ckcN {n : ℕ} (G : RSGraph (n + 1)) : ℕ := G (0, 0)

/-- The old pins `U ∩ V`. -/
private def ckcU {n : ℕ} (U : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun v => v.succ ∈ U

/-- Reassemble a multigraph on `Fin (n+1)` from its four blocks. -/
private def ckcJoin {n : ℕ} (w : RSGraph n × ((Fin n → ℕ) × ((Fin n → ℕ) × ℕ))) :
    RSGraph (n + 1) := fun e =>
  (Fin.cons (α := fun _ => Fin (n + 1) → ℕ) (Fin.cons (α := fun _ => ℕ) w.2.2.2 w.2.2.1)
    (fun i => Fin.cons (α := fun _ => ℕ) (w.2.1 i) (fun j => w.1 (i, j)))) e.1 e.2

private def ckcSplit (n : ℕ) :
    RSGraph (n + 1) ≃ RSGraph n × ((Fin n → ℕ) × ((Fin n → ℕ) × ℕ)) where
  toFun G := (ckcG G, ckcA G, ckcB G, ckcN G)
  invFun := ckcJoin
  left_inv G := by
    funext e
    obtain ⟨i, j⟩ := e
    cases i using Fin.cases <;> cases j using Fin.cases <;> rfl
  right_inv w := by
    obtain ⟨G, a, b, N0⟩ := w
    rfl

private lemma ckc_prod_split {M : Type*} [CommMonoid M] {n : ℕ}
    (φ : Fin (n + 1) × Fin (n + 1) → M) :
    ∏ e, φ e = (∏ e : Fin n × Fin n, φ (e.1.succ, e.2.succ)) * (∏ v : Fin n, φ (v.succ, 0)) *
      (∏ v : Fin n, φ (0, v.succ)) * φ (0, 0) := by
  simp only [Fintype.prod_prod_type, Fin.prod_univ_succ, Finset.prod_mul_distrib]
  ac_rfl

private lemma ckc_sum_split {M : Type*} [AddCommMonoid M] {n : ℕ}
    (φ : Fin (n + 1) × Fin (n + 1) → M) :
    ∑ e, φ e = (∑ e : Fin n × Fin n, φ (e.1.succ, e.2.succ)) + (∑ v : Fin n, φ (v.succ, 0)) +
      (∑ v : Fin n, φ (0, v.succ)) + φ (0, 0) := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, Finset.sum_add_distrib]
  ac_rfl

private lemma ckc_rsEdges_split {n : ℕ} (G : RSGraph (n + 1)) :
    rsEdges G = rsEdges (ckcG G) + (∑ v, (ckcA G + ckcB G) v + ckcN G) := by
  unfold rsEdges
  rw [ckc_sum_split]
  simp only [Pi.add_apply, Finset.sum_add_distrib, ckcG, ckcA, ckcB, ckcN]
  ring

private lemma ckc_rsEdges_G_le {n : ℕ} (G : RSGraph (n + 1)) : rsEdges (ckcG G) ≤ rsEdges G := by
  rw [ckc_rsEdges_split G]
  omega

private lemma ckc_rsEdges_DN_le {n : ℕ} (G : RSGraph (n + 1)) :
    ∑ v, (ckcA G + ckcB G) v + ckcN G ≤ rsEdges G := by
  rw [ckc_rsEdges_split G]
  omega

private lemma ckc_poisPi_split {n : ℕ} (lam : Fin (n + 1) × Fin (n + 1) → ℝ) (G : RSGraph (n + 1)) :
    poisPi lam G = poisPi (fun e => lam (e.1.succ, e.2.succ)) (ckcG G) *
      poisPi (fun v => lam (v.succ, 0)) (ckcA G) * poisPi (fun v => lam (0, v.succ)) (ckcB G) *
        poisPMF (lam (0, 0)) (ckcN G) := by
  unfold poisPi
  exact ckc_prod_split _

/-- `L(G⁺, (c, τ)) = L(G, τ) e^{ϱ(1-m₋)} m₋^{N₀} e^{δ_c(τ)} ∏_v M(τ_v, c)^{D_v}`. -/
private lemma ckc_L_split {q n : ℕ} (t ϱ : ℝ) (G : RSGraph (n + 1)) (c : Fin q)
    (τ : Fin n → Fin q) :
    ckL q t ϱ G (Fin.cons c τ) = ckL q t ϱ (ckcG G) τ *
      (Real.exp (ϱ * (1 - ckMm q t)) * ckMm q t ^ ckcN G *
        (Real.exp (-(2 * ϱ) * ∑ v, (rsM q t (τ v) c - 1)) *
          ∏ v, rsM q t (τ v) c ^ (ckcA G + ckcB G) v)) := by
  have hS : ckS q t (Fin.cons c τ : Fin (n + 1) → Fin q) =
      ckS q t τ + 2 * ∑ v, (rsM q t (τ v) c - 1) + (ckMm q t - 1) := by
    unfold ckS
    rw [ckc_sum_split]
    simp only [Fin.cons_succ, Fin.cons_zero, ckc_M_self]
    have : ∑ v : Fin n, (rsM q t c (τ v) - 1) = ∑ v : Fin n, (rsM q t (τ v) c - 1) :=
      Finset.sum_congr rfl fun v _ => by rw [ckc_M_symm]
    rw [this]
    ring
  have hW : rsW q t G (Fin.cons c τ : Fin (n + 1) → Fin q) =
      rsW q t (ckcG G) τ * (ckMm q t ^ ckcN G * ∏ v, rsM q t (τ v) c ^ (ckcA G + ckcB G) v) := by
    unfold rsW
    rw [ckc_prod_split]
    simp only [Fin.cons_succ, Fin.cons_zero, ckc_M_self, Pi.add_apply, pow_add,
      Finset.prod_mul_distrib, ckcG, ckcA, ckcB, ckcN]
    have : ∏ v : Fin n, rsM q t c (τ v) ^ G (0, v.succ) =
        ∏ v : Fin n, rsM q t (τ v) c ^ G (0, v.succ) :=
      Finset.prod_congr rfl fun v _ => by rw [ckc_M_symm]
    rw [this]
    ring
  unfold ckL
  rw [hS, hW]
  have he : -(ϱ * (ckS q t τ + 2 * ∑ v, (rsM q t (τ v) c - 1) + (ckMm q t - 1))) =
      -(ϱ * ckS q t τ) + ϱ * (1 - ckMm q t) + -(2 * ϱ) * ∑ v, (rsM q t (τ v) c - 1) := by ring
  rw [he, Real.exp_add, Real.exp_add]
  ring

/-- Sum over colourings of `Fin (n+1)`: the cavity colour first. -/
private lemma ckc_sum_cons {q n : ℕ} (F : (Fin (n + 1) → Fin q) → ℝ) :
    ∑ σ, F σ = ∑ c : Fin q, ∑ σ : Fin n → Fin q, F (Fin.cons c σ) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin q) _ _ (fun p => rfl)).symm

/-- The pin set on `Fin (n+1)` with old pins `p.1`; it contains the cavity vertex iff `p.2`. -/
private def ckcUJoin {n : ℕ} (p : Finset (Fin n) × Bool) : Finset (Fin (n + 1)) :=
  if p.2 then insert 0 (p.1.map (Fin.succEmb n)) else p.1.map (Fin.succEmb n)

private lemma ckc_mem_UJoin_zero {n : ℕ} (p : Finset (Fin n) × Bool) :
    (0 : Fin (n + 1)) ∈ ckcUJoin p ↔ p.2 = true := by
  obtain ⟨U, b⟩ := p
  cases b <;> simp [ckcUJoin, Fin.succ_ne_zero]

private lemma ckc_mem_UJoin_succ {n : ℕ} (p : Finset (Fin n) × Bool) (v : Fin n) :
    v.succ ∈ ckcUJoin p ↔ v ∈ p.1 := by
  obtain ⟨U, b⟩ := p
  cases b <;> simp [ckcUJoin, (Fin.succ_ne_zero v)]

private def ckcUSplit (n : ℕ) : Finset (Fin (n + 1)) ≃ Finset (Fin n) × Bool where
  toFun U := (ckcU U, decide ((0 : Fin (n + 1)) ∈ U))
  invFun := ckcUJoin
  left_inv U := by
    ext x
    cases x using Fin.cases with
    | zero => simp [ckc_mem_UJoin_zero]
    | succ v => simp [ckc_mem_UJoin_succ, ckcU]
  right_inv p := by
    obtain ⟨U, b⟩ := p
    refine Prod.ext ?_ ?_
    · ext v
      simp [ckcU, ckc_mem_UJoin_succ]
    · simp only
      cases b <;> simp [ckc_mem_UJoin_zero]

private lemma ckc_bern_succ {n : ℕ} (π : ℝ) (U : Finset (Fin (n + 1))) :
    ckBern π U = (if (0 : Fin (n + 1)) ∈ U then π else 1 - π) * ckBern π (ckcU U) := by
  unfold ckBern
  rw [Fin.prod_univ_succ]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  simp [ckcU]

/-- Marginalizing the pin of the cavity vertex. -/
private lemma ckc_bern_marg {n : ℕ} (π : ℝ) (g : Finset (Fin n) → ℝ) :
    ∑ U : Finset (Fin (n + 1)), ckBern π U * g (ckcU U) = ∑ U : Finset (Fin n), ckBern π U * g U := by
  rw [← Fintype.sum_equiv (ckcUSplit n).symm (fun p => ckBern π (ckcUJoin p) * g (ckcU (ckcUJoin p)))
    _ (fun p => rfl), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun U _ => ?_
  have hU : ∀ b : Bool, ckcU (ckcUJoin (U, b)) = U := fun b => by
    ext v
    simp [ckcU, ckc_mem_UJoin_succ]
  simp only [Fintype.sum_bool, ckc_bern_succ π (ckcUJoin _), hU, ckc_mem_UJoin_zero]
  simp
  ring

/-! ### Poisson series over the cavity blocks -/

private lemma ckc_sum_add {n : ℕ} (N N' : Fin n → ℕ) : ∑ v, (N + N') v = ∑ v, N v + ∑ v, N' v := by
  simp [Finset.sum_add_distrib]

/-- Summability of `P_lam(D) Pois(l)(N₀) g(D, N₀)` under geometric domination. -/
private lemma ckc_summable_DN {n : ℕ} {lamD : Fin n → ℝ} (hD : ∀ i, 0 ≤ lamD i) {l : ℝ}
    (hl : 0 ≤ l) {g : (Fin n → ℕ) → ℕ → ℝ} {A y : ℝ} (hA : 0 ≤ A) (hy : 0 ≤ y)
    (hg : ∀ D N0, |g D N0| ≤ A * y ^ (∑ v, D v + N0)) :
    Summable (fun z : (Fin n → ℕ) × ℕ => poisPi lamD z.1 * poisPMF l z.2 * g z.1 z.2) := by
  refine ckc_summable_of_dom (u := fun D => A * (poisPi lamD D * y ^ (∑ v, D v)))
    (v := fun N0 => poisPMF l N0 * y ^ N0)
    ((ckc_hasSum_poisPi_pow hD hy).summable.mul_left A)
    (RSPoisPiAux.hasSum_poisPMF_mul_pow y).summable
    (fun D => mul_nonneg hA (ckc_poisPi_pow_nonneg hD hy D))
    (ckc_poisPMF_pow_nonneg hl hy) (fun z => ?_)
  have h1 := rs_poisPi_nonneg hD z.1
  have h2 := poisPMF_nonneg hl z.2
  rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h2]
  calc poisPi lamD z.1 * poisPMF l z.2 * |g z.1 z.2|
      ≤ poisPi lamD z.1 * poisPMF l z.2 * (A * y ^ (∑ v, z.1 v + z.2)) :=
        mul_le_mul_of_nonneg_left (hg _ _) (mul_nonneg h1 h2)
    _ = A * (poisPi lamD z.1 * y ^ (∑ v, z.1 v)) * (poisPMF l z.2 * y ^ z.2) := by
        rw [pow_add]; ring

private lemma ckc_abs_tsum_DN_le {n : ℕ} {lamD : Fin n → ℝ} (hD : ∀ i, 0 ≤ lamD i) {l : ℝ}
    (hl : 0 ≤ l) {g : (Fin n → ℕ) → ℕ → ℝ} {A y : ℝ} (hy : 0 ≤ y)
    (hg : ∀ D N0, |g D N0| ≤ A * y ^ (∑ v, D v + N0)) :
    |∑' z : (Fin n → ℕ) × ℕ, poisPi lamD z.1 * poisPMF l z.2 * g z.1 z.2| ≤
      A * (Real.exp ((∑ i, lamD i) * (y - 1)) * Real.exp (l * (y - 1))) := by
  rw [← Real.norm_eq_abs]
  refine tsum_of_norm_bounded ((ckc_hasSum_prod (ckc_hasSum_poisPi_pow hD hy)
    (RSPoisPiAux.hasSum_poisPMF_mul_pow (lam := l) y) (ckc_poisPi_pow_nonneg hD hy)
    (ckc_poisPMF_pow_nonneg hl hy)).mul_left A) fun z => ?_
  have h1 := rs_poisPi_nonneg hD z.1
  have h2 := poisPMF_nonneg hl z.2
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h2]
  calc poisPi lamD z.1 * poisPMF l z.2 * |g z.1 z.2|
      ≤ poisPi lamD z.1 * poisPMF l z.2 * (A * y ^ (∑ v, z.1 v + z.2)) :=
        mul_le_mul_of_nonneg_left (hg _ _) (mul_nonneg h1 h2)
    _ = A * ((poisPi lamD z.1 * y ^ (∑ v, z.1 v)) * (poisPMF l z.2 * y ^ z.2)) := by
        rw [pow_add]; ring

/-- Superposition of the two cross blocks (Lemma 7.1(iii)): independent Poisson counts with rates
`a` and `b` add up to Poisson counts with rates `a + b`; the loop coordinate is carried along. -/
private lemma ckc_superpose_loop {n : ℕ} {a b : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 ≤ b i) {l : ℝ} (hl : 0 ≤ l) (g : (Fin n → ℕ) → ℕ → ℝ) {A y : ℝ}
    (hA : 0 ≤ A) (hy : 0 ≤ y) (hg : ∀ D N0, |g D N0| ≤ A * y ^ (∑ v, D v + N0)) :
    ∑' w : (Fin n → ℕ) × ((Fin n → ℕ) × ℕ),
        poisPi a w.1 * (poisPi b w.2.1 * (poisPMF l w.2.2 * g (w.1 + w.2.1) w.2.2)) =
      ∑' z : (Fin n → ℕ) × ℕ, poisPi (a + b) z.1 * poisPMF l z.2 * g z.1 z.2 := by
  have hab : ∀ i, 0 ≤ (a + b) i := fun i => add_nonneg (ha i) (hb i)
  set Φ : (Fin n → ℕ) → ℝ := fun D => ∑' N0, poisPMF l N0 * g D N0 with hΦdef
  have hΦ : ∀ D, |Φ D| ≤ A * Real.exp (l * (y - 1)) * y ^ (∑ v, D v) := by
    intro D
    rw [← Real.norm_eq_abs]
    refine le_of_le_of_eq (tsum_of_norm_bounded
      ((RSPoisPiAux.hasSum_poisPMF_mul_pow (lam := l) y).mul_left (A * y ^ (∑ v, D v)))
      fun N0 => ?_) (by ring)
    have h2 := poisPMF_nonneg hl N0
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
    calc poisPMF l N0 * |g D N0| ≤ poisPMF l N0 * (A * y ^ (∑ v, D v + N0)) :=
          mul_le_mul_of_nonneg_left (hg _ _) h2
      _ = A * y ^ (∑ v, D v) * (poisPMF l N0 * y ^ N0) := by rw [pow_add]; ring
  -- the right side as an iterated series
  have hR : ∑' z : (Fin n → ℕ) × ℕ, poisPi (a + b) z.1 * poisPMF l z.2 * g z.1 z.2 =
      ∑' D, poisPi (a + b) D * Φ D := by
    rw [(ckc_summable_DN hab hl hA hy hg).tsum_prod]
    refine tsum_congr fun D => ?_
    simp only [hΦdef]
    rw [← tsum_mul_left]
    exact tsum_congr fun N0 => by ring
  -- summability of the triple series
  have hv : Summable (fun p : (Fin n → ℕ) × ℕ =>
      (poisPi b p.1 * y ^ (∑ v, p.1 v)) * (poisPMF l p.2 * y ^ p.2)) :=
    (ckc_hasSum_prod (ckc_hasSum_poisPi_pow hb hy)
      (RSPoisPiAux.hasSum_poisPMF_mul_pow (lam := l) y) (ckc_poisPi_pow_nonneg hb hy)
      (ckc_poisPMF_pow_nonneg hl hy)).summable
  have hv0 : ∀ p : (Fin n → ℕ) × ℕ,
      0 ≤ (poisPi b p.1 * y ^ (∑ v, p.1 v)) * (poisPMF l p.2 * y ^ p.2) := fun p =>
    mul_nonneg (ckc_poisPi_pow_nonneg hb hy _) (ckc_poisPMF_pow_nonneg hl hy _)
  have hS3 : Summable (fun w : (Fin n → ℕ) × ((Fin n → ℕ) × ℕ) =>
      poisPi a w.1 * (poisPi b w.2.1 * (poisPMF l w.2.2 * g (w.1 + w.2.1) w.2.2))) := by
    refine ckc_summable_of_dom (u := fun N => A * (poisPi a N * y ^ (∑ v, N v))) (v := _)
      ((ckc_hasSum_poisPi_pow ha hy).summable.mul_left A) hv
      (fun N => mul_nonneg hA (ckc_poisPi_pow_nonneg ha hy N)) hv0 (fun w => ?_)
    have h1 := rs_poisPi_nonneg ha w.1
    have h2 := rs_poisPi_nonneg hb w.2.1
    have h3 := poisPMF_nonneg hl w.2.2
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg h3]
    calc poisPi a w.1 * (poisPi b w.2.1 * (poisPMF l w.2.2 * |g (w.1 + w.2.1) w.2.2|))
        ≤ poisPi a w.1 * (poisPi b w.2.1 * (poisPMF l w.2.2 *
            (A * y ^ (∑ v, (w.1 + w.2.1) v + w.2.2)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hg _ _) h3) h2) h1
      _ = A * (poisPi a w.1 * y ^ (∑ v, w.1 v)) *
            ((poisPi b w.2.1 * y ^ (∑ v, w.2.1 v)) * (poisPMF l w.2.2 * y ^ w.2.2)) := by
          rw [ckc_sum_add, pow_add, pow_add]; ring
  have hS2 : ∀ N : Fin n → ℕ, Summable (fun p : (Fin n → ℕ) × ℕ =>
      poisPi b p.1 * (poisPMF l p.2 * g (N + p.1) p.2)) := by
    intro N
    refine ckc_summable_of_dom (u := fun N' => A * y ^ (∑ v, N v) * (poisPi b N' * y ^ (∑ v, N' v)))
      (v := fun N0 => poisPMF l N0 * y ^ N0)
      ((ckc_hasSum_poisPi_pow hb hy).summable.mul_left _)
      (RSPoisPiAux.hasSum_poisPMF_mul_pow (lam := l) y).summable
      (fun N' => mul_nonneg (mul_nonneg hA (pow_nonneg hy _)) (ckc_poisPi_pow_nonneg hb hy N'))
      (ckc_poisPMF_pow_nonneg hl hy) (fun p => ?_)
    have h2 := rs_poisPi_nonneg hb p.1
    have h3 := poisPMF_nonneg hl p.2
    rw [abs_mul, abs_mul, abs_of_nonneg h2, abs_of_nonneg h3]
    calc poisPi b p.1 * (poisPMF l p.2 * |g (N + p.1) p.2|)
        ≤ poisPi b p.1 * (poisPMF l p.2 * (A * y ^ (∑ v, (N + p.1) v + p.2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hg _ _) h3) h2
      _ = A * y ^ (∑ v, N v) * (poisPi b p.1 * y ^ (∑ v, p.1 v)) * (poisPMF l p.2 * y ^ p.2) := by
          rw [ckc_sum_add, pow_add, pow_add]; ring
  rw [hR, ck_poisPi_superpose ha hb hy hΦ, hS3.tsum_prod]
  refine tsum_congr fun N => ?_
  dsimp only
  rw [tsum_mul_left]
  congr 1
  rw [(hS2 N).tsum_prod]
  refine tsum_congr fun N' => ?_
  dsimp only
  simp only [hΦdef]
  rw [tsum_mul_left]

private lemma ckc_join_G {n : ℕ} (w : RSGraph n × ((Fin n → ℕ) × ((Fin n → ℕ) × ℕ))) :
    ckcG (ckcJoin w) = w.1 := rfl

private lemma ckc_join_A {n : ℕ} (w : RSGraph n × ((Fin n → ℕ) × ((Fin n → ℕ) × ℕ))) :
    ckcA (ckcJoin w) = w.2.1 := rfl

private lemma ckc_join_B {n : ℕ} (w : RSGraph n × ((Fin n → ℕ) × ((Fin n → ℕ) × ℕ))) :
    ckcB (ckcJoin w) = w.2.2.1 := rfl

private lemma ckc_join_N {n : ℕ} (w : RSGraph n × ((Fin n → ℕ) × ((Fin n → ℕ) × ℕ))) :
    ckcN (ckcJoin w) = w.2.2.2 := rfl

/-- The Poisson multigraph on `Fin (n+1)` is the independent product of its old block, the two
cross blocks and the loop; the cross blocks superpose into `D` (Lemma 7.1(i),(iii)). -/
private lemma ckc_tsum_split {n : ℕ} {lam : Fin (n + 1) × Fin (n + 1) → ℝ}
    (hlam : ∀ e, 0 ≤ lam e) (g : RSGraph n → (Fin n → ℕ) → ℕ → ℝ) {A y : ℝ} (hA : 0 ≤ A)
    (hy : 0 ≤ y) (hg : ∀ G D N0, |g G D N0| ≤ A * y ^ (rsEdges G + ∑ v, D v + N0)) :
    ∑' G : RSGraph (n + 1), poisPi lam G * g (ckcG G) (ckcA G + ckcB G) (ckcN G) =
      ∑' G : RSGraph n, poisPi (fun e => lam (e.1.succ, e.2.succ)) G *
        ∑' z : (Fin n → ℕ) × ℕ,
          poisPi ((fun v => lam (v.succ, 0)) + fun v => lam (0, v.succ)) z.1 *
            poisPMF (lam (0, 0)) z.2 * g G z.1 z.2 := by
  have hla : ∀ v : Fin n, 0 ≤ lam (v.succ, 0) := fun v => hlam _
  have hlb : ∀ v : Fin n, 0 ≤ lam (0, v.succ) := fun v => hlam _
  have hl0 : 0 ≤ lam (0, 0) := hlam _
  have hFw : ∀ w : RSGraph n × ((Fin n → ℕ) × ((Fin n → ℕ) × ℕ)),
      (fun G : RSGraph (n + 1) => poisPi lam G * g (ckcG G) (ckcA G + ckcB G) (ckcN G))
          ((ckcSplit n).symm w) =
        poisPi (fun e => lam (e.1.succ, e.2.succ)) w.1 * (poisPi (fun v => lam (v.succ, 0)) w.2.1 *
          (poisPi (fun v => lam (0, v.succ)) w.2.2.1 * (poisPMF (lam (0, 0)) w.2.2.2 *
            g w.1 (w.2.1 + w.2.2.1) w.2.2.2))) := by
    intro w
    show poisPi lam (ckcJoin w) * g (ckcG (ckcJoin w)) (ckcA (ckcJoin w) + ckcB (ckcJoin w))
      (ckcN (ckcJoin w)) = _
    rw [ckc_poisPi_split, ckc_join_G, ckc_join_A, ckc_join_B, ckc_join_N]
    ring
  have hFs : Summable
      (fun G : RSGraph (n + 1) => poisPi lam G * g (ckcG G) (ckcA G + ckcB G) (ckcN G)) := by
    refine rs_summable_poisPi_of_abs_le hlam (A := A) (c := y) hy fun G => ?_
    have h := ckc_rsEdges_split G
    have h' : ∑ i, G i = rsEdges (ckcG G) + ∑ v, (ckcA G + ckcB G) v + ckcN G := by
      rw [Nat.add_assoc]
      exact h
    rw [h']
    exact hg _ _ _
  have hS1 := ((ckcSplit n).symm.summable_iff.mpr hFs).congr hFw
  calc ∑' G : RSGraph (n + 1), poisPi lam G * g (ckcG G) (ckcA G + ckcB G) (ckcN G)
      = ∑' w, (fun G : RSGraph (n + 1) => poisPi lam G * g (ckcG G) (ckcA G + ckcB G) (ckcN G))
          ((ckcSplit n).symm w) := ((ckcSplit n).symm.tsum_eq _).symm
    _ = ∑' w : RSGraph n × ((Fin n → ℕ) × ((Fin n → ℕ) × ℕ)),
          poisPi (fun e => lam (e.1.succ, e.2.succ)) w.1 *
            (poisPi (fun v => lam (v.succ, 0)) w.2.1 * (poisPi (fun v => lam (0, v.succ)) w.2.2.1 *
              (poisPMF (lam (0, 0)) w.2.2.2 * g w.1 (w.2.1 + w.2.2.1) w.2.2.2))) := tsum_congr hFw
    _ = ∑' G : RSGraph n, ∑' w : (Fin n → ℕ) × ((Fin n → ℕ) × ℕ),
          poisPi (fun e => lam (e.1.succ, e.2.succ)) G *
            (poisPi (fun v => lam (v.succ, 0)) w.1 * (poisPi (fun v => lam (0, v.succ)) w.2.1 *
              (poisPMF (lam (0, 0)) w.2.2 * g G (w.1 + w.2.1) w.2.2))) := hS1.tsum_prod
    _ = ∑' G : RSGraph n, poisPi (fun e => lam (e.1.succ, e.2.succ)) G *
          ∑' w : (Fin n → ℕ) × ((Fin n → ℕ) × ℕ),
            poisPi (fun v => lam (v.succ, 0)) w.1 * (poisPi (fun v => lam (0, v.succ)) w.2.1 *
              (poisPMF (lam (0, 0)) w.2.2 * g G (w.1 + w.2.1) w.2.2)) :=
        tsum_congr fun G => tsum_mul_left
    _ = _ := tsum_congr fun G => by
        congr 1
        exact ckc_superpose_loop hla hlb hl0 (g G) (A := A * y ^ rsEdges G)
          (mul_nonneg hA (pow_nonneg hy _)) hy
          (fun D N0 => (hg G D N0).trans_eq (by rw [Nat.add_assoc, pow_add]; ring))

/-! ### Factorization of the planted law at `n + 1` (Lemma 7.1(iii)) -/

private lemma ckc_rates {q n : ℕ} (t ϱ : ℝ) (σ : Fin n → Fin q) (c : Fin q) :
    ((fun v : Fin n => ckPl q t ϱ (Fin.cons c σ : Fin (n + 1) → Fin q) (v.succ, 0)) +
        fun v => ckPl q t ϱ (Fin.cons c σ : Fin (n + 1) → Fin q) (0, v.succ)) =
      fun v => 2 * ϱ * rsM q t (σ v) c := by
  funext v
  simp only [Pi.add_apply, ckPl, Fin.cons_succ, Fin.cons_zero]
  rw [ckc_M_symm q t c (σ v)]
  ring

private lemma ckc_rate_old {q n : ℕ} (t ϱ : ℝ) (σ : Fin n → Fin q) (c : Fin q) :
    (fun e : Fin n × Fin n =>
        ckPl q t ϱ (Fin.cons c σ : Fin (n + 1) → Fin q) (e.1.succ, e.2.succ)) = ckPl q t ϱ σ := by
  funext e
  simp [ckPl]

private lemma ckc_rate_loop {q n : ℕ} (t ϱ : ℝ) (σ : Fin n → Fin q) (c : Fin q) :
    ckPl q t ϱ (Fin.cons c σ : Fin (n + 1) → Fin q) (0, 0) = ϱ * ckMm q t := by
  simp [ckPl, ckc_M_self]

/-- `E^{σ,c} g(D, N₀)` for `D_v ∼ Pois(2ϱ M(σ_v, c))`, `N₀ ∼ Pois(ϱ m₋)`. -/
private def ckcPsi (q : ℕ) (t ϱ : ℝ) {n : ℕ} (g : (Fin n → ℕ) → ℕ → ℝ) (σ : Fin n → Fin q)
    (c : Fin q) : ℝ :=
  ∑' z : (Fin n → ℕ) × ℕ, poisPi (fun v => 2 * ϱ * rsM q t (σ v) c) z.1 *
    poisPMF (ϱ * ckMm q t) z.2 * g z.1 z.2

private lemma ckc_rate_nonneg {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (σ : Fin n → Fin q) (c : Fin q) (v : Fin n) : 0 ≤ 2 * ϱ * rsM q t (σ v) c :=
  mul_nonneg (by positivity) (ckc_M_pos hp _ _).le

private lemma ckc_loop_nonneg {q : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) :
    0 ≤ ϱ * ckMm q t :=
  mul_nonneg hϱ (ck_const_bounds hp).1.le

/-- **Factorization.** Under `𝖰_{n+1}`, the old triple `(σ, G, U)` has law `𝖰_n`, the cavity colour
`c` is uniform and independent of it, and given `(σ, c, G, U)` we have `(D, N₀) ∼ P^{σ,c}`. -/
private lemma ckc_factor {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (π : ℝ)
    (f : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → (Fin n → ℕ) → ℕ → ℝ)
    {A y : ℝ} (hA : 0 ≤ A) (hy : 0 ≤ y)
    (hf : ∀ σ G U D N0, |f σ G U D N0| ≤ A * y ^ (rsEdges G + ∑ v, D v + N0)) :
    ckQExp q t ϱ π (n + 1) (fun σ G U =>
        f (fun v => σ v.succ) (ckcG G) (ckcU U) (ckcA G + ckcB G) (ckcN G)) =
      ckQExp q t ϱ π n (fun σ G U => (q : ℝ)⁻¹ * ∑ c : Fin q, ckcPsi q t ϱ (f σ G U) σ c) := by
  have hpl : ∀ (σ' : Fin (n + 1) → Fin q) e, 0 ≤ ckPl q t ϱ σ' e := fun σ' e =>
    mul_nonneg hϱ (ckc_M_pos hp _ _).le
  have hpl' : ∀ (σ : Fin n → Fin q) e, 0 ≤ ckPl q t ϱ σ e := fun σ e =>
    mul_nonneg hϱ (ckc_M_pos hp _ _).le
  have hinner : ∀ (c : Fin q) (σ : Fin n → Fin q) (U : Finset (Fin n)),
      ∑' G : RSGraph (n + 1), poisPi (ckPl q t ϱ (Fin.cons c σ : Fin (n + 1) → Fin q)) G *
        f σ (ckcG G) U (ckcA G + ckcB G) (ckcN G) =
      ∑' G : RSGraph n, poisPi (ckPl q t ϱ σ) G * ckcPsi q t ϱ (f σ G U) σ c := by
    intro c σ U
    have := ckc_tsum_split (lam := ckPl q t ϱ (Fin.cons c σ : Fin (n + 1) → Fin q)) (hpl _)
      (fun G D N0 => f σ G U D N0) hA hy (fun G D N0 => hf σ G U D N0)
    rw [this, ckc_rate_old, ckc_rates, ckc_rate_loop]
    rfl
  have hΨs : ∀ (c : Fin q) (σ : Fin n → Fin q) (U : Finset (Fin n)),
      Summable (fun G : RSGraph n => poisPi (ckPl q t ϱ σ) G * ckcPsi q t ϱ (f σ G U) σ c) := by
    intro c σ U
    refine rs_summable_poisPi_of_abs_le (hpl' σ) (c := y) hy
      (A := A * (Real.exp ((∑ i, 2 * ϱ * rsM q t (σ i) c) * (y - 1)) *
        Real.exp (ϱ * ckMm q t * (y - 1)))) fun G => ?_
    refine (ckc_abs_tsum_DN_le (ckc_rate_nonneg hp hϱ σ c) (ckc_loop_nonneg hp hϱ) hy
      (A := A * y ^ rsEdges G)
      (fun D N0 => (hf σ G U D N0).trans_eq (by rw [Nat.add_assoc, pow_add]; ring))).trans_eq ?_
    unfold rsEdges
    ring
  have hL : ∀ (c : Fin q) (σ : Fin n → Fin q),
      ∑ U : Finset (Fin (n + 1)), ckBern π U * ∑' G : RSGraph (n + 1),
        poisPi (ckPl q t ϱ (Fin.cons c σ : Fin (n + 1) → Fin q)) G *
          f (fun v => (Fin.cons c σ : Fin (n + 1) → Fin q) v.succ) (ckcG G) (ckcU U)
            (ckcA G + ckcB G) (ckcN G) =
      ∑ U : Finset (Fin n), ckBern π U *
        ∑' G : RSGraph n, poisPi (ckPl q t ϱ σ) G * ckcPsi q t ϱ (f σ G U) σ c := by
    intro c σ
    have hσ : (fun v : Fin n => (Fin.cons c σ : Fin (n + 1) → Fin q) v.succ) = σ := by
      funext v
      simp
    rw [hσ, ckc_bern_marg π (fun U => ∑' G : RSGraph (n + 1),
      poisPi (ckPl q t ϱ (Fin.cons c σ : Fin (n + 1) → Fin q)) G *
        f σ (ckcG G) U (ckcA G + ckcB G) (ckcN G))]
    exact Finset.sum_congr rfl fun U _ => by rw [hinner]
  have hR : ∀ (σ : Fin n → Fin q) (U : Finset (Fin n)),
      ∑' G : RSGraph n, poisPi (ckPl q t ϱ σ) G *
          ((q : ℝ)⁻¹ * ∑ c : Fin q, ckcPsi q t ϱ (f σ G U) σ c) =
        (q : ℝ)⁻¹ * ∑ c : Fin q,
          ∑' G : RSGraph n, poisPi (ckPl q t ϱ σ) G * ckcPsi q t ϱ (f σ G U) σ c := by
    intro σ U
    rw [← Summable.tsum_finsetSum (fun c _ => hΨs c σ U), ← tsum_mul_left]
    refine tsum_congr fun G => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  unfold ckQExp
  rw [ckc_sum_cons]
  simp only [hL, hR]
  rw [pow_succ, mul_inv, mul_assoc]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun U _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-! ### The pointwise bound (Lemma 7.1(ii)) -/

/-- The weight of the cavity vertex in `L(G⁺, (c, τ))`. -/
private def ckcK (q : ℕ) (t ϱ : ℝ) {n : ℕ} (D : Fin n → ℕ) (N0 : ℕ) (τ : Fin n → Fin q)
    (c : Fin q) : ℝ :=
  Real.exp (ϱ * (1 - ckMm q t)) * ckMm q t ^ N0 *
    (Real.exp (-(2 * ϱ) * ∑ v, (rsM q t (τ v) c - 1)) * ∏ v, rsM q t (τ v) c ^ D v)

private lemma ckc_K_pos {q n : ℕ} {t : ℝ} (hp : CKPar q t) (ϱ : ℝ) (D : Fin n → ℕ) (N0 : ℕ)
    (τ : Fin n → Fin q) (c : Fin q) : 0 < ckcK q t ϱ D N0 τ c := by
  unfold ckcK
  rw [ckc_term_eq_exp hp]
  exact Real.exp_pos _

private lemma ckc_L_pos {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (G : RSGraph n)
    (τ : Fin n → Fin q) : 0 < ckL q t ϱ G τ :=
  lt_of_lt_of_le (pow_pos (ck_const_bounds hp).1 _) (ck_L_mem hp hϱ G τ).1

private lemma ckc_agree_old {q n : ℕ} {U : Finset (Fin (n + 1))} {σ : Fin (n + 1) → Fin q}
    {c : Fin q} {τ : Fin n → Fin q} (h : ckAgree U σ (Fin.cons c τ : Fin (n + 1) → Fin q)) :
    ckAgree (ckcU U) (fun v => σ v.succ) τ := by
  intro v hv
  have := h v.succ (by simpa [ckcU] using hv)
  simpa using this

/-- `F̃(G⁺, U⁺, σ⁺) ≤ F̃(G, U, σ) X_{post}(D, N₀)`, by enlarging the sum over the cavity colour
to all of `[q]`. -/
private lemma ckc_Ft_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (σ : Fin (n + 1) → Fin q) (G : RSGraph (n + 1)) (U : Finset (Fin (n + 1))) :
    ckFt q t ϱ G U σ ≤ ckFt q t ϱ (ckcG G) (ckcU U) (fun v => σ v.succ) *
      ckX q t ϱ (ckPost q t ϱ (ckcG G) (ckcU U) (fun v => σ v.succ)) (ckcA G + ckcB G)
        (ckcN G) := by
  set σ' : Fin n → Fin q := fun v => σ v.succ with hσ'
  set Z := ∑ τ with ckAgree (ckcU U) σ' τ, ckL q t ϱ (ckcG G) τ with hZ
  have hZpos : 0 < Z := by
    have := ck_Ft_pos hp hϱ (ckcG G) (ckcU U) σ'
    unfold ckFt at this
    exact pos_of_mul_pos_right this (by positivity)
  have hpost : ∀ τ, ckPost q t ϱ (ckcG G) (ckcU U) σ' τ =
      if ckAgree (ckcU U) σ' τ then ckL q t ϱ (ckcG G) τ / Z else 0 := fun τ => rfl
  have hFt : ckFt q t ϱ (ckcG G) (ckcU U) σ' = ((q : ℝ) ^ n)⁻¹ * Z := rfl
  have hRHS : ckFt q t ϱ (ckcG G) (ckcU U) σ' *
        ckX q t ϱ (ckPost q t ϱ (ckcG G) (ckcU U) σ') (ckcA G + ckcB G) (ckcN G) =
      ((q : ℝ) ^ (n + 1))⁻¹ * ∑ c : Fin q, ∑ τ, if ckAgree (ckcU U) σ' τ then
        ckL q t ϱ (ckcG G) τ * ckcK q t ϱ (ckcA G + ckcB G) (ckcN G) τ c else 0 := by
    rw [hFt]
    unfold ckX ckcK
    simp only [hpost]
    rw [pow_succ, mul_inv]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun τ _ => ?_
    split_ifs with h
    · field_simp
    · simp
  have hLHS : ckFt q t ϱ G U σ = ((q : ℝ) ^ (n + 1))⁻¹ * ∑ c : Fin q, ∑ τ : Fin n → Fin q,
      if ckAgree U σ (Fin.cons c τ : Fin (n + 1) → Fin q) then
        ckL q t ϱ G (Fin.cons c τ : Fin (n + 1) → Fin q) else 0 := by
    unfold ckFt
    rw [Finset.sum_filter, ckc_sum_cons]
  rw [hLHS, hRHS]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun τ _ => ?_)
    (by positivity)
  by_cases h : ckAgree U σ (Fin.cons c τ : Fin (n + 1) → Fin q)
  · rw [if_pos h, if_pos (ckc_agree_old h), ckc_L_split]
    rfl
  · rw [if_neg h]
    split_ifs
    · exact (mul_pos (ckc_L_pos hp hϱ _ _) (ckc_K_pos hp _ _ _ _ _)).le
    · exact le_refl 0

private lemma ckc_log_Ft_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (σ : Fin (n + 1) → Fin q) (G : RSGraph (n + 1)) (U : Finset (Fin (n + 1))) :
    Real.log (ckFt q t ϱ G U σ) ≤
      Real.log (ckFt q t ϱ (ckcG G) (ckcU U) (fun v => σ v.succ)) +
        Real.log (ckX q t ϱ (ckPost q t ϱ (ckcG G) (ckcU U) (fun v => σ v.succ))
          (ckcA G + ckcB G) (ckcN G)) := by
  rw [← Real.log_mul (ck_Ft_pos hp hϱ _ _ _).ne'
    (ckc_X_pos hp hϱ (ck_post_isPMF hp hϱ _ _ _) _ _).ne']
  exact Real.log_le_log (ck_Ft_pos hp hϱ _ _ _) (ckc_Ft_le hp hϱ σ G U)

/-! ### The predictive kernel (Lemma 7.1(iv)) -/

/-- `R(h, τ) = q⁻¹ ∑_c P^{τ,c}(h)`: the law of `h = (D, N₀)` given the old colouring `τ`. -/
private def ckcR (q : ℕ) (t ϱ : ℝ) {n : ℕ} (h : (Fin n → ℕ) × ℕ) (τ : Fin n → Fin q) : ℝ :=
  (q : ℝ)⁻¹ * ∑ c : Fin q,
    poisPi (fun v => 2 * ϱ * rsM q t (τ v) c) h.1 * poisPMF (ϱ * ckMm q t) h.2

private lemma ckc_poisPMF_tilt (l m : ℝ) (k : ℕ) :
    poisPMF (l * m) k = poisPMF l k * (Real.exp (l * (1 - m)) * m ^ k) := by
  unfold poisPMF
  rw [mul_pow]
  have : Real.exp (-(l * m)) = Real.exp (-l) * Real.exp (l * (1 - m)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [this]
  ring

private lemma ckc_poisPi_tilt {n : ℕ} (ϱ : ℝ) (M : Fin n → ℝ) (D : Fin n → ℕ) :
    poisPi (fun v => 2 * ϱ * M v) D = poisPi (fun _ => 2 * ϱ) D *
      (Real.exp (-(2 * ϱ) * ∑ v, (M v - 1)) * ∏ v, M v ^ D v) := by
  have h := rs_poisPi_mul_prod_pow (fun _ => 2 * ϱ) M D
  set x := ∑ i : Fin n, 2 * ϱ * (M i - 1) with hx
  have hx' : -(2 * ϱ) * ∑ v, (M v - 1) = -x := by
    rw [hx, ← Finset.mul_sum]
    ring
  calc poisPi (fun v => 2 * ϱ * M v) D =
        Real.exp (-x) * (Real.exp x * poisPi (fun v => 2 * ϱ * M v) D) := by
          rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ = Real.exp (-x) * (poisPi (fun _ => 2 * ϱ) D * ∏ v, M v ^ D v) := by rw [h]
    _ = _ := by rw [hx']; ring

private lemma ckc_R_avg {q n : ℕ} (t ϱ : ℝ) (μ : (Fin n → Fin q) → ℝ) (h : (Fin n → ℕ) × ℕ) :
    ∑ τ, μ τ * ckcR q t ϱ h τ =
      poisPi (fun _ => 2 * ϱ) h.1 * poisPMF ϱ h.2 * ckX q t ϱ μ h.1 h.2 := by
  unfold ckcR ckX
  simp only [ckc_poisPi_tilt, ckc_poisPMF_tilt]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun τ _ => ?_
  ring

private lemma ckc_R_nonneg {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (h : (Fin n → ℕ) × ℕ) (τ : Fin n → Fin q) : 0 ≤ ckcR q t ϱ h τ := by
  unfold ckcR
  refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg q)) (Finset.sum_nonneg fun c _ => ?_)
  exact mul_nonneg (rs_poisPi_nonneg (ckc_rate_nonneg hp hϱ τ c) _)
    (poisPMF_nonneg (ckc_loop_nonneg hp hϱ) _)

private lemma ckc_post_congr {q n : ℕ} (t ϱ : ℝ) (G : RSGraph n) (U : Finset (Fin n))
    {ς ς' : Fin n → Fin q} (h : ckAgree U ς ς') : ckPost q t ϱ G U ς = ckPost q t ϱ G U ς' := by
  have hag : ckAgree U ς = ckAgree U ς' := by
    funext τ
    apply propext
    unfold ckAgree
    constructor
    · intro hτ v hv
      rw [hτ v hv, h v hv]
    · intro hτ v hv
      rw [hτ v hv, h v hv]
  unfold ckPost
  rw [hag]

/-! ### Domination by `A c^{|G|}` -/

private lemma ckc_affine_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {m m' : ℕ} (hm : m ≤ m') :
    a + b * m ≤ (a + 1) * Real.exp b ^ m' := by
  have h1 : (m : ℝ) ≤ m' := by exact_mod_cast hm
  rw [← Real.exp_nat_mul]
  have h2 : m' * b + 1 ≤ Real.exp (m' * b) := Real.add_one_le_exp _
  have h4 : 1 ≤ Real.exp (m' * b) := Real.one_le_exp (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left h1 hb]

private lemma ckc_dom_affine {n q : ℕ} {f : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ}
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hf : ∀ σ G U, |f σ G U| ≤ a + b * rsEdges G) :
    CKDom f :=
  ⟨a + 1, Real.exp b, (Real.exp_pos b).le, fun σ G U =>
    (hf σ G U).trans (ckc_affine_le ha hb le_rfl)⟩

/-! ### Lemma 7.1 and the step bound (7.1) -/

/-- **Lemma 7.1** (inequality form): for `ϱ ≥ 0` and `π ∈ [0, 1]`, with `𝖰 = 𝖰_{[n],ϱ,π}`,
`𝒦_{[n+1]}(ϱ, π) ≤ 𝒦_{[n]}(ϱ, π) + E_𝖰 Vert(post_{G,U,σ})`. -/
theorem ck_cavity {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ π : ℝ} (hϱ : 0 ≤ ϱ) (hπ0 : 0 ≤ π)
    (hπ1 : π ≤ 1) :
    ckK q t ϱ π (n + 1) ≤
      ckK q t ϱ π n + ckQExp q t ϱ π n (fun σ G U => ckVert q t ϱ (ckPost q t ϱ G U σ)) := by
  have hc := ck_const_bounds hp
  have hℓ : 0 ≤ ckEll q t := hc.2.2.2.2.2.1.le
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg (by have := hp.two_le; exact_mod_cast (by omega : 1 ≤ q))
  have hq := ckc_q_pos hp
  have ha1 : 0 ≤ (n : ℝ) * Real.log q + ϱ * (n : ℝ) ^ 2 :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) hlogq) (mul_nonneg hϱ (sq_nonneg _))
  have ha2 : 0 ≤ ϱ * (2 * (n : ℝ) + 1) := by positivity
  have hy : (0 : ℝ) ≤ Real.exp (ckEll q t) := (Real.exp_pos _).le
  -- bounds on the two pieces at level `n`
  have hb1 : ∀ (σ : Fin n → Fin q) (G : RSGraph n) (U : Finset (Fin n)),
      |Real.log (ckFt q t ϱ G U σ)| ≤
        ((n : ℝ) * Real.log q + ϱ * (n : ℝ) ^ 2) + ckEll q t * rsEdges G := fun σ G U =>
    (ck_abs_log_Ft_le hp hϱ G U σ).trans_eq (by ring)
  have hb2 : ∀ (G : RSGraph n) (U : Finset (Fin n)) (σ : Fin n → Fin q) (D : Fin n → ℕ) (N0 : ℕ),
      |Real.log (ckX q t ϱ (ckPost q t ϱ G U σ) D N0)| ≤
        ϱ * (2 * (n : ℝ) + 1) + ckEll q t * ((∑ v, D v + N0 : ℕ) : ℝ) := fun G U σ D N0 =>
    (ckc_abs_log_X_le hp hϱ (ck_post_isPMF hp hϱ G U σ) D N0).trans_eq (by unfold ckcBd; ring)
  -- domination at level `n + 1`
  have hd0 : CKDom (fun (σ : Fin (n + 1) → Fin q) (G : RSGraph (n + 1))
      (U : Finset (Fin (n + 1))) => Real.log (ckFt q t ϱ G U σ)) := by
    refine ckc_dom_affine (a := ((n + 1 : ℕ) : ℝ) * Real.log q + ϱ * ((n + 1 : ℕ) : ℝ) ^ 2)
      (b := ckEll q t) (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hlogq)
        (mul_nonneg hϱ (sq_nonneg _))) hℓ fun σ G U => ?_
    exact (ck_abs_log_Ft_le hp hϱ G U σ).trans_eq (by ring)
  have hd1 : CKDom (fun (σ : Fin (n + 1) → Fin q) (G : RSGraph (n + 1))
      (U : Finset (Fin (n + 1))) =>
        Real.log (ckFt q t ϱ (ckcG G) (ckcU U) (fun v => σ v.succ))) := by
    refine ckc_dom_affine ha1 hℓ fun σ G U => (hb1 _ _ _).trans ?_
    have h3 : (rsEdges (ckcG G) : ℝ) ≤ rsEdges G := by exact_mod_cast ckc_rsEdges_G_le G
    have := mul_le_mul_of_nonneg_left h3 hℓ
    linarith
  have hd2 : CKDom (fun (σ : Fin (n + 1) → Fin q) (G : RSGraph (n + 1))
      (U : Finset (Fin (n + 1))) => Real.log (ckX q t ϱ
        (ckPost q t ϱ (ckcG G) (ckcU U) (fun v => σ v.succ)) (ckcA G + ckcB G) (ckcN G))) := by
    refine ckc_dom_affine ha2 hℓ fun σ G U => (hb2 _ _ _ _ _).trans ?_
    have h4 : ((∑ v, (ckcA G + ckcB G) v + ckcN G : ℕ) : ℝ) ≤ rsEdges G := by
      exact_mod_cast ckc_rsEdges_DN_le G
    have := mul_le_mul_of_nonneg_left h4 hℓ
    linarith
  have hd12 : CKDom (fun (σ : Fin (n + 1) → Fin q) (G : RSGraph (n + 1))
      (U : Finset (Fin (n + 1))) =>
        Real.log (ckFt q t ϱ (ckcG G) (ckcU U) (fun v => σ v.succ)) + Real.log (ckX q t ϱ
          (ckPost q t ϱ (ckcG G) (ckcU U) (fun v => σ v.succ)) (ckcA G + ckcB G) (ckcN G))) := by
    refine ckc_dom_affine (add_nonneg ha1 ha2) (mul_nonneg zero_le_two hℓ) (b := 2 * ckEll q t)
      fun σ G U => (abs_add_le _ _).trans ?_
    have h1 := hb1 (fun v => σ v.succ) (ckcG G) (ckcU U)
    have h2 := hb2 (ckcG G) (ckcU U) (fun v => σ v.succ) (ckcA G + ckcB G) (ckcN G)
    have h3 : (rsEdges (ckcG G) : ℝ) ≤ rsEdges G := by exact_mod_cast ckc_rsEdges_G_le G
    have h4 : ((∑ v, (ckcA G + ckcB G) v + ckcN G : ℕ) : ℝ) ≤ rsEdges G := by
      exact_mod_cast ckc_rsEdges_DN_le G
    have := mul_le_mul_of_nonneg_left h3 hℓ
    have := mul_le_mul_of_nonneg_left h4 hℓ
    linarith
  -- (ii): the pointwise bound, integrated
  have hstep : ckK q t ϱ π (n + 1) ≤
      ckQExp q t ϱ π (n + 1) (fun σ G U =>
          Real.log (ckFt q t ϱ (ckcG G) (ckcU U) (fun v => σ v.succ))) +
        ckQExp q t ϱ π (n + 1) (fun σ G U => Real.log (ckX q t ϱ
          (ckPost q t ϱ (ckcG G) (ckcU U) (fun v => σ v.succ)) (ckcA G + ckcB G) (ckcN G))) := by
    rw [← ck_QExp_add hp hϱ π hd1 hd2]
    exact ck_QExp_mono hp hϱ hπ0 hπ1 hd0 hd12 fun σ G U => ckc_log_Ft_le hp hϱ σ G U
  -- (iii): the old free energy
  have hF1 : ckQExp q t ϱ π (n + 1) (fun σ G U =>
      Real.log (ckFt q t ϱ (ckcG G) (ckcU U) (fun v => σ v.succ))) = ckK q t ϱ π n := by
    have hfac := ckc_factor hp hϱ π
      (fun σ G U (_ : Fin n → ℕ) (_ : ℕ) => Real.log (ckFt q t ϱ G U σ))
      (A := (n : ℝ) * Real.log q + ϱ * (n : ℝ) ^ 2 + 1) (y := Real.exp (ckEll q t))
      (by linarith) hy (fun σ G U D N0 => (hb1 σ G U).trans (ckc_affine_le ha1 hℓ (by omega)))
    refine hfac.trans ?_
    unfold ckK
    congr 1
    funext σ G U
    have hone : ∀ c : Fin q, ckcPsi q t ϱ (fun _ _ => Real.log (ckFt q t ϱ G U σ)) σ c =
        Real.log (ckFt q t ϱ G U σ) := by
      intro c
      unfold ckcPsi
      rw [tsum_mul_right]
      have H := ckc_hasSum_prod (rs_hasSum_poisPi (ckc_rate_nonneg hp hϱ σ c))
        (hasSum_poisPMF (ckc_loop_nonneg hp hϱ)) (rs_poisPi_nonneg (ckc_rate_nonneg hp hϱ σ c))
        (poisPMF_nonneg (ckc_loop_nonneg hp hϱ))
      rw [H.tsum_eq, one_mul, one_mul]
    simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- (iii) + (iv): the vertex term
  have hF2 : ckQExp q t ϱ π (n + 1) (fun σ G U => Real.log (ckX q t ϱ
      (ckPost q t ϱ (ckcG G) (ckcU U) (fun v => σ v.succ)) (ckcA G + ckcB G) (ckcN G))) =
      ckQExp q t ϱ π n (fun σ G U => ckVert q t ϱ (ckPost q t ϱ G U σ)) := by
    have hfac := ckc_factor hp hϱ π
      (fun σ G U D N0 => Real.log (ckX q t ϱ (ckPost q t ϱ G U σ) D N0))
      (A := ϱ * (2 * (n : ℝ) + 1) + 1) (y := Real.exp (ckEll q t)) (by linarith) hy
      (fun σ G U D N0 => (hb2 G U σ D N0).trans (ckc_affine_le ha2 hℓ (by omega)))
    refine hfac.trans ?_
    have hsc : ∀ (σ : Fin n → Fin q) (G : RSGraph n) (U : Finset (Fin n)) (c : Fin q),
        Summable (fun h : (Fin n → ℕ) × ℕ => poisPi (fun v => 2 * ϱ * rsM q t (σ v) c) h.1 *
          poisPMF (ϱ * ckMm q t) h.2 * Real.log (ckX q t ϱ (ckPost q t ϱ G U σ) h.1 h.2)) := by
      intro σ G U c
      refine ckc_summable_DN (ckc_rate_nonneg hp hϱ σ c) (ckc_loop_nonneg hp hϱ)
        (g := fun D N0 => Real.log (ckX q t ϱ (ckPost q t ϱ G U σ) D N0))
        (A := ϱ * (2 * (n : ℝ) + 1) + 1) (y := Real.exp (ckEll q t)) (by linarith) hy ?_
      intro D N0
      exact (hb2 G U σ D N0).trans (ckc_affine_le ha2 hℓ le_rfl)
    have hR1 : ∀ (σ : Fin n → Fin q) (G : RSGraph n) (U : Finset (Fin n)),
        (q : ℝ)⁻¹ * ∑ c : Fin q,
            ckcPsi q t ϱ (fun D N0 => Real.log (ckX q t ϱ (ckPost q t ϱ G U σ) D N0)) σ c =
          ∑' h : (Fin n → ℕ) × ℕ,
            ckcR q t ϱ h σ * Real.log (ckX q t ϱ (ckPost q t ϱ G U σ) h.1 h.2) := by
      intro σ G U
      unfold ckcPsi ckcR
      rw [← Summable.tsum_finsetSum (fun c _ => hsc σ G U c), ← tsum_mul_left]
      refine tsum_congr fun h => ?_
      rw [mul_assoc, Finset.sum_mul]
    have hΦ : ∀ τ : Fin n → Fin q, Summable (fun h : (Fin n → ℕ) × ℕ =>
        ckcR q t ϱ h τ * ckcBd q t ϱ n (∑ v, h.1 v + h.2)) := by
      intro τ
      have hs : ∀ c : Fin q, Summable (fun h : (Fin n → ℕ) × ℕ =>
          poisPi (fun v => 2 * ϱ * rsM q t (τ v) c) h.1 * poisPMF (ϱ * ckMm q t) h.2 *
            ckcBd q t ϱ n (∑ v, h.1 v + h.2)) := by
        intro c
        refine ckc_summable_DN (ckc_rate_nonneg hp hϱ τ c) (ckc_loop_nonneg hp hϱ)
          (g := fun D N0 => ckcBd q t ϱ n (∑ v, D v + N0))
          (A := ϱ * (2 * (n : ℝ) + 1) + 1) (y := Real.exp (ckEll q t)) (by linarith) hy ?_
        intro D N0
        rw [abs_of_nonneg (ckc_Bd_nonneg hp hϱ _ _)]
        exact (le_of_eq (by unfold ckcBd; ring)).trans (ckc_affine_le ha2 hℓ le_rfl)
      refine ((summable_sum (s := Finset.univ) fun c _ => hs c).mul_left (q : ℝ)⁻¹).congr
        fun h => ?_
      unfold ckcR
      rw [mul_assoc, Finset.sum_mul]
    have hpred := ck_predictive (n := n) hp hϱ π (H := (Fin n → ℕ) × ℕ)
      (fun h τ => ckcR q t ϱ h τ) (fun h τ => ckc_R_nonneg hp hϱ h τ)
      (fun h G U ς => Real.log (ckX q t ϱ (ckPost q t ϱ G U ς) h.1 h.2))
      (fun h G U ς ς' hς =>
        congrArg (fun μ => Real.log (ckX q t ϱ μ h.1 h.2)) (ckc_post_congr t ϱ G U hς))
      (fun h => ckcBd q t ϱ n (∑ v, h.1 v + h.2))
      (fun h G U ς => ckc_abs_log_X_le hp hϱ (ck_post_isPMF hp hϱ G U ς) h.1 h.2) hΦ
    calc _ = ckQExp q t ϱ π n (fun σ G U => ∑' h : (Fin n → ℕ) × ℕ,
            ckcR q t ϱ h σ * Real.log (ckX q t ϱ (ckPost q t ϱ G U σ) h.1 h.2)) := by
          congr 1
          funext σ G U
          exact hR1 σ G U
      _ = _ := hpred
      _ = _ := by
          congr 1
          funext σ G U
          unfold ckVert
          refine tsum_congr fun h => ?_
          rw [ckc_R_avg]
          unfold ckLam
          ring
  rw [hF1, hF2] at hstep
  exact hstep

/-- **(7.1)**, from Lemmas 7.1 and 7.2: for `s ≥ 0` and `n ≥ 1`, with `ϱ'' = s/(2(n+1))`,
`β = s/(2n(n+1))` and `𝖰_k = 𝖰_{[n],ϱ'',π_k(n+1)}`,
`a_{n+1}(k) - a_n(k) ≤ E_{𝖰_k}[Vert(post) - β ∑_e kl(⟨M_e⟩_post)] + ks log q/(n+1)`. -/
theorem ck_step_decomp {q : ℕ} {t : ℝ} (hp : CKPar q t) {s : ℝ} (hs : 0 ≤ s) {n : ℕ}
    (hn : 0 < n) (k : ℕ) :
    ckA q t s (n + 1) k - ckA q t s n k ≤
      ckQExp q t (s / (2 * ((n : ℝ) + 1))) (ckPin s k (n + 1)) n (fun σ G U =>
          ckVert q t (s / (2 * ((n : ℝ) + 1))) (ckPost q t (s / (2 * ((n : ℝ) + 1))) G U σ) -
            s / (2 * n * ((n : ℝ) + 1)) *
              ckEdgeKL q t (ckPost q t (s / (2 * ((n : ℝ) + 1))) G U σ)) +
        k * s * Real.log q / ((n : ℝ) + 1) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg (by have := hp.two_le; exact_mod_cast (by omega : 1 ≤ q))
  set ϱ : ℝ := s / (2 * ((n : ℝ) + 1)) with hϱdef
  set β : ℝ := s / (2 * n * ((n : ℝ) + 1)) with hβdef
  set π : ℝ := ckPin s k (n + 1) with hπdef
  set πx : ℝ := 1 - Real.exp (-(k * s / (n * ((n : ℝ) + 1)))) with hπxdef
  have hϱ : 0 ≤ ϱ := by positivity
  have hβ : 0 ≤ β := by positivity
  have hπ0 : 0 ≤ π := by
    simp only [hπdef, ckPin]
    have h0 : 0 ≤ (k : ℝ) * s / ((n + 1 : ℕ) : ℝ) := by positivity
    linarith [Real.exp_le_one_iff.mpr (by linarith : -((k : ℝ) * s / ((n + 1 : ℕ) : ℝ)) ≤ 0)]
  have hπ1 : π ≤ 1 := by
    simp only [hπdef, ckPin]
    linarith [Real.exp_pos (-((k : ℝ) * s / ((n + 1 : ℕ) : ℝ)))]
  have hy : 0 ≤ (k : ℝ) * s / (n * ((n : ℝ) + 1)) := by positivity
  have hx0 : 0 ≤ πx := by
    simp only [hπxdef]
    linarith [Real.exp_le_one_iff.mpr (by linarith : -((k : ℝ) * s / (n * ((n : ℝ) + 1))) ≤ 0)]
  have hx1 : πx ≤ 1 := by
    simp only [hπxdef]
    linarith [Real.exp_pos (-((k : ℝ) * s / (n * ((n : ℝ) + 1))))]
  have hcav := ck_cavity (n := n) hp hϱ hπ0 hπ1
  have hedge := ck_edge_lower (n := n) hp hϱ hβ hπ0 hπ1
  have hpin := (ck_pin_cost (n := n) hp (add_nonneg hϱ hβ) hπ0 hπ1 hx0 hx1).1
  have hsum : ϱ + β = s / (2 * (n : ℝ)) := by
    simp only [hϱdef, hβdef]
    field_simp
  have hpinn : 1 - (1 - π) * (1 - πx) = ckPin s k n := by
    simp only [hπdef, hπxdef, ckPin, sub_sub_cancel, ← Real.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  have hA1 : ckA q t s (n + 1) k = ckK q t ϱ π (n + 1) := by
    simp only [ckA, hϱdef, hπdef]
    push_cast
    rfl
  have hA0 : ckA q t s n k = ckK q t (ϱ + β) (1 - (1 - π) * (1 - πx)) n := by
    rw [hsum, hpinn]
    rfl
  have hπx : (n : ℝ) * πx * Real.log q ≤ k * s * Real.log q / ((n : ℝ) + 1) := by
    have h1 : πx ≤ k * s / (n * ((n : ℝ) + 1)) := by
      simp only [hπxdef]
      linarith [Real.add_one_le_exp (-((k : ℝ) * s / (n * ((n : ℝ) + 1))))]
    have h2 : (n : ℝ) * πx ≤ k * s / ((n : ℝ) + 1) := by
      calc (n : ℝ) * πx ≤ n * (k * s / (n * ((n : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left h1 hn'.le
        _ = k * s / ((n : ℝ) + 1) := by field_simp
    calc (n : ℝ) * πx * Real.log q ≤ k * s / ((n : ℝ) + 1) * Real.log q :=
          mul_le_mul_of_nonneg_right h2 hlogq
      _ = k * s * Real.log q / ((n : ℝ) + 1) := by ring
  obtain ⟨V, hV⟩ := ckc_abs_vert_le (n := n) hp hϱ
  have hdV : CKDom (fun (σ : Fin n → Fin q) (G : RSGraph n) (U : Finset (Fin n)) =>
      ckVert q t ϱ (ckPost q t ϱ G U σ)) :=
    ⟨V, 1, zero_le_one, fun σ G U => by
      rw [one_pow, mul_one]
      exact hV _ (ck_post_isPMF hp hϱ G U σ)⟩
  have hdE : CKDom (fun (σ : Fin n → Fin q) (G : RSGraph n) (U : Finset (Fin n)) =>
      (-β) * ckEdgeKL q t (ckPost q t ϱ G U σ)) := by
    refine ⟨β * ((n : ℝ) ^ 2 * (1 + ckEll q t * ckMp t)), 1, zero_le_one, fun σ G U => ?_⟩
    have h := ck_edgeKL_mem hp (ck_post_isPMF hp hϱ G U σ)
    rw [one_pow, mul_one, abs_mul, abs_neg, abs_of_nonneg hβ, abs_of_nonneg h.1]
    exact mul_le_mul_of_nonneg_left h.2 hβ
  have hlin : ckQExp q t ϱ π n (fun σ G U => ckVert q t ϱ (ckPost q t ϱ G U σ) -
        β * ckEdgeKL q t (ckPost q t ϱ G U σ)) =
      ckQExp q t ϱ π n (fun σ G U => ckVert q t ϱ (ckPost q t ϱ G U σ)) -
        β * ckQExp q t ϱ π n (fun σ G U => ckEdgeKL q t (ckPost q t ϱ G U σ)) := by
    have hfun : (fun (σ : Fin n → Fin q) (G : RSGraph n) (U : Finset (Fin n)) =>
          ckVert q t ϱ (ckPost q t ϱ G U σ) - β * ckEdgeKL q t (ckPost q t ϱ G U σ)) =
        (fun σ G U => ckVert q t ϱ (ckPost q t ϱ G U σ) +
          (-β) * ckEdgeKL q t (ckPost q t ϱ G U σ)) := by
      funext σ G U
      ring
    rw [hfun, ck_QExp_add hp hϱ π hdV hdE, ck_QExp_smul]
    ring
  rw [hlin, hA1, hA0]
  linarith

end

end ERZeroFreeness
