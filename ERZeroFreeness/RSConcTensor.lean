/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSConcOneDim

/-!
# Appendix C, Lemma C.6: tensorization

The two Doob-martingale steps and the coupling step of the proof of Lemma C.6 (`lem:rs-conc`),
without conditional expectations:

* `rs_poisPiExp_exp_sub_le` (edge counts given the labels): for independent Poisson coordinates
  with means `lam_i` and `f` with `B`-bounded increments, `|h| B ≤ 1`:
  `E e^{h(f - E f)} ≤ e^{2 h² B² ∑_i lam_i}`;
* `rs_abs_poisPiExp_sub_le` (changing the means):
  `|E_{lam} f - E_{lam'} f| ≤ B ∑_i |lam_i - lam'_i|`;
* `rs_label_exp_sub_le` (the labels): for independent labels and `Φ` with `c`-bounded differences:
  `E e^{h(Φ - EΦ)} ≤ e^{n h² c²/2}`.

## Proof

All three by induction on the number of coordinates (`Fin k`, `Fin.consEquiv`); the two Poisson
statements are then transported to a general finite `ι` along `Fintype.equivFin`.  The "chain
rule" replaces the tower property: if `∑_b ν_a(b) e^{h(F(a,b) - G(a))} ≤ e^s` for every `a` and
`∑_a μ(a) e^{h(G(a) - m)} ≤ e^t`, then `∑_a μ(a) ∑_b ν_a(b) e^{h(F(a,b) - m)} ≤ e^{s+t}`
(`exp_moment_chain` for the Poisson coordinates; the label step does the same computation with
finite sums).  The Fubini split of `poisPiExp` over `Fin (k+1)` (`poisPiExp_cons`) uses
`(Fin.consEquiv _).tsum_eq` and `Summable.tsum_prod`, with summability from `rs_edgeLip_summable`.
For the edge step, the function `y ↦ E_{rest} f(cons y ·)` has increments `≤ B` and
`rs_poisExp_exp_sub_le` applies; the coupling step applies `rs_abs_poisExp_sub_le` coordinate by
coordinate; for the label step the averaged function `Ψ(a) = E_{rest} Φ(cons a ·)` has
oscillation `≤ c` and `rs_fin_exp_sub_le` applies.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

namespace RSConcTensorAux

/-! ### Auxiliary lemmas: chain rule, Fubini over `Fin.cons`, transport, increments, summability -/

/-- The chain rule replacing the tower property. -/
theorem exp_moment_chain {α β : Type*} {μ : α → ℝ} (hμ : ∀ a, 0 ≤ μ a) {ν : α → β → ℝ}
    {F : α → β → ℝ} {G : α → ℝ} {h m s t : ℝ}
    (hin : ∀ a, ∑' b, ν a b * Real.exp (h * (F a b - G a)) ≤ Real.exp s)
    (hout : ∑' a, μ a * Real.exp (h * (G a - m)) ≤ Real.exp t)
    (hsum : Summable fun a => μ a * Real.exp (h * (G a - m))) :
    ∑' a, μ a * ∑' b, ν a b * Real.exp (h * (F a b - m)) ≤ Real.exp (s + t) := by
  have hpt : ∀ a, μ a * ∑' b, ν a b * Real.exp (h * (F a b - m)) ≤
      μ a * Real.exp (h * (G a - m)) * Real.exp s := by
    intro a
    have h1 : ∑' b, ν a b * Real.exp (h * (F a b - m)) =
        Real.exp (h * (G a - m)) * ∑' b, ν a b * Real.exp (h * (F a b - G a)) := by
      rw [← tsum_mul_left]
      congr 1
      ext b
      rw [show h * (F a b - m) = h * (G a - m) + h * (F a b - G a) by ring, Real.exp_add]
      ring
    rw [h1, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left (hin a) (mul_nonneg (hμ a) (Real.exp_pos _).le)
  have hbound : Summable fun a => μ a * Real.exp (h * (G a - m)) * Real.exp s :=
    hsum.mul_right _
  by_cases hS : Summable fun a => μ a * ∑' b, ν a b * Real.exp (h * (F a b - m))
  · calc ∑' a, μ a * ∑' b, ν a b * Real.exp (h * (F a b - m))
        ≤ ∑' a, μ a * Real.exp (h * (G a - m)) * Real.exp s := hS.tsum_le_tsum hpt hbound
      _ = (∑' a, μ a * Real.exp (h * (G a - m))) * Real.exp s := tsum_mul_right
      _ ≤ Real.exp t * Real.exp s := mul_le_mul_of_nonneg_right hout (Real.exp_pos _).le
      _ = Real.exp (s + t) := by rw [← Real.exp_add, add_comm]
  · rw [tsum_eq_zero_of_not_summable hS]
    exact (Real.exp_pos _).le

/-- `P_lam(cons y z) = Pois(lam_0)(y) · P_{lam ∘ succ}(z)`. -/
theorem poisPi_cons {k : ℕ} (lam : Fin (k + 1) → ℝ) (y : ℕ) (z : Fin k → ℕ) :
    poisPi lam (Fin.cons y z) = poisPMF (lam 0) y * poisPi (fun j => lam j.succ) z := by
  simp only [poisPi, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- Fubini over the first coordinate: `E_lam f = E_{y ∼ Pois(lam_0)} E_{lam ∘ succ} f(cons y ·)`. -/
theorem poisPiExp_cons {k : ℕ} {lam : Fin (k + 1) → ℝ} {f : (Fin (k + 1) → ℕ) → ℝ}
    (hf : Summable fun N => poisPi lam N * f N) :
    poisPiExp lam f = ∑' y : ℕ, poisPMF (lam 0) y *
      poisPiExp (fun j => lam j.succ) (fun z => f (Fin.cons y z)) := by
  unfold poisPiExp
  rw [← (Fin.consEquiv (fun _ => ℕ)).tsum_eq]
  have hs : Summable fun p : ℕ × (Fin k → ℕ) =>
      poisPi lam (Fin.consEquiv (fun _ => ℕ) p) * f (Fin.consEquiv (fun _ => ℕ) p) :=
    (Fin.consEquiv (fun _ => ℕ)).summable_iff.mpr hf
  rw [hs.tsum_prod]
  refine tsum_congr fun y => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun z => ?_
  have hc : (Fin.consEquiv (fun _ => ℕ)) (y, z) = (Fin.cons y z : Fin (k + 1) → ℕ) := rfl
  rw [hc, poisPi_cons]
  ring

/-- Transport of `poisPiExp` along an equivalence of index types. -/
theorem poisPiExp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (lam : ι → ℝ)
    (f : (ι → ℕ) → ℝ) :
    poisPiExp lam f = poisPiExp (fun k => lam (e.symm k)) (fun M => f (fun i => M (e i))) := by
  let E : (κ → ℕ) ≃ (ι → ℕ) :=
    { toFun := fun M i => M (e i)
      invFun := fun N k => N (e.symm k)
      left_inv := fun M => by funext k; simp
      right_inv := fun N => by funext i; simp }
  unfold poisPiExp
  rw [← E.tsum_eq]
  refine tsum_congr fun M => ?_
  congr 1
  unfold poisPi
  have := Equiv.prod_comp e (fun k => poisPMF (lam (e.symm k)) (M k))
  simp only [Equiv.symm_apply_apply] at this
  exact this

/-- Bounded increments are preserved by relabelling the coordinates. -/
theorem edgeLip_comp_equiv {ι κ : Type*} (e : ι ≃ κ) {B : ℝ} {f : (ι → ℕ) → ℝ}
    (hf : EdgeLip B f) : EdgeLip B (fun M : κ → ℕ => f (fun i => M (e i))) := by
  intro M M' j hj hj'
  refine hf (fun i => M (e i)) (fun i => M' (e i)) (e.symm j) (fun i hi => ?_) ?_
  · exact hj (e i) (fun hc => hi (by rw [← hc, Equiv.symm_apply_apply]))
  · simp only [Equiv.apply_symm_apply]
    exact hj'

/-- Freezing the first coordinate preserves bounded increments. -/
theorem edgeLip_cons {k : ℕ} {B : ℝ} {f : (Fin (k + 1) → ℕ) → ℝ} (hf : EdgeLip B f) (y : ℕ) :
    EdgeLip B (fun z : Fin k → ℕ => f (Fin.cons y z)) := by
  intro z z' j hj hj'
  refine hf (Fin.cons y z) (Fin.cons y z') j.succ (fun i hi => ?_) ?_
  · cases i using Fin.cases with
    | zero => simp
    | succ i =>
      simp only [Fin.cons_succ]
      exact hj i (fun hc => hi (by rw [hc]))
  · simp only [Fin.cons_succ]
    exact hj'

/-- Increment in the first coordinate. -/
theorem edgeLip_cons_succ {k : ℕ} {B : ℝ} {f : (Fin (k + 1) → ℕ) → ℝ} (hf : EdgeLip B f)
    (y : ℕ) (z : Fin k → ℕ) :
    |f (Fin.cons (y + 1) z) - f (Fin.cons y z)| ≤ B := by
  refine hf (Fin.cons y z) (Fin.cons (y + 1) z) 0 (fun i hi => ?_) (by simp)
  cases i using Fin.cases with
  | zero => exact absurd rfl hi
  | succ i => simp

/-- Linear growth from bounded increments on `ℕ`. -/
theorem abs_sub_zero_le_of_succ {B : ℝ} {g : ℕ → ℝ} (hg : ∀ k, |g (k + 1) - g k| ≤ B) :
    ∀ k : ℕ, |g k - g 0| ≤ B * k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc |g (k + 1) - g 0| = |(g (k + 1) - g k) + (g k - g 0)| := by ring_nf
      _ ≤ |g (k + 1) - g k| + |g k - g 0| := abs_add_le _ _
      _ ≤ B + B * k := add_le_add (hg k) ih
      _ = B * ((k + 1 : ℕ) : ℝ) := by push_cast; ring

/-- `k ↦ Pois(lam)(k) g(k)` is summable when `g` has bounded increments. -/
theorem summable_poisPMF_mul_of_succ {lam : ℝ} (hlam : 0 ≤ lam) {B : ℝ} {g : ℕ → ℝ}
    (hg : ∀ k, |g (k + 1) - g k| ≤ B) : Summable fun k => poisPMF lam k * g k := by
  have h1 : Summable fun k => poisPMF lam k * (k : ℝ) ^ 1 := summable_poisPMF_mul_pow hlam 1
  have h0 : Summable fun k => poisPMF lam k := (hasSum_poisPMF hlam).summable
  have hs : Summable fun k => |g 0| * poisPMF lam k + B * (poisPMF lam k * (k : ℝ) ^ 1) :=
    (h0.mul_left _).add (h1.mul_left _)
  refine Summable.of_norm_bounded hs fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poisPMF_nonneg hlam k)]
  have hk := abs_sub_zero_le_of_succ hg k
  have hgk : |g k| ≤ |g 0| + B * k := by
    calc |g k| = |(g k - g 0) + g 0| := by ring_nf
      _ ≤ |g k - g 0| + |g 0| := abs_add_le _ _
      _ ≤ B * k + |g 0| := add_le_add hk le_rfl
      _ = |g 0| + B * k := by ring
  calc poisPMF lam k * |g k| ≤ poisPMF lam k * (|g 0| + B * k) :=
        mul_le_mul_of_nonneg_left hgk (poisPMF_nonneg hlam k)
    _ = |g 0| * poisPMF lam k + B * (poisPMF lam k * (k : ℝ) ^ 1) := by ring

/-- `k ↦ Pois(lam)(k) y^k` is summable (all real `lam`, `y`). -/
theorem summable_poisPMF_mul_geom (lam y : ℝ) : Summable fun k => poisPMF lam k * y ^ k := by
  refine ((Real.summable_pow_div_factorial (lam * y)).mul_left (Real.exp (-lam))).congr
    fun k => ?_
  unfold poisPMF
  rw [mul_pow]
  ring

/-- `k ↦ Pois(lam)(k) e^{h(g(k) - m)}` is summable when `g` has bounded increments. -/
theorem summable_poisPMF_mul_exp_of_succ {lam : ℝ} (hlam : 0 ≤ lam) {B : ℝ} {g : ℕ → ℝ}
    (hg : ∀ k, |g (k + 1) - g k| ≤ B) (h m : ℝ) :
    Summable fun k => poisPMF lam k * Real.exp (h * (g k - m)) := by
  have hs : Summable fun k => Real.exp (|h| * |g 0 - m|) *
      (poisPMF lam k * Real.exp (|h| * B) ^ k) :=
    (summable_poisPMF_mul_geom lam (Real.exp (|h| * B))).mul_left _
  refine Summable.of_norm_bounded hs fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poisPMF_nonneg hlam k),
    abs_of_nonneg (Real.exp_pos _).le]
  have hk := abs_sub_zero_le_of_succ hg k
  have hexp : Real.exp (h * (g k - m)) ≤
      Real.exp (|h| * |g 0 - m|) * Real.exp (|h| * B) ^ k := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have e1 : h * (g k - m) ≤ |h| * |g k - m| := by
      rw [← abs_mul]; exact le_abs_self _
    have e2 : |g k - m| ≤ |g k - g 0| + |g 0 - m| := abs_sub_le _ _ _
    have e3 : |h| * |g k - m| ≤ |h| * (B * k + |g 0 - m|) :=
      mul_le_mul_of_nonneg_left (e2.trans (add_le_add hk le_rfl)) (abs_nonneg h)
    nlinarith [e1, e3]
  calc poisPMF lam k * Real.exp (h * (g k - m))
      ≤ poisPMF lam k * (Real.exp (|h| * |g 0 - m|) * Real.exp (|h| * B) ^ k) :=
        mul_le_mul_of_nonneg_left hexp (poisPMF_nonneg hlam k)
    _ = _ := by ring

/-- Two `B`-close summable functions have `B`-close expectations. -/
theorem abs_poisPiExp_sub_le_of_abs_le {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) {f g : (ι → ℕ) → ℝ}
    (hf : Summable fun N => poisPi lam N * f N) (hg : Summable fun N => poisPi lam N * g N)
    {C : ℝ} (hfg : ∀ N, |f N - g N| ≤ C) : |poisPiExp lam f - poisPiExp lam g| ≤ C := by
  have hP := rs_hasSum_poisPi hlam
  rw [abs_sub_le_iff]
  constructor
  · have H : HasSum (fun N => poisPi lam N * g N + C * poisPi lam N)
        (poisPiExp lam g + C * 1) := hg.hasSum.add (hP.mul_left C)
    have : poisPiExp lam f ≤ poisPiExp lam g + C * 1 := hasSum_le (fun N => ?_) hf.hasSum H
    · linarith
    · have h1 := (abs_le.mp (hfg N)).2
      have h2 := rs_poisPi_nonneg hlam N
      nlinarith
  · have H : HasSum (fun N => poisPi lam N * f N + C * poisPi lam N)
        (poisPiExp lam f + C * 1) := hf.hasSum.add (hP.mul_left C)
    have : poisPiExp lam g ≤ poisPiExp lam f + C * 1 := hasSum_le (fun N => ?_) hg.hasSum H
    · linarith
    · have h1 := (abs_le.mp (hfg N)).1
      have h2 := rs_poisPi_nonneg hlam N
      nlinarith

/-- One-coordinate version of `abs_poisPiExp_sub_le_of_abs_le`. -/
theorem abs_poisExp_sub_le_of_abs_le {lam : ℝ} (hlam : 0 ≤ lam) {f g : ℕ → ℝ}
    (hf : Summable fun k => poisPMF lam k * f k) (hg : Summable fun k => poisPMF lam k * g k)
    {C : ℝ} (hfg : ∀ k, |f k - g k| ≤ C) : |poisExp lam f - poisExp lam g| ≤ C := by
  have hP := hasSum_poisPMF hlam
  rw [abs_sub_le_iff]
  constructor
  · have H : HasSum (fun k => poisPMF lam k * g k + C * poisPMF lam k)
        (poisExp lam g + C * 1) := hg.hasSum.add (hP.mul_left C)
    have : poisExp lam f ≤ poisExp lam g + C * 1 := hasSum_le (fun k => ?_) hf.hasSum H
    · linarith
    · have h1 := (abs_le.mp (hfg k)).2
      have h2 := poisPMF_nonneg hlam k
      nlinarith
  · have H : HasSum (fun k => poisPMF lam k * f k + C * poisPMF lam k)
        (poisExp lam f + C * 1) := hf.hasSum.add (hP.mul_left C)
    have : poisExp lam g ≤ poisExp lam f + C * 1 := hasSum_le (fun k => ?_) hg.hasSum H
    · linarith
    · have h1 := (abs_le.mp (hfg k)).1
      have h2 := poisPMF_nonneg hlam k
      nlinarith

/-- `f` is `P_lam`-summable when it has bounded increments. -/
theorem edgeLip_summable_id {ι : Type*} [Fintype ι] {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    {B : ℝ} {f : (ι → ℕ) → ℝ} (hf : EdgeLip B f) :
    Summable fun N => poisPi lam N * f N := by
  have := rs_edgeLip_summable hlam hf (φ := id) (A := 1) (c := 1) (fun y => by
    simp only [id, one_mul]
    have := Real.add_one_le_exp |y|
    linarith)
  simpa using this

/-- `e^{h(f - m)}` is `P_lam`-summable when `f` has bounded increments. -/
theorem edgeLip_summable_exp {ι : Type*} [Fintype ι] {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    {B : ℝ} {f : (ι → ℕ) → ℝ} (hf : EdgeLip B f) (h m : ℝ) :
    Summable fun N => poisPi lam N * Real.exp (h * (f N - m)) := by
  have := rs_edgeLip_summable hlam hf (φ := fun u => Real.exp (h * (u - m)))
    (A := Real.exp (|h| * |m|)) (c := |h|) (fun y => by
      rw [abs_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have e1 : h * (y - m) ≤ |h| * |y - m| := by
        rw [← abs_mul]; exact le_abs_self _
      have e2 : |y - m| ≤ |y| + |m| := abs_sub _ _
      have e3 : |h| * |y - m| ≤ |h| * (|y| + |m|) :=
        mul_le_mul_of_nonneg_left e2 (abs_nonneg h)
      nlinarith [e1, e3])
  simpa using this

/-- With no coordinates, `E_lam g = g(x)` for the unique `x`. -/
theorem poisPiExp_fin_zero (lam : Fin 0 → ℝ) (g : (Fin 0 → ℕ) → ℝ) (x : Fin 0 → ℕ) :
    poisPiExp lam g = g x := by
  unfold poisPiExp
  have h1 : ∀ y : Fin 0 → ℕ, poisPi lam y = 1 := fun y => by simp [poisPi]
  rw [(hasSum_unique (fun N : Fin 0 → ℕ => poisPi lam N * g N)).tsum_eq, h1, one_mul]
  exact congrArg g (Subsingleton.elim _ _)

/-- `rs_poisPiExp_exp_sub_le` on `Fin k`, by induction on `k`. -/
theorem poisPiExp_exp_sub_le_fin : ∀ (k : ℕ) {lam : Fin k → ℝ} (_hlam : ∀ i, 0 ≤ lam i)
    {B : ℝ} (_hB : 0 ≤ B) {f : (Fin k → ℕ) → ℝ} (_hf : EdgeLip B f) {h : ℝ}
    (_hh : |h| * B ≤ 1),
    poisPiExp lam (fun N => Real.exp (h * (f N - poisPiExp lam f))) ≤
      Real.exp (2 * h ^ 2 * B ^ 2 * ∑ i, lam i)
  | 0, lam, _, B, _, f, _, h, _ => by
    rw [poisPiExp_fin_zero lam f default, poisPiExp_fin_zero lam _ default]
    simp
  | k + 1, lam, hlam, B, hB, f, hf, h, hh => by
    set lam' : Fin k → ℝ := fun j => lam j.succ with hlam'_def
    have hlam' : ∀ j, 0 ≤ lam' j := fun j => hlam j.succ
    set G : ℕ → ℝ := fun y => poisPiExp lam' (fun z => f (Fin.cons y z)) with hG_def
    have hfy : ∀ y, EdgeLip B (fun z : Fin k → ℕ => f (Fin.cons y z)) := edgeLip_cons hf
    have hG : ∀ y, |G (y + 1) - G y| ≤ B := fun y =>
      abs_poisPiExp_sub_le_of_abs_le hlam' (edgeLip_summable_id hlam' (hfy (y + 1)))
        (edgeLip_summable_id hlam' (hfy y)) (fun z => edgeLip_cons_succ hf y z)
    set m := poisPiExp lam f with hm_def
    have hm : m = poisExp (lam 0) G := poisPiExp_cons (edgeLip_summable_id hlam hf)
    have hL : poisPiExp lam (fun N => Real.exp (h * (f N - m))) =
        ∑' y, poisPMF (lam 0) y *
          ∑' z, poisPi lam' z * Real.exp (h * (f (Fin.cons y z) - m)) :=
      poisPiExp_cons (edgeLip_summable_exp hlam hf h m)
    have hin : ∀ y, ∑' z, poisPi lam' z * Real.exp (h * (f (Fin.cons y z) - G y)) ≤
        Real.exp (2 * h ^ 2 * B ^ 2 * ∑ j, lam' j) := fun y =>
      poisPiExp_exp_sub_le_fin k hlam' hB (hfy y) hh
    have hout : ∑' y, poisPMF (lam 0) y * Real.exp (h * (G y - m)) ≤
        Real.exp (2 * lam 0 * h ^ 2 * B ^ 2) := by
      rw [hm]; exact rs_poisExp_exp_sub_le (hlam 0) hG hh
    have hsum := summable_poisPMF_mul_exp_of_succ (hlam 0) hG h m
    rw [hL]
    calc _ ≤ Real.exp (2 * h ^ 2 * B ^ 2 * ∑ j, lam' j + 2 * lam 0 * h ^ 2 * B ^ 2) :=
          exp_moment_chain (fun y => poisPMF_nonneg (hlam 0) y) hin hout hsum
      _ = Real.exp (2 * h ^ 2 * B ^ 2 * ∑ i, lam i) := by
          congr 1
          rw [Fin.sum_univ_succ]
          simp only [hlam'_def]
          ring

/-- `rs_abs_poisPiExp_sub_le` on `Fin k`, by induction on `k`. -/
theorem abs_poisPiExp_sub_le_fin : ∀ (k : ℕ) {lam lam' : Fin k → ℝ} (_hlam : ∀ i, 0 ≤ lam i)
    (_hlam' : ∀ i, 0 ≤ lam' i) {B : ℝ} (_hB : 0 ≤ B) {f : (Fin k → ℕ) → ℝ}
    (_hf : EdgeLip B f),
    |poisPiExp lam f - poisPiExp lam' f| ≤ B * ∑ i, |lam i - lam' i|
  | 0, lam, lam', _, _, B, _, f, _ => by
    rw [poisPiExp_fin_zero lam f default, poisPiExp_fin_zero lam' f default]
    simp
  | k + 1, lam, lam', hlam, hlam', B, hB, f, hf => by
    set l1 : Fin k → ℝ := fun j => lam j.succ with hl1_def
    set l2 : Fin k → ℝ := fun j => lam' j.succ with hl2_def
    have hl1 : ∀ j, 0 ≤ l1 j := fun j => hlam j.succ
    have hl2 : ∀ j, 0 ≤ l2 j := fun j => hlam' j.succ
    have hfy : ∀ y, EdgeLip B (fun z : Fin k → ℕ => f (Fin.cons y z)) := edgeLip_cons hf
    set G : ℕ → ℝ := fun y => poisPiExp l1 (fun z => f (Fin.cons y z)) with hG_def
    set G' : ℕ → ℝ := fun y => poisPiExp l2 (fun z => f (Fin.cons y z)) with hG'_def
    have hG : ∀ y, |G (y + 1) - G y| ≤ B := fun y =>
      abs_poisPiExp_sub_le_of_abs_le hl1 (edgeLip_summable_id hl1 (hfy (y + 1)))
        (edgeLip_summable_id hl1 (hfy y)) (fun z => edgeLip_cons_succ hf y z)
    have hG' : ∀ y, |G' (y + 1) - G' y| ≤ B := fun y =>
      abs_poisPiExp_sub_le_of_abs_le hl2 (edgeLip_summable_id hl2 (hfy (y + 1)))
        (edgeLip_summable_id hl2 (hfy y)) (fun z => edgeLip_cons_succ hf y z)
    have hm : poisPiExp lam f = poisExp (lam 0) G :=
      poisPiExp_cons (edgeLip_summable_id hlam hf)
    have hm' : poisPiExp lam' f = poisExp (lam' 0) G' :=
      poisPiExp_cons (edgeLip_summable_id hlam' hf)
    have h1 : |poisExp (lam 0) G - poisExp (lam' 0) G| ≤ B * |lam 0 - lam' 0| :=
      rs_abs_poisExp_sub_le (hlam 0) (hlam' 0) hG
    have h2 : |poisExp (lam' 0) G - poisExp (lam' 0) G'| ≤ B * ∑ j, |l1 j - l2 j| :=
      abs_poisExp_sub_le_of_abs_le (hlam' 0) (summable_poisPMF_mul_of_succ (hlam' 0) hG)
        (summable_poisPMF_mul_of_succ (hlam' 0) hG')
        (fun y => abs_poisPiExp_sub_le_fin k hl1 hl2 hB (hfy y))
    rw [hm, hm']
    calc |poisExp (lam 0) G - poisExp (lam' 0) G'|
        ≤ |poisExp (lam 0) G - poisExp (lam' 0) G| +
            |poisExp (lam' 0) G - poisExp (lam' 0) G'| := abs_sub_le _ _ _
      _ ≤ B * |lam 0 - lam' 0| + B * ∑ j, |l1 j - l2 j| := add_le_add h1 h2
      _ = B * ∑ i, |lam i - lam' i| := by rw [Fin.sum_univ_succ]; ring

/-- `rs_label_exp_sub_le`, by induction on `n`. -/
theorem label_exp_sub_le_fin {S : Type*} [Fintype S] : ∀ (n : ℕ) {p : Fin n → S → ℝ}
    (_hp0 : ∀ v a, 0 ≤ p v a) (_hp1 : ∀ v, ∑ a, p v a = 1) {c : ℝ}
    {Φ : (Fin n → S) → ℝ} (_hΦ : BddDiff c Φ) (h : ℝ),
    ∑ ξ, (∏ v, p v (ξ v)) * Real.exp (h * (Φ ξ - ∑ ξ', (∏ v, p v (ξ' v)) * Φ ξ')) ≤
      Real.exp (n * h ^ 2 * c ^ 2 / 2)
  | 0, p, _, _, c, Φ, _, h => by
    simp
  | n + 1, p, hp0, hp1, c, Φ, hΦ, h => by
    set P' : (Fin n → S) → ℝ := fun z => ∏ v : Fin n, p v.succ (z v) with hP'_def
    have hsplit : ∀ F : (Fin (n + 1) → S) → ℝ, ∑ ξ, F ξ = ∑ a, ∑ z, F (Fin.cons a z) := by
      intro F
      rw [← (Fin.consEquiv fun _ => S).sum_comp F, Fintype.sum_prod_type]
      rfl
    have hP : ∀ a (z : Fin n → S),
        ∏ v, p v ((Fin.cons a z : Fin (n + 1) → S) v) = p 0 a * P' z := by
      intro a z
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, hP'_def]
    set Ψ : S → ℝ := fun a => ∑ z, P' z * Φ (Fin.cons a z) with hΨ_def
    have hmean : ∑ ξ', (∏ v, p v (ξ' v)) * Φ ξ' = ∑ a, p 0 a * Ψ a := by
      rw [hsplit]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hΨ_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [hP]; ring
    have hP'0 : ∀ z, 0 ≤ P' z := fun z => Finset.prod_nonneg fun v _ => hp0 v.succ (z v)
    have hP'1 : ∑ z, P' z = 1 := by
      rw [hP'_def, ← Fintype.prod_sum (fun (v : Fin n) (a : S) => p v.succ a)]
      simp [hp1]
    have hΦ0 : ∀ a b (z : Fin n → S), |Φ (Fin.cons a z) - Φ (Fin.cons b z)| ≤ c := by
      intro a b z
      refine hΦ (Fin.cons b z) (Fin.cons a z) 0 (fun w hw => ?_)
      cases w using Fin.cases with
      | zero => exact absurd rfl hw
      | succ w => simp
    have hΨc : ∀ a b, |Ψ a - Ψ b| ≤ c := by
      intro a b
      have he : Ψ a - Ψ b = ∑ z, P' z * (Φ (Fin.cons a z) - Φ (Fin.cons b z)) := by
        rw [hΨ_def, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun z _ => ?_
        ring
      rw [he]
      calc |∑ z, P' z * (Φ (Fin.cons a z) - Φ (Fin.cons b z))|
          ≤ ∑ z, |P' z * (Φ (Fin.cons a z) - Φ (Fin.cons b z))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ z, P' z * c := by
            refine Finset.sum_le_sum fun z _ => ?_
            rw [abs_mul, abs_of_nonneg (hP'0 z)]
            exact mul_le_mul_of_nonneg_left (hΦ0 a b z) (hP'0 z)
        _ = c := by rw [← Finset.sum_mul, hP'1, one_mul]
    have hΦa : ∀ a, BddDiff c (fun z : Fin n → S => Φ (Fin.cons a z)) := by
      intro a z z' v hv
      refine hΦ (Fin.cons a z) (Fin.cons a z') v.succ (fun w hw => ?_)
      cases w using Fin.cases with
      | zero => simp
      | succ w =>
        simp only [Fin.cons_succ]
        exact hv w (fun hc => hw (by rw [hc]))
    have hin : ∀ a, ∑ z, P' z * Real.exp (h * (Φ (Fin.cons a z) - Ψ a)) ≤
        Real.exp (n * h ^ 2 * c ^ 2 / 2) := fun a =>
      label_exp_sub_le_fin n (p := fun v => p v.succ) (fun v => hp0 v.succ)
        (fun v => hp1 v.succ) (hΦa a) h
    have hout : ∑ a, p 0 a * Real.exp (h * (Ψ a - ∑ b, p 0 b * Ψ b)) ≤
        Real.exp (h ^ 2 * c ^ 2 / 2) :=
      rs_fin_exp_sub_le (hp0 0) (hp1 0) hΨc h
    rw [hmean, hsplit]
    set m := ∑ b, p 0 b * Ψ b with hm_def
    calc ∑ a, ∑ z, (∏ v, p v ((Fin.cons a z : Fin (n + 1) → S) v)) *
            Real.exp (h * (Φ (Fin.cons a z) - m))
        = ∑ a, p 0 a * Real.exp (h * (Ψ a - m)) *
            ∑ z, P' z * Real.exp (h * (Φ (Fin.cons a z) - Ψ a)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [hP, show h * (Φ (Fin.cons a z) - m) =
            h * (Ψ a - m) + h * (Φ (Fin.cons a z) - Ψ a) by ring, Real.exp_add]
          ring
      _ ≤ ∑ a, p 0 a * Real.exp (h * (Ψ a - m)) * Real.exp (n * h ^ 2 * c ^ 2 / 2) := by
          refine Finset.sum_le_sum fun a _ => ?_
          exact mul_le_mul_of_nonneg_left (hin a)
            (mul_nonneg (hp0 0 a) (Real.exp_pos _).le)
      _ = (∑ a, p 0 a * Real.exp (h * (Ψ a - m))) * Real.exp (n * h ^ 2 * c ^ 2 / 2) := by
          rw [Finset.sum_mul]
      _ ≤ Real.exp (h ^ 2 * c ^ 2 / 2) * Real.exp (n * h ^ 2 * c ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right hout (Real.exp_pos _).le
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * h ^ 2 * c ^ 2 / 2) := by
          rw [← Real.exp_add]; push_cast; ring_nf

end RSConcTensorAux

/-- **Edge-count martingale.** `E e^{h(f(N) - E f)} ≤ e^{2h²B² ∑_i lam_i}` for independent
`N_i ∼ Pois(lam_i)`, `f` with `B`-bounded increments and `|h| B ≤ 1`. -/
theorem rs_poisPiExp_exp_sub_le {ι : Type*} [Fintype ι] {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    {B : ℝ} (hB : 0 ≤ B) {f : (ι → ℕ) → ℝ} (hf : EdgeLip B f) {h : ℝ} (hh : |h| * B ≤ 1) :
    poisPiExp lam (fun N => Real.exp (h * (f N - poisPiExp lam f))) ≤
      Real.exp (2 * h ^ 2 * B ^ 2 * ∑ i, lam i) := by
  let e := Fintype.equivFin ι
  have H := RSConcTensorAux.poisPiExp_exp_sub_le_fin (Fintype.card ι)
    (lam := fun k => lam (e.symm k)) (fun k => hlam _) hB
    (RSConcTensorAux.edgeLip_comp_equiv e hf) hh
  have hs : ∑ k, lam (e.symm k) = ∑ i, lam i := Equiv.sum_comp e.symm lam
  rw [hs] at H
  rw [RSConcTensorAux.poisPiExp_equiv e lam f, RSConcTensorAux.poisPiExp_equiv e lam]
  exact H

/-- **Coupling by superposition.** `|E_{lam} f - E_{lam'} f| ≤ B ∑_i |lam_i - lam'_i|`. -/
theorem rs_abs_poisPiExp_sub_le {ι : Type*} [Fintype ι] {lam lam' : ι → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hlam' : ∀ i, 0 ≤ lam' i) {B : ℝ} (hB : 0 ≤ B)
    {f : (ι → ℕ) → ℝ} (hf : EdgeLip B f) :
    |poisPiExp lam f - poisPiExp lam' f| ≤ B * ∑ i, |lam i - lam' i| := by
  let e := Fintype.equivFin ι
  have H := RSConcTensorAux.abs_poisPiExp_sub_le_fin (Fintype.card ι)
    (lam := fun k => lam (e.symm k)) (lam' := fun k => lam' (e.symm k)) (fun k => hlam _)
    (fun k => hlam' _) hB
    (RSConcTensorAux.edgeLip_comp_equiv e hf)
  have hs : ∑ k, |lam (e.symm k) - lam' (e.symm k)| = ∑ i, |lam i - lam' i| :=
    Equiv.sum_comp e.symm (fun i => |lam i - lam' i|)
  rw [hs] at H
  rw [RSConcTensorAux.poisPiExp_equiv e lam f, RSConcTensorAux.poisPiExp_equiv e lam' f]
  exact H

/-- **Label martingale.** For independent labels `ξ_v ∼ p v` and `Φ` with `c`-bounded differences:
`E e^{h(Φ(ξ) - E Φ)} ≤ e^{n h² c²/2}`. -/
theorem rs_label_exp_sub_le {S : Type*} [Fintype S] {n : ℕ} {p : Fin n → S → ℝ}
    (hp0 : ∀ v a, 0 ≤ p v a) (hp1 : ∀ v, ∑ a, p v a = 1) {c : ℝ}
    {Φ : (Fin n → S) → ℝ} (hΦ : BddDiff c Φ) (h : ℝ) :
    ∑ ξ, (∏ v, p v (ξ v)) * Real.exp (h * (Φ ξ - ∑ ξ', (∏ v, p v (ξ' v)) * Φ ξ')) ≤
      Real.exp (n * h ^ 2 * c ^ 2 / 2) :=
  RSConcTensorAux.label_exp_sub_le_fin n hp0 hp1 hΦ h

end

end ERZeroFreeness
