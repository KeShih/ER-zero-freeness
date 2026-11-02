/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSPoisPi

/-!
# Appendix C, Lemma C.6: one-dimensional ingredients

Ingredients of the proof of Lemma C.6 (`lem:rs-conc`), with every conditional expectation replaced
by an explicit sum:

* `rs_edgeLip_abs_sub_le`, `rs_edgeLip_summable`: a function with `B`-bounded increments grows at
  most linearly in `m = ∑_i N_i`, so `φ(f(N))` is `P_lam`-summable whenever `|φ(y)| ≤ A e^{c|y|}`
  (the paper's "all exponential moments below are finite");
* `rs_poisExp_exp_sub_le`: for `X ∼ Pois(ϖ)` and `g` with increments `≤ B`, `|h| B ≤ 1`:
  `E e^{h(g(X) - E g(X))} ≤ e^{2ϖ h² B²}`;
* `rs_abs_poisExp_sub_le`: `|E g(X_a) - E g(X_{a'})| ≤ B |a - a'|` (the superposition coupling);
* `rs_fin_exp_sub_le`: for a finitely supported law and `g` with range `≤ c`:
  `E e^{h(g - Eg)} ≤ e^{h² c²/2}`.

## Proof

The auxiliary lemmas are in the namespace `RSConcOneDimAux`: `sym_exp_le`,
`hasSum_poisPMF_mul_exp`, `poisPMF_add`, `tsum_prod_eq_tsum_antidiagonal`, `abs_sub_le_of_succ`,
`summable_poisPMF_mul_of_abs_le`, `hasSum_poisPMF_prod_cosh`, `exp_add_exp_neg_sub_two_le` and
`summable_prod_mul_of_nonneg`.
* Growth: induct on `∑_i N_i`, stepping down one nonzero coordinate
  (`Finset.exists_ne_zero_of_sum_ne_zero`); summability from `rs_summable_poisPi_of_abs_le`.
* Symmetrization (`sym_exp_le`): Jensen by the tangent line `e^y ≥ 1 + y` gives
  `E e^{h(g(X) - Eg)} ≤ E_{X,X'} e^{h(g(X) - g(X'))} = E cosh(h(g(X) - g(X')))` (swap symmetry,
  `Equiv.prodComm`), then `|g(X) - g(X')| ≤ ω(X,X')` and monotonicity of `cosh` in `|·|`.
* Poisson: with `ω(k,l) = B|k - l|`, `E cosh(hB(X - X')) = e^{2ϖ(cosh(hB) - 1)}` (two Poisson
  generating functions, `HasSum.mul`), and `cosh y - 1 ≤ y²` for `|y| ≤ 1`.
* Coupling: for `a ≤ a' = a + b`, `Pois(a+b)(m) = ∑_{i+j=m} Pois(a)(i) Pois(b)(j)` (binomial
  theorem), so `E g(X_{a'}) - E g(X_a) = ∑_{i,j} Pois(a)(i) Pois(b)(j)(g(i+j) - g(i))`, bounded by
  `B E[Pois(b)] = Bb` (`poisExp_natCast`); `wlog a ≤ a'`.
* Finite labels: `ω ≡ c` and `cosh y ≤ e^{y²/2}` (`Real.cosh_le_exp_half_sq`).

## Implementation notes

`summable_prod_mul_of_nonneg` restates `Summable.mul_of_nonneg` (conclusion
`Summable fun x => f x.1 * g x.2`), and this file applies it only as
`have h := summable_prod_mul_of_nonneg …`, never against an expected type (such as an argument of
`HasSum.mul` or a `have h : Summable … :=` ascription): there the non-pattern unification problem
`?f x.1 * ?g x.2 =?= …` fails only after unfolding `Summable`/`HasSum`/`Tendsto`, at a cost of
about `10⁵` heartbeats per occurrence.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

namespace RSConcOneDimAux

/-- Summability of a product family of nonnegative summable families (pointwise hypotheses). -/
theorem summable_prod_mul_of_nonneg {α β : Type*} {f : α → ℝ} {g : β → ℝ} (hf : Summable f)
    (hg : Summable g) (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ b, 0 ≤ g b) :
    Summable fun x : α × β => f x.1 * g x.2 :=
  Summable.mul_of_nonneg hf hg hf0 hg0

/-- **Symmetrization.** `E e^{h(g - Eg)} ≤ E_{X,X'} cosh(h ω(X,X'))` for any `ω ≥ |g(·) - g(·)|`
(Jensen by the tangent line, then the swap symmetry of `(X, X')`). -/
theorem sym_exp_le {α : Type*} {μ : α → ℝ} (hμ0 : ∀ a, 0 ≤ μ a) (hμ1 : HasSum μ 1)
    {g : α → ℝ} {ω : α → α → ℝ} (hgω : ∀ a b, |g a - g b| ≤ ω a b) (h : ℝ)
    (hg : Summable fun a => μ a * g a)
    (hgp : Summable fun a => μ a * Real.exp (h * g a))
    (hgm : Summable fun a => μ a * Real.exp (-(h * g a)))
    (hω : Summable fun x : α × α => μ x.1 * μ x.2 * Real.cosh (h * ω x.1 x.2)) :
    ∑' a, μ a * Real.exp (h * (g a - ∑' b, μ b * g b)) ≤
      ∑' x : α × α, μ x.1 * μ x.2 * Real.cosh (h * ω x.1 x.2) := by
  set m := ∑' b, μ b * g b with hm
  -- Jensen via the tangent line `exp y ≥ 1 + y`
  have hJ : Real.exp (-(h * m)) ≤ ∑' b, μ b * Real.exp (-(h * g b)) := by
    have key : ∀ b, μ b * (Real.exp (-(h * m)) * (1 - h * (g b - m))) ≤
        μ b * Real.exp (-(h * g b)) := by
      intro b
      refine mul_le_mul_of_nonneg_left ?_ (hμ0 b)
      have h1 := Real.add_one_le_exp (-(h * (g b - m)))
      have h2 : Real.exp (-(h * g b)) =
          Real.exp (-(h * m)) * Real.exp (-(h * (g b - m))) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [h2]
      exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    have hL : HasSum (fun b => μ b * (Real.exp (-(h * m)) * (1 - h * (g b - m))))
        (Real.exp (-(h * m))) := by
      have h1 := hμ1.mul_left (Real.exp (-(h * m)) * (1 + h * m))
      have h2 := hg.hasSum.mul_left (Real.exp (-(h * m)) * h)
      have h3 := h1.sub h2
      have hfun : (fun i => Real.exp (-(h * m)) * (1 + h * m) * μ i -
          Real.exp (-(h * m)) * h * (μ i * g i)) =
          fun b => μ b * (Real.exp (-(h * m)) * (1 - h * (g b - m))) := by
        funext b; ring
      have hval : Real.exp (-(h * m)) * (1 + h * m) * 1 -
          Real.exp (-(h * m)) * h * ∑' b, μ b * g b = Real.exp (-(h * m)) := by
        rw [← hm]; ring
      rw [hfun, hval] at h3
      exact h3
    exact hasSum_le key hL hgm.hasSum
  have hpos : 0 ≤ ∑' a, μ a * Real.exp (h * g a) :=
    tsum_nonneg fun a => mul_nonneg (hμ0 a) (Real.exp_pos _).le
  have hLHS : ∑' a, μ a * Real.exp (h * (g a - m)) =
      Real.exp (-(h * m)) * ∑' a, μ a * Real.exp (h * g a) := by
    rw [← tsum_mul_left]
    congr 1; ext a
    rw [show h * (g a - m) = -(h * m) + h * g a by ring, Real.exp_add]
    ring
  have hprodS := summable_prod_mul_of_nonneg hgp hgm
    (fun a => mul_nonneg (hμ0 a) (Real.exp_pos _).le)
    (fun a => mul_nonneg (hμ0 a) (Real.exp_pos _).le)
  let E : α × α → ℝ := fun x => μ x.1 * μ x.2 * Real.exp (h * (g x.1 - g x.2))
  let E' : α × α → ℝ := fun x => μ x.1 * μ x.2 * Real.exp (-(h * (g x.1 - g x.2)))
  have hEeq : ∀ x : α × α,
      (μ x.1 * Real.exp (h * g x.1)) * (μ x.2 * Real.exp (-(h * g x.2))) = E x := by
    intro x
    simp only [E]
    rw [show h * (g x.1 - g x.2) = h * g x.1 + -(h * g x.2) by ring, Real.exp_add]
    ring
  have hprod : (∑' a, μ a * Real.exp (h * g a)) * (∑' b, μ b * Real.exp (-(h * g b))) =
      ∑' x, E x := by
    rw [hgp.tsum_mul_tsum hgm hprodS]
    exact tsum_congr hEeq
  have hEs : Summable E := hprodS.congr hEeq
  have hEE' : ∀ x, E (Equiv.prodComm α α x) = E' x := by
    intro x
    simp only [E, E', Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [show -(h * (g x.1 - g x.2)) = h * (g x.2 - g x.1) by ring]
    ring
  have hE's : Summable E' :=
    ((Equiv.prodComm α α).summable_iff.mpr hEs).congr hEE'
  have hswap : ∑' x, E' x = ∑' x, E x := by
    rw [← (Equiv.prodComm α α).tsum_eq E]
    exact (tsum_congr hEE').symm
  let C : α × α → ℝ := fun x => μ x.1 * μ x.2 * Real.cosh (h * (g x.1 - g x.2))
  have hCE : ∀ x, (E x + E' x) / 2 = C x := by
    intro x; simp only [C, E, E', Real.cosh_eq]; ring
  have hCs : Summable C := ((hEs.add hE's).div_const 2).congr hCE
  have hCsum : ∑' x, C x = ∑' x, E x := by
    rw [← tsum_congr hCE, tsum_div_const, hEs.tsum_add hE's, hswap]
    ring
  have hcmp : ∀ x, C x ≤ μ x.1 * μ x.2 * Real.cosh (h * ω x.1 x.2) := by
    intro x
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hμ0 _) (hμ0 _))
    have hω0 : 0 ≤ ω x.1 x.2 := (abs_nonneg _).trans (hgω _ _)
    rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_nonneg hω0]
    exact mul_le_mul_of_nonneg_left (hgω _ _) (abs_nonneg _)
  calc ∑' a, μ a * Real.exp (h * (g a - m))
      = Real.exp (-(h * m)) * ∑' a, μ a * Real.exp (h * g a) := hLHS
    _ ≤ (∑' b, μ b * Real.exp (-(h * g b))) * ∑' a, μ a * Real.exp (h * g a) :=
        mul_le_mul_of_nonneg_right hJ hpos
    _ = ∑' x, E x := by rw [mul_comm, hprod]
    _ = ∑' x, C x := hCsum.symm
    _ ≤ _ := hCs.tsum_le_tsum hcmp hω

/-- The exponential moment of a Poisson law: `E e^{cX} = e^{lam(e^c - 1)}`. -/
theorem hasSum_poisPMF_mul_exp {lam : ℝ} (hlam : 0 ≤ lam) (c : ℝ) :
    HasSum (fun k : ℕ => poisPMF lam k * Real.exp (c * k))
      (Real.exp (lam * (Real.exp c - 1))) := by
  have h := (hasSum_poisPMF (mul_nonneg hlam (Real.exp_pos c).le)).mul_left
    (Real.exp (lam * (Real.exp c - 1)))
  rw [mul_one] at h
  have hfun : (fun k : ℕ => poisPMF lam k * Real.exp (c * k)) =
      fun k => Real.exp (lam * (Real.exp c - 1)) * poisPMF (lam * Real.exp c) k := by
    funext k
    unfold poisPMF
    have h1 : Real.exp (c * k) = Real.exp c ^ k := by rw [← Real.exp_nat_mul, mul_comm]
    have h2 : Real.exp (lam * (Real.exp c - 1)) * Real.exp (-(lam * Real.exp c)) =
        Real.exp (-lam) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h1, mul_pow, ← h2]
    ring
  rw [hfun]
  exact h

/-- Domination by an exponential: `|φ k| ≤ A e^{ck}` makes `poisPMF lam · φ` summable. -/
theorem summable_poisPMF_mul_of_abs_le {lam : ℝ} (hlam : 0 ≤ lam) {φ : ℕ → ℝ} {A c : ℝ}
    (hφ : ∀ k, |φ k| ≤ A * Real.exp (c * k)) : Summable fun k => poisPMF lam k * φ k := by
  refine Summable.of_norm_bounded ((hasSum_poisPMF_mul_exp hlam c).summable.mul_left A)
    fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poisPMF_nonneg hlam k)]
  calc poisPMF lam k * |φ k| ≤ poisPMF lam k * (A * Real.exp (c * k)) :=
        mul_le_mul_of_nonneg_left (hφ k) (poisPMF_nonneg hlam k)
    _ = A * (poisPMF lam k * Real.exp (c * k)) := by ring

/-- Convolution identity `Pois(a+b) = Pois(a) * Pois(b)`. -/
theorem poisPMF_add (a b : ℝ) (m : ℕ) :
    poisPMF (a + b) m =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, poisPMF a x.1 * poisPMF b x.2 := by
  unfold poisPMF
  rw [(Commute.all a b).add_pow' m, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  subst hx
  rw [nsmul_eq_mul, Nat.cast_add_choose, neg_add, Real.exp_add]
  field_simp

/-- Regrouping a summable family on `ℕ × ℕ` along the antidiagonals. -/
theorem tsum_prod_eq_tsum_antidiagonal {F : ℕ × ℕ → ℝ} (hF : Summable F) :
    ∑' x : ℕ × ℕ, F x = ∑' m : ℕ, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, F x := by
  rw [← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd).tsum_eq]
  have hs : Summable fun c => F (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ) c) :=
    (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).summable_iff.mpr hF
  rw [hs.tsum_sigma' (fun m => (hasSum_fintype _).summable)]
  refine tsum_congr fun m => ?_
  rw [tsum_fintype]
  exact Finset.sum_coe_sort _ _

/-- Bounded increments give a Lipschitz bound: `|g k - g l| ≤ B |k - l|`. -/
theorem abs_sub_le_of_succ {B : ℝ} {g : ℕ → ℝ} (hg : ∀ k, |g (k + 1) - g k| ≤ B) (k l : ℕ) :
    |g k - g l| ≤ B * |(k : ℝ) - l| := by
  have key : ∀ l d : ℕ, |g (l + d) - g l| ≤ B * d := by
    intro l d
    induction d with
    | zero => simp
    | succ d ih =>
      calc |g (l + (d + 1)) - g l| = |(g (l + d + 1) - g (l + d)) + (g (l + d) - g l)| := by
            rw [← add_assoc]; ring_nf
        _ ≤ |g (l + d + 1) - g (l + d)| + |g (l + d) - g l| := abs_add_le _ _
        _ ≤ B + B * d := add_le_add (hg _) ih
        _ = B * ((d + 1 : ℕ) : ℝ) := by push_cast; ring
  rcases le_total l k with hlk | hkl
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hlk
    have : |((l + d : ℕ) : ℝ) - l| = d := by push_cast; simp
    rw [this]; exact key l d
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
    rw [abs_sub_comm, abs_sub_comm (k : ℝ)]
    have : |((k + d : ℕ) : ℝ) - k| = d := by push_cast; simp
    rw [this]; exact key k d

/-- `e^c + e^{-c} - 2 ≤ 2c²` for `|c| ≤ 1`. -/
theorem exp_add_exp_neg_sub_two_le {c : ℝ} (hc : |c| ≤ 1) :
    Real.exp c + Real.exp (-c) - 2 ≤ 2 * c ^ 2 := by
  have h1 := Real.abs_exp_sub_one_sub_id_le hc
  have h2 := Real.abs_exp_sub_one_sub_id_le (x := -c) (by rwa [abs_neg])
  rw [neg_sq] at h2
  have h1' := (abs_le.mp h1).2
  have h2' := (abs_le.mp h2).2
  linarith

/-- `E cosh(c (X - X')) = e^{lam(e^c - 1)} e^{lam(e^{-c} - 1)}` for independent
`X, X' ∼ Pois(lam)`. -/
theorem hasSum_poisPMF_prod_cosh {lam : ℝ} (hlam : 0 ≤ lam) (c : ℝ) :
    HasSum (fun x : ℕ × ℕ =>
        poisPMF lam x.1 * poisPMF lam x.2 * Real.cosh (c * ((x.1 : ℝ) - x.2)))
      (Real.exp (lam * (Real.exp c - 1)) * Real.exp (lam * (Real.exp (-c) - 1))) := by
  have H1 := hasSum_poisPMF_mul_exp hlam c
  have H2 := hasSum_poisPMF_mul_exp hlam (-c)
  have hnn : ∀ (c' : ℝ) (k : ℕ), 0 ≤ poisPMF lam k * Real.exp (c' * k) :=
    fun c' k => mul_nonneg (poisPMF_nonneg hlam k) (Real.exp_pos _).le
  have S12 := summable_prod_mul_of_nonneg H1.summable H2.summable (hnn c) (hnn (-c))
  have S21 := summable_prod_mul_of_nonneg H2.summable H1.summable (hnn (-c)) (hnn c)
  have P12 := H1.mul H2 S12
  have P21 := H2.mul H1 S21
  have H := (P12.add P21).mul_left (1 / 2)
  have hval : 1 / 2 * (Real.exp (lam * (Real.exp c - 1)) * Real.exp (lam * (Real.exp (-c) - 1)) +
      Real.exp (lam * (Real.exp (-c) - 1)) * Real.exp (lam * (Real.exp c - 1))) =
      Real.exp (lam * (Real.exp c - 1)) * Real.exp (lam * (Real.exp (-c) - 1)) := by ring
  rw [hval] at H
  refine H.congr_fun fun x => ?_
  obtain ⟨i, j⟩ := x
  dsimp only
  rw [Real.cosh_eq, show c * ((i : ℝ) - j) = c * i + -c * j by ring,
    show -(c * i + -c * j) = -c * i + c * j by ring, Real.exp_add, Real.exp_add]
  ring

end RSConcOneDimAux

open RSConcOneDimAux

/-- A function with `B`-bounded edge increments grows at most linearly. -/
theorem rs_edgeLip_abs_sub_le {ι : Type*} [Fintype ι] {B : ℝ} {f : (ι → ℕ) → ℝ}
    (hf : EdgeLip B f) (N : ι → ℕ) : |f N - f 0| ≤ B * ∑ i, (N i : ℝ) := by
  have key : ∀ s : ℕ, ∀ N : ι → ℕ, ∑ i, N i = s → |f N - f 0| ≤ B * s := by
    intro s
    induction s with
    | zero =>
      intro N hN
      have : N = 0 := by
        funext i
        exact (Finset.sum_eq_zero_iff.mp hN) i (Finset.mem_univ i)
      subst this; simp
    | succ s ih =>
      intro N hN
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero
        (by rw [hN]; exact Nat.succ_ne_zero s)
      set N₀ : ι → ℕ := fun j => if j = i then N i - 1 else N j with hN₀
      have hdecomp : ∀ j, N j = N₀ j + if j = i then 1 else 0 := by
        intro j
        by_cases hj : j = i
        · subst hj; simp only [N₀, if_true]; omega
        · simp [N₀, hj]
      have hN₀sum : ∑ j, N₀ j = s := by
        have h2 : ∑ j, N j = ∑ j, N₀ j + 1 := by
          rw [Finset.sum_congr rfl (fun j _ => hdecomp j), Finset.sum_add_distrib]
          simp
        omega
      have hstep : |f N - f N₀| ≤ B :=
        hf N₀ N i (fun j hj => by simp [N₀, hj]) (by simp only [N₀, if_true]; omega)
      have := ih N₀ hN₀sum
      calc |f N - f 0| = |(f N - f N₀) + (f N₀ - f 0)| := by ring_nf
        _ ≤ |f N - f N₀| + |f N₀ - f 0| := abs_add_le _ _
        _ ≤ B + B * s := add_le_add hstep this
        _ = B * ((s + 1 : ℕ) : ℝ) := by push_cast; ring
  have := key (∑ i, N i) N rfl
  rwa [Nat.cast_sum] at this

/-- Summability of `φ ∘ f` under a product Poisson law, for `f` with bounded increments and `φ` of
at most exponential growth. -/
theorem rs_edgeLip_summable {ι : Type*} [Fintype ι] {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    {B : ℝ} {f : (ι → ℕ) → ℝ} (hf : EdgeLip B f) {φ : ℝ → ℝ} {A c : ℝ}
    (hφ : ∀ y, |φ y| ≤ A * Real.exp (c * |y|)) :
    Summable fun N => poisPi lam N * φ (f N) := by
  have hA : 0 ≤ A := by
    have h0 := hφ 0
    rw [abs_zero, mul_zero, Real.exp_zero, mul_one] at h0
    exact (abs_nonneg _).trans h0
  refine rs_summable_poisPi_of_abs_le hlam (A := A * Real.exp (|c| * |f 0|))
    (c := Real.exp (|c| * |B|)) (Real.exp_pos _).le (fun N => ?_)
  have h1 := rs_edgeLip_abs_sub_le hf N
  rw [← Nat.cast_sum] at h1
  set m := ∑ i, N i with hm
  have hfN : |f N| ≤ |f 0| + |B| * m := by
    have h2 := abs_sub_abs_le_abs_sub (f N) (f 0)
    have h3 : B * m ≤ |B| * m := mul_le_mul_of_nonneg_right (le_abs_self B) (Nat.cast_nonneg m)
    linarith
  calc |φ (f N)| ≤ A * Real.exp (c * |f N|) := hφ _
    _ ≤ A * Real.exp (|c| * (|f 0| + |B| * m)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA
        calc c * |f N| ≤ |c| * |f N| :=
              mul_le_mul_of_nonneg_right (le_abs_self c) (abs_nonneg _)
          _ ≤ |c| * (|f 0| + |B| * m) := mul_le_mul_of_nonneg_left hfN (abs_nonneg c)
    _ = A * Real.exp (|c| * |f 0|) * Real.exp (|c| * |B|) ^ m := by
        rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- **One Poisson coordinate.** For `X ∼ Pois(ϖ)`, `g` with `|g(k+1) - g(k)| ≤ B` and `|h| B ≤ 1`:
`E e^{h(g(X) - E g(X))} ≤ e^{2ϖ h² B²}`. -/
theorem rs_poisExp_exp_sub_le {lam : ℝ} (hlam : 0 ≤ lam) {B : ℝ} {g : ℕ → ℝ}
    (hg : ∀ k, |g (k + 1) - g k| ≤ B) {h : ℝ} (hh : |h| * B ≤ 1) :
    poisExp lam (fun k => Real.exp (h * (g k - poisExp lam g))) ≤
      Real.exp (2 * lam * h ^ 2 * B ^ 2) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hg 0)
  have hgk : ∀ k : ℕ, |g k| ≤ |g 0| + B * k := by
    intro k
    have h1 := abs_sub_le_of_succ hg k 0
    rw [Nat.cast_zero, sub_zero, Nat.abs_cast] at h1
    have h2 := abs_sub_abs_le_abs_sub (g k) (g 0)
    linarith
  -- summability of the three one-dimensional families
  have hs_g : Summable fun k => poisPMF lam k * g k := by
    refine summable_poisPMF_mul_of_abs_le hlam (A := |g 0| + B) (c := 1) fun k => ?_
    have hk : (1 : ℝ) + k ≤ Real.exp (1 * k) := by
      rw [one_mul, add_comm]; exact Real.add_one_le_exp _
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hg0 : 0 ≤ |g 0| := abs_nonneg _
    calc |g k| ≤ |g 0| + B * k := hgk k
      _ ≤ (|g 0| + B) * (1 + k) := by nlinarith
      _ ≤ (|g 0| + B) * Real.exp (1 * k) := mul_le_mul_of_nonneg_left hk (by positivity)
  have hexp_bd : ∀ (y : ℝ) (k : ℕ), |y| ≤ |h| * |g k| →
      |Real.exp y| ≤ Real.exp (|h| * |g 0|) * Real.exp ((|h| * B) * k) := by
    intro y k hy
    rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add, Real.exp_le_exp]
    calc y ≤ |y| := le_abs_self y
      _ ≤ |h| * |g k| := hy
      _ ≤ |h| * (|g 0| + B * k) := mul_le_mul_of_nonneg_left (hgk k) (abs_nonneg h)
      _ = |h| * |g 0| + |h| * B * k := by ring
  have hs_p : Summable fun k => poisPMF lam k * Real.exp (h * g k) :=
    summable_poisPMF_mul_of_abs_le hlam fun k => hexp_bd _ k (by rw [abs_mul])
  have hs_m : Summable fun k => poisPMF lam k * Real.exp (-(h * g k)) :=
    summable_poisPMF_mul_of_abs_le hlam fun k => hexp_bd _ k (by rw [abs_neg, abs_mul])
  -- the symmetrized bound, evaluated with two Poisson generating functions
  set c := h * B with hc
  have hcabs : |c| ≤ 1 := by rw [hc, abs_mul, abs_of_nonneg hB]; exact hh
  have HC : HasSum (fun x : ℕ × ℕ => poisPMF lam x.1 * poisPMF lam x.2 *
      Real.cosh (h * (B * |(x.1 : ℝ) - x.2|)))
      (Real.exp (lam * (Real.exp c - 1)) * Real.exp (lam * (Real.exp (-c) - 1))) := by
    refine (hasSum_poisPMF_prod_cosh hlam c).congr_fun fun x => ?_
    congr 1
    rw [show h * (B * |(x.1 : ℝ) - x.2|) = c * |(x.1 : ℝ) - x.2| by rw [hc]; ring]
    rcases abs_choice ((x.1 : ℝ) - x.2) with hx | hx <;> rw [hx]
    rw [mul_neg, Real.cosh_neg]
  have key := sym_exp_le (poisPMF_nonneg hlam) (hasSum_poisPMF hlam)
    (ω := fun k l => B * |(k : ℝ) - l|) (fun k l => abs_sub_le_of_succ hg k l) h hs_g hs_p hs_m
    HC.summable
  calc poisExp lam (fun k => Real.exp (h * (g k - poisExp lam g)))
      ≤ _ := key
    _ = Real.exp (lam * (Real.exp c - 1)) * Real.exp (lam * (Real.exp (-c) - 1)) := HC.tsum_eq
    _ ≤ Real.exp (2 * lam * h ^ 2 * B ^ 2) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have h3 := mul_le_mul_of_nonneg_left (exp_add_exp_neg_sub_two_le hcabs) hlam
      have h4 : lam * c ^ 2 = lam * h ^ 2 * B ^ 2 := by rw [hc]; ring
      linarith

/-- **Superposition coupling, one coordinate.** `|E g(X_a) - E g(X_{a'})| ≤ B |a - a'|` for
`X_a ∼ Pois(a)` and `g` with increments bounded by `B`. -/
theorem rs_abs_poisExp_sub_le {a a' : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') {B : ℝ} {g : ℕ → ℝ}
    (hg : ∀ k, |g (k + 1) - g k| ≤ B) :
    |poisExp a g - poisExp a' g| ≤ B * |a - a'| := by
  wlog hle : a ≤ a' generalizing a a'
  · have := this ha' ha (not_le.mp hle).le
    rwa [abs_sub_comm, abs_sub_comm a]
  have hB : 0 ≤ B := (abs_nonneg _).trans (hg 0)
  set b := a' - a with hb
  have hb0 : 0 ≤ b := sub_nonneg.mpr hle
  have ha'eq : a' = a + b := by rw [hb]; ring
  have hgk : ∀ k : ℕ, |g k| ≤ |g 0| + B * k := by
    intro k
    have h1 := abs_sub_le_of_succ hg k 0
    rw [Nat.cast_zero, sub_zero, Nat.abs_cast] at h1
    have h2 := abs_sub_abs_le_abs_sub (g k) (g 0)
    linarith
  set C := |g 0| + B with hC
  have hg0 : 0 ≤ |g 0| := abs_nonneg _
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hexp1 : ∀ k : ℕ, (1 : ℝ) + k ≤ Real.exp (1 * k) := fun k => by
    rw [one_mul, add_comm]; exact Real.add_one_le_exp _
  have hbd : ∀ i j : ℕ, |g (i + j)| ≤ C * (Real.exp (1 * i) * Real.exp (1 * j)) ∧
      |g i| ≤ C * (Real.exp (1 * i) * Real.exp (1 * j)) := by
    intro i j
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hprod : (1 + (i : ℝ)) * (1 + j) ≤ Real.exp (1 * i) * Real.exp (1 * j) :=
      mul_le_mul (hexp1 i) (hexp1 j) (by positivity) (Real.exp_pos _).le
    have hmain : |g 0| + B * ((i : ℝ) + j) ≤ C * ((1 + (i : ℝ)) * (1 + j)) := by
      have e1 : 0 ≤ |g 0| * i := mul_nonneg hg0 hi
      have e2 : 0 ≤ |g 0| * j := mul_nonneg hg0 hj
      have e3 : 0 ≤ |g 0| * i * j := mul_nonneg e1 hj
      have e4 : 0 ≤ B * i * j := mul_nonneg (mul_nonneg hB hi) hj
      rw [hC]; nlinarith
    have hfin := hmain.trans (mul_le_mul_of_nonneg_left hprod hC0)
    constructor
    · have := hgk (i + j); push_cast at this; linarith
    · have := hgk i
      have : B * (i : ℝ) ≤ B * ((i : ℝ) + j) := mul_le_mul_of_nonneg_left (by linarith) hB
      linarith
  -- the dominating family
  have HA := hasSum_poisPMF_mul_exp ha 1
  have HB := hasSum_poisPMF_mul_exp hb0 1
  have hD := summable_prod_mul_of_nonneg HA.summable HB.summable
      (fun k => mul_nonneg (poisPMF_nonneg ha k) (Real.exp_pos _).le)
      (fun k => mul_nonneg (poisPMF_nonneg hb0 k) (Real.exp_pos _).le)
  have hD' := hD.mul_left C
  have hμ0 : ∀ x : ℕ × ℕ, 0 ≤ poisPMF a x.1 * poisPMF b x.2 :=
    fun x => mul_nonneg (poisPMF_nonneg ha _) (poisPMF_nonneg hb0 _)
  have hdom : ∀ (x : ℕ × ℕ) (y : ℝ), |y| ≤ C * (Real.exp (1 * x.1) * Real.exp (1 * x.2)) →
      ‖poisPMF a x.1 * poisPMF b x.2 * y‖ ≤
        C * ((poisPMF a x.1 * Real.exp (1 * x.1)) * (poisPMF b x.2 * Real.exp (1 * x.2))) := by
    intro x y hy
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hμ0 x)]
    calc poisPMF a x.1 * poisPMF b x.2 * |y|
        ≤ poisPMF a x.1 * poisPMF b x.2 * (C * (Real.exp (1 * x.1) * Real.exp (1 * x.2))) :=
          mul_le_mul_of_nonneg_left hy (hμ0 x)
      _ = _ := by ring
  let F : ℕ × ℕ → ℝ := fun x => poisPMF a x.1 * poisPMF b x.2 * g (x.1 + x.2)
  let G : ℕ × ℕ → ℝ := fun x => poisPMF a x.1 * poisPMF b x.2 * g x.1
  let H : ℕ × ℕ → ℝ := fun x => poisPMF a x.1 * poisPMF b x.2 * (B * x.2)
  have hFs : Summable F := Summable.of_norm_bounded hD' fun x => hdom x _ (hbd x.1 x.2).1
  have hGs : Summable G := Summable.of_norm_bounded hD' fun x => hdom x _ (hbd x.1 x.2).2
  have hNat : HasSum (fun j : ℕ => poisPMF b j * (j : ℝ)) b := by
    have hs : Summable fun j : ℕ => poisPMF b j * (j : ℝ) := by
      simpa using summable_poisPMF_mul_pow hb0 1
    have h1 := hs.hasSum
    have h2 : ∑' j : ℕ, poisPMF b j * (j : ℝ) = b := poisExp_natCast hb0
    rwa [h2] at h1
  have hHas : HasSum H (B * b) := by
    have hS := summable_prod_mul_of_nonneg (hasSum_poisPMF ha).summable hNat.summable
      (poisPMF_nonneg ha) (fun j => mul_nonneg (poisPMF_nonneg hb0 j) (Nat.cast_nonneg j))
    have h1 := (hasSum_poisPMF ha).mul hNat hS
    have h2 := h1.mul_left B
    rw [one_mul] at h2
    refine h2.congr_fun fun x => ?_
    simp only [H]
    ring
  have hga : Summable fun i => poisPMF a i * g i := by
    refine summable_poisPMF_mul_of_abs_le ha (A := C) (c := 1) fun k => ?_
    have := (hbd k 0).2
    simpa using this
  have hEa : poisExp a g = ∑' x, G x := by
    have hprod : Summable fun x : ℕ × ℕ => (poisPMF a x.1 * g x.1) * poisPMF b x.2 :=
      hGs.congr fun x => by simp only [G]; ring
    calc poisExp a g = (∑' i, poisPMF a i * g i) * ∑' j, poisPMF b j := by
          rw [(hasSum_poisPMF hb0).tsum_eq, mul_one]; rfl
      _ = ∑' x : ℕ × ℕ, (poisPMF a x.1 * g x.1) * poisPMF b x.2 :=
          hga.tsum_mul_tsum (hasSum_poisPMF hb0).summable hprod
      _ = ∑' x, G x := tsum_congr fun x => by simp only [G]; ring
  have hEa' : poisExp a' g = ∑' x, F x := by
    rw [tsum_prod_eq_tsum_antidiagonal hFs]
    unfold poisExp
    refine tsum_congr fun m => ?_
    rw [ha'eq, poisPMF_add, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    simp only [F, hx]
  have hFG : ∀ x, |F x - G x| ≤ H x := by
    intro x
    simp only [F, G, H]
    rw [← mul_sub, abs_mul, abs_of_nonneg (hμ0 x)]
    refine mul_le_mul_of_nonneg_left ?_ (hμ0 x)
    have := abs_sub_le_of_succ hg (x.1 + x.2) x.1
    rwa [Nat.cast_add, add_sub_cancel_left, Nat.abs_cast] at this
  have hdiff_s : Summable fun x => F x - G x := hFs.sub hGs
  have hsub : poisExp a' g - poisExp a g = ∑' x, (F x - G x) := by
    rw [hEa', hEa, hFs.tsum_sub hGs]
  have habs : |∑' x, (F x - G x)| ≤ ∑' x, H x := by
    rw [abs_le]
    constructor
    · rw [← tsum_neg]
      exact hHas.summable.neg.tsum_le_tsum (fun x => (abs_le.mp (hFG x)).1) hdiff_s
    · exact hdiff_s.tsum_le_tsum (fun x => (le_abs_self _).trans (hFG x)) hHas.summable
  rw [abs_sub_comm, hsub, abs_sub_comm a a', abs_of_nonneg hb0]
  calc |∑' x, (F x - G x)| ≤ ∑' x, H x := habs
    _ = B * b := hHas.tsum_eq

/-- **One finite label.** For a probability vector `p` and `g` with oscillation `≤ c`:
`E_p e^{h(g - E_p g)} ≤ e^{h² c²/2}`. -/
theorem rs_fin_exp_sub_le {S : Type*} [Fintype S] {p : S → ℝ} (hp0 : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a, p a = 1) {g : S → ℝ} {c : ℝ} (hg : ∀ a b, |g a - g b| ≤ c) (h : ℝ) :
    ∑ a, p a * Real.exp (h * (g a - ∑ b, p b * g b)) ≤ Real.exp (h ^ 2 * c ^ 2 / 2) := by
  have hμ1 : HasSum p 1 := by rw [← hp1]; exact hasSum_fintype p
  have key := sym_exp_le hp0 hμ1 (ω := fun _ _ => c) hg h Summable.of_finite Summable.of_finite
    Summable.of_finite Summable.of_finite
  simp only [tsum_fintype] at key
  refine key.trans ?_
  rw [← Finset.sum_mul, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, hp1, one_mul]
  calc Real.cosh (h * c) ≤ Real.exp ((h * c) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
    _ = Real.exp (h ^ 2 * c ^ 2 / 2) := by rw [mul_pow]

end

end ERZeroFreeness
