/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs

/-!
# Exponential moments of the empirical relative entropy (Theorem 5.3, `thm:multinomial-moment`)

`exists_sum_exp_empKL_le`: for `θ ∈ [0,1)` and `k` colours there is `C(θ, k)` with
`∑_{f : ι → κ} exp(θ n D(emp f ‖ u)) ≤ C k^n` for `n = |ι|`, `k = |κ|`, i.e.
`E exp(θ n D(X/n ‖ u)) ≤ C` for `X ∼ Mult(n, u)`, uniformly in `n`.  This is Theorem 5.3 for the
uniform vector `p = u`, the only case used, with some constant `C(θ, k)` in place of Agrawal's
sharp `(1-θ)^{-(k-1)}`; only uniformity in `n` is needed.  The file also proves
`exists_empKL_ge_of_not_balanced`: colourings outside the balanced window `balanced q n δ` have
`D(emp σ ‖ u)` bounded below by a positive constant.  Together with the moment bound this
replaces Hoeffding's inequality for the colour counts (Lemma 5.1 and Appendix C).

Proof.  Binomial case: let `kl(a,p) = a log(a/p) + (1-a) log((1-a)/(1-p))`.  The change of
measure `binom(n,x)p^x(1-p)^{n-x} = binom(n,x)a^x(1-a)^{n-x}·(p/a)^x((1-p)/(1-a))^{n-x}`
gives `P[X ≥ an] ≤ e^{-n kl(a,p)}` for `a ≥ p`, and symmetrically `P[X ≤ an] ≤ e^{-n kl(a,p)}`
for `a ≤ p`.  Applied at the least `s ≥ np` (resp. the largest `s < np`) with
`n kl(s/n, p) ≥ y`, this gives `P[n kl(X/n,p) ≥ y] ≤ 2e^{-y}`.  A layer-cake sum over integer
levels then gives
`E e^{θ n kl} ≤ 1 + ∑_j (e^{θ(j+1)} - e^{θj}) 2e^{-j} ≤ 1 + 2(e^θ - 1)/(1 - e^{θ-1}) = C_bin`.
General `κ`: induct on `|κ|`, splitting off one colour `c`: with `S = f⁻¹(c)`,
`D(emp f) = kl(|S|/n, 1/k) + (1-|S|/n) D(emp f|_{Sᶜ})` (chain rule), and `f|_{Sᶜ}` is uniform
into `κ \ {c}`; summing first over `f|_{Sᶜ}` (induction hypothesis on `ι = Sᶜ`) and then over
`S` (`Finset.sum_powerset_apply_card`) gives `C_k ≤ C_bin C_{k-1}`.
For `exists_empKL_ge_of_not_balanced`, write `D(α ‖ u) = q⁻¹ ∑_c klFun(q α_c)` with
`klFun x = x log x + 1 - x ≥ 0` and keep the term of a colour `i` with `|α_i - 1/q| > δ`; by
convexity, `klFun x ≥ min (klFun (1+ε)) (klFun (1-ε)) > 0` for `|x - 1| ≥ ε = min(qδ, 1/2)`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-! ### Elementary facts about `fiberCard` and `empKL` -/

private lemma mn_fiberCard_le {ι κ : Type*} [Fintype ι] (f : ι → κ) (c : κ) :
    fiberCard f c ≤ Fintype.card ι := by
  unfold fiberCard
  exact Finset.card_filter_le _ _

private lemma mn_sum_fiberCard {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ) :
    ∑ c : κ, fiberCard f c = Fintype.card ι := by
  unfold fiberCard
  rw [← Finset.card_univ (α := ι)]
  exact (Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (f x))).symm

private lemma mn_natCast_mul_div_cancel {N n : ℕ} (h : N ≤ n) : (n : ℝ) * ((N : ℝ) / n) = N := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.le_zero.mp h]
  · have : (n : ℝ) ≠ 0 := by positivity
    field_simp

private lemma mn_card_mul_empKL {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ) :
    (Fintype.card ι : ℝ) * empKL f = ∑ c : κ, (fiberCard f c : ℝ) *
      Real.log ((Fintype.card κ : ℝ) * fiberCard f c / Fintype.card ι) := by
  unfold empKL
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← mul_assoc, mn_natCast_mul_div_cancel (mn_fiberCard_le f c)]

private lemma mn_empKL_eq_klFun {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ)
    (hn : 0 < Fintype.card ι) :
    empKL f = ((Fintype.card κ : ℝ))⁻¹ * ∑ c : κ, InformationTheory.klFun
      ((Fintype.card κ : ℝ) * fiberCard f c / Fintype.card ι) := by
  have hK : 0 < Fintype.card κ := by
    obtain ⟨i⟩ := Fintype.card_pos_iff.mp hn
    exact Fintype.card_pos_iff.mpr ⟨f i⟩
  have hsum : ∑ c : κ, (fiberCard f c : ℝ) = Fintype.card ι := by
    exact_mod_cast mn_sum_fiberCard f
  have hK' : (Fintype.card κ : ℝ) ≠ 0 := by positivity
  have hn' : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  unfold empKL
  simp only [InformationTheory.klFun]
  rw [Finset.mul_sum]
  have key : ∀ c : κ, ((Fintype.card κ : ℝ))⁻¹ *
      ((Fintype.card κ : ℝ) * fiberCard f c / Fintype.card ι *
        Real.log ((Fintype.card κ : ℝ) * fiberCard f c / Fintype.card ι) + 1 -
        (Fintype.card κ : ℝ) * fiberCard f c / Fintype.card ι) =
      (fiberCard f c : ℝ) / Fintype.card ι *
        Real.log ((Fintype.card κ : ℝ) * fiberCard f c / Fintype.card ι) +
      (((Fintype.card κ : ℝ))⁻¹ - (fiberCard f c : ℝ) / Fintype.card ι) := by
    intro c
    field_simp
    ring
  rw [Finset.sum_congr rfl fun c _ => key c, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div, hsum]
  simp [hK', hn']

/-- `D(emp f ‖ u) ≥ 0`. -/
theorem empKL_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ) : 0 ≤ empKL f := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
  · unfold empKL
    simp [h]
  · rw [mn_empKL_eq_klFun f h]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun c _ => ?_)
    exact InformationTheory.klFun_nonneg (by positivity)

/-! ### The binomial case: Chernoff bounds and the exponential moment of `n · kl` -/

/-- `n · kl(s/n ‖ p)`, the binary relative entropy written with counts. -/
private def mnKl (n s : ℕ) (p : ℝ) : ℝ :=
  (s : ℝ) * Real.log ((s : ℝ) / ((n : ℝ) * p)) +
    ((n : ℝ) - s) * Real.log (((n : ℝ) - s) / ((n : ℝ) * (1 - p)))

private lemma mn_upper_aux {p a : ℝ} (hp : 0 ≤ p) (hpa : p ≤ a) (ha1 : a ≤ 1) {n s₀ s : ℕ}
    (h0 : s₀ ≤ s) (hs : s ≤ n) :
    p ^ s * (1 - p) ^ (n - s) * (a ^ s₀ * (1 - a) ^ (n - s₀)) ≤
      a ^ s * (1 - a) ^ (n - s) * (p ^ s₀ * (1 - p) ^ (n - s₀)) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h0
  have e : n - s₀ = (n - (s₀ + t)) + t := by omega
  rw [e]
  have ha0 : 0 ≤ a := hp.trans hpa
  have hp1 : 0 ≤ 1 - p := by linarith
  have ha1' : 0 ≤ 1 - a := by linarith
  have h1 : p * (1 - a) ≤ a * (1 - p) := by nlinarith
  have h2 : p ^ t * (1 - a) ^ t ≤ a ^ t * (1 - p) ^ t := by
    rw [← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hp ha1') h1 t
  have hF : 0 ≤ p ^ s₀ * a ^ s₀ * (1 - p) ^ (n - (s₀ + t)) * (1 - a) ^ (n - (s₀ + t)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hp _) (pow_nonneg ha0 _)) (pow_nonneg hp1 _))
      (pow_nonneg ha1' _)
  calc p ^ (s₀ + t) * (1 - p) ^ (n - (s₀ + t)) * (a ^ s₀ * (1 - a) ^ (n - (s₀ + t) + t))
      = (p ^ s₀ * a ^ s₀ * (1 - p) ^ (n - (s₀ + t)) * (1 - a) ^ (n - (s₀ + t))) *
          (p ^ t * (1 - a) ^ t) := by ring
    _ ≤ (p ^ s₀ * a ^ s₀ * (1 - p) ^ (n - (s₀ + t)) * (1 - a) ^ (n - (s₀ + t))) *
          (a ^ t * (1 - p) ^ t) := mul_le_mul_of_nonneg_left h2 hF
    _ = a ^ (s₀ + t) * (1 - a) ^ (n - (s₀ + t)) * (p ^ s₀ * (1 - p) ^ (n - (s₀ + t) + t)) := by
        ring

private lemma mn_lower_aux {p a : ℝ} (ha : 0 ≤ a) (hap : a ≤ p) (hp1 : p ≤ 1) {n s₁ s : ℕ}
    (h0 : s ≤ s₁) (hs : s₁ ≤ n) :
    p ^ s * (1 - p) ^ (n - s) * (a ^ s₁ * (1 - a) ^ (n - s₁)) ≤
      a ^ s * (1 - a) ^ (n - s) * (p ^ s₁ * (1 - p) ^ (n - s₁)) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h0
  have e : n - s = (n - (s + t)) + t := by omega
  rw [e]
  have hp0 : 0 ≤ p := ha.trans hap
  have hp1' : 0 ≤ 1 - p := by linarith
  have ha1' : 0 ≤ 1 - a := by linarith
  have h1 : a * (1 - p) ≤ p * (1 - a) := by nlinarith
  have h2 : a ^ t * (1 - p) ^ t ≤ p ^ t * (1 - a) ^ t := by
    rw [← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg ha hp1') h1 t
  have hF : 0 ≤ p ^ s * a ^ s * (1 - p) ^ (n - (s + t)) * (1 - a) ^ (n - (s + t)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hp0 _) (pow_nonneg ha _)) (pow_nonneg hp1' _))
      (pow_nonneg ha1' _)
  calc p ^ s * (1 - p) ^ (n - (s + t) + t) * (a ^ (s + t) * (1 - a) ^ (n - (s + t)))
      = (p ^ s * a ^ s * (1 - p) ^ (n - (s + t)) * (1 - a) ^ (n - (s + t))) *
          (a ^ t * (1 - p) ^ t) := by ring
    _ ≤ (p ^ s * a ^ s * (1 - p) ^ (n - (s + t)) * (1 - a) ^ (n - (s + t))) *
          (p ^ t * (1 - a) ^ t) := mul_le_mul_of_nonneg_left h2 hF
    _ = a ^ s * (1 - a) ^ (n - (s + t) + t) * (p ^ (s + t) * (1 - p) ^ (n - (s + t))) := by
        ring

private lemma mn_binom_sum_one (n : ℕ) (a : ℝ) :
    ∑ s ∈ Finset.range (n + 1), (n.choose s : ℝ) * (a ^ s * (1 - a) ^ (n - s)) = 1 := by
  have h := add_pow a (1 - a) n
  rw [add_sub_cancel, one_pow] at h
  exact (Finset.sum_congr rfl fun s _ => by ring).trans h.symm

/-- Change of measure: a pointwise likelihood-ratio bound on `T` bounds the binomial mass of
`T`. -/
private lemma mn_tilt_sum {n : ℕ} {p a A B : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hA : 0 < A)
    (hB : 0 ≤ B)
    (T : Finset ℕ) (hT : T ⊆ Finset.range (n + 1))
    (hpt : ∀ s ∈ T, p ^ s * (1 - p) ^ (n - s) * A ≤ a ^ s * (1 - a) ^ (n - s) * B) :
    ∑ s ∈ T, (n.choose s : ℝ) * p ^ s * (1 - p) ^ (n - s) ≤ B / A := by
  rw [le_div_iff₀ hA, Finset.sum_mul]
  calc ∑ s ∈ T, (n.choose s : ℝ) * p ^ s * (1 - p) ^ (n - s) * A
      ≤ ∑ s ∈ T, (n.choose s : ℝ) * (a ^ s * (1 - a) ^ (n - s)) * B := by
        refine Finset.sum_le_sum fun s hs => ?_
        have hc : (0 : ℝ) ≤ n.choose s := by positivity
        calc (n.choose s : ℝ) * p ^ s * (1 - p) ^ (n - s) * A
            = n.choose s * (p ^ s * (1 - p) ^ (n - s) * A) := by ring
          _ ≤ n.choose s * (a ^ s * (1 - a) ^ (n - s) * B) :=
              mul_le_mul_of_nonneg_left (hpt s hs) hc
          _ = _ := by ring
    _ ≤ ∑ s ∈ Finset.range (n + 1), (n.choose s : ℝ) * (a ^ s * (1 - a) ^ (n - s)) * B := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hT fun s _ _ => ?_
        have : 0 ≤ 1 - a := by linarith
        positivity
    _ = B := by rw [← Finset.sum_mul, mn_binom_sum_one, one_mul]

private lemma mn_exp_mul_log {x : ℝ} {m : ℕ} (h : m ≠ 0 → 0 < x) :
    Real.exp (m * Real.log x) = x ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [Real.exp_nat_mul, Real.exp_log (h hm.ne')]

private lemma mn_exp_mnKl {n s : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hs : s ≤ n) (hn : 0 < n) :
    Real.exp (mnKl n s p) * (p ^ s * (1 - p) ^ (n - s)) =
      ((s : ℝ) / n) ^ s * (1 - (s : ℝ) / n) ^ (n - s) := by
  unfold mnKl
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp1' : (0 : ℝ) < 1 - p := by linarith
  have hcast : (n : ℝ) - s = ((n - s : ℕ) : ℝ) := by rw [Nat.cast_sub hs]
  rw [hcast, Real.exp_add, mn_exp_mul_log, mn_exp_mul_log]
  · calc ((s : ℝ) / (n * p)) ^ s * (((n - s : ℕ) : ℝ) / (n * (1 - p))) ^ (n - s) *
          (p ^ s * (1 - p) ^ (n - s))
        = ((s : ℝ) / (n * p) * p) ^ s *
            (((n - s : ℕ) : ℝ) / (n * (1 - p)) * (1 - p)) ^ (n - s) := by
          rw [mul_pow, mul_pow]; ring
      _ = ((s : ℝ) / n) ^ s * (1 - (s : ℝ) / n) ^ (n - s) := by
          congr 2
          · field_simp
          · rw [← hcast]; field_simp
  · intro h
    have : (0 : ℝ) < ((n - s : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
    positivity
  · intro h
    have : (0 : ℝ) < (s : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
    positivity

private lemma mn_tilt_ratio {n s₀ : ℕ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hs : s₀ ≤ n)
    (hn : 0 < n) :
    (p ^ s₀ * (1 - p) ^ (n - s₀)) / (((s₀ : ℝ) / n) ^ s₀ * (1 - (s₀ : ℝ) / n) ^ (n - s₀)) =
      Real.exp (-mnKl n s₀ p) := by
  rw [← mn_exp_mnKl hp0 hp1 hs hn, Real.exp_neg]
  have h1p : 0 < 1 - p := by linarith
  have hB1 : p ^ s₀ ≠ 0 := (pow_pos hp0 _).ne'
  have hB2 : (1 - p) ^ (n - s₀) ≠ 0 := (pow_pos h1p _).ne'
  have hE := (Real.exp_pos (mnKl n s₀ p)).ne'
  field_simp

private lemma mn_tilt_pos {n s₀ : ℕ} (hs : s₀ ≤ n) :
    0 < ((s₀ : ℝ) / n) ^ s₀ * (1 - (s₀ : ℝ) / n) ^ (n - s₀) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : s₀ = 0 := Nat.le_zero.mp hs
    simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply mul_pos
  · rcases Nat.eq_zero_or_pos s₀ with h | h
    · simp [h]
    · have : (0 : ℝ) < s₀ := by exact_mod_cast h
      positivity
  · rcases Nat.eq_zero_or_pos (n - s₀) with h | h
    · simp [h]
    · have : (s₀ : ℝ) < n := by exact_mod_cast (by omega : s₀ < n)
      have : (s₀ : ℝ) / n < 1 := (div_lt_one hn').mpr this
      have : 0 < 1 - (s₀ : ℝ) / n := by linarith
      positivity

/-- **Chernoff bound**, upper tail. -/
private lemma mn_chernoff_upper {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {n s₀ : ℕ} (hs₀ : s₀ ≤ n)
    (hps : (n : ℝ) * p ≤ s₀) :
    ∑ s ∈ (Finset.range (n + 1)).filter (fun s => s₀ ≤ s),
      (n.choose s : ℝ) * p ^ s * (1 - p) ^ (n - s) ≤ Real.exp (-mnKl n s₀ p) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : s₀ = 0 := Nat.le_zero.mp hs₀
    simp [mnKl]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpa : p ≤ (s₀ : ℝ) / n := by rw [le_div_iff₀ hn']; linarith
  have ha1 : (s₀ : ℝ) / n ≤ 1 := by rw [div_le_one hn']; exact_mod_cast hs₀
  rw [← mn_tilt_ratio hp0 hp1 hs₀ hn]
  refine mn_tilt_sum (hp0.le.trans hpa) ha1 (mn_tilt_pos hs₀) (by
      have : 0 < 1 - p := by linarith
      positivity) _ (Finset.filter_subset _ _) fun s hs => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hs
  exact mn_upper_aux hp0.le hpa ha1 hs.2 (by omega)

/-- **Chernoff bound**, lower tail. -/
private lemma mn_chernoff_lower {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {n s₁ : ℕ} (hs₁ : s₁ ≤ n)
    (hps : (s₁ : ℝ) ≤ n * p) :
    ∑ s ∈ (Finset.range (n + 1)).filter (fun s => s ≤ s₁),
      (n.choose s : ℝ) * p ^ s * (1 - p) ^ (n - s) ≤ Real.exp (-mnKl n s₁ p) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : s₁ = 0 := Nat.le_zero.mp hs₁
    simp [mnKl]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hap : (s₁ : ℝ) / n ≤ p := by rw [div_le_iff₀ hn']; linarith
  have ha0 : (0 : ℝ) ≤ (s₁ : ℝ) / n := by positivity
  rw [← mn_tilt_ratio hp0 hp1 hs₁ hn]
  refine mn_tilt_sum ha0 (hap.trans hp1.le) (mn_tilt_pos hs₁) (by
      have : 0 < 1 - p := by linarith
      positivity) _ (Finset.filter_subset _ _) fun s hs => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hs
  exact mn_lower_aux ha0 hap hp1.le hs.2 hs₁

/-- Two-sided tail bound `P[n kl(X/n, p) ≥ y] ≤ 2 e^{-y}`. -/
private lemma mn_tail {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) (y : ℝ) :
    ∑ s ∈ (Finset.range (n + 1)).filter (fun s => y ≤ mnKl n s p),
      (n.choose s : ℝ) * p ^ s * (1 - p) ^ (n - s) ≤ 2 * Real.exp (-y) := by
  set T := (Finset.range (n + 1)).filter (fun s => y ≤ mnKl n s p) with hT
  set P : ℕ → ℝ := fun s => (n.choose s : ℝ) * p ^ s * (1 - p) ^ (n - s) with hPdef
  have hP : ∀ s, 0 ≤ P s := fun s => by
    have : 0 ≤ 1 - p := by linarith
    positivity
  change ∑ s ∈ T, P s ≤ 2 * Real.exp (-y)
  rw [← Finset.sum_filter_add_sum_filter_not T (fun s : ℕ => (n : ℝ) * p ≤ (s : ℝ)), two_mul]
  apply add_le_add
  · set U := T.filter (fun s : ℕ => (n : ℝ) * p ≤ (s : ℝ)) with hU
    rcases U.eq_empty_or_nonempty with hUe | hUne
    · rw [hUe, Finset.sum_empty]; positivity
    · set s₀ := U.min' hUne
      have hs₀U : s₀ ∈ U := Finset.min'_mem U hUne
      simp only [hU, hT, Finset.mem_filter, Finset.mem_range] at hs₀U
      calc ∑ s ∈ U, P s
          ≤ ∑ s ∈ (Finset.range (n + 1)).filter (fun s => s₀ ≤ s), P s := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun s _ _ => hP s
            intro s hs
            have hmin : s₀ ≤ s := Finset.min'_le U s hs
            simp only [hU, hT, Finset.mem_filter, Finset.mem_range] at hs ⊢
            exact ⟨hs.1.1, hmin⟩
        _ ≤ Real.exp (-mnKl n s₀ p) :=
            mn_chernoff_upper hp0 hp1 (by omega) hs₀U.2
        _ ≤ Real.exp (-y) := Real.exp_le_exp.mpr (neg_le_neg hs₀U.1.2)
  · set L := T.filter (fun s : ℕ => ¬ (n : ℝ) * p ≤ (s : ℝ)) with hL
    rcases L.eq_empty_or_nonempty with hLe | hLne
    · rw [hLe, Finset.sum_empty]; positivity
    · set s₁ := L.max' hLne
      have hs₁L : s₁ ∈ L := Finset.max'_mem L hLne
      simp only [hL, hT, Finset.mem_filter, Finset.mem_range] at hs₁L
      calc ∑ s ∈ L, P s
          ≤ ∑ s ∈ (Finset.range (n + 1)).filter (fun s => s ≤ s₁), P s := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun s _ _ => hP s
            intro s hs
            have hmax : s ≤ s₁ := Finset.le_max' L s hs
            simp only [hL, hT, Finset.mem_filter, Finset.mem_range] at hs ⊢
            exact ⟨hs.1.1, hmax⟩
        _ ≤ Real.exp (-mnKl n s₁ p) :=
            mn_chernoff_lower hp0 hp1 (by omega) (le_of_lt (not_le.mp hs₁L.2))
        _ ≤ Real.exp (-y) := Real.exp_le_exp.mpr (neg_le_neg hs₁L.1.2)

/-- Pointwise layer-cake bound with integer levels. -/
private lemma mn_layer_pointwise {θ Y : ℝ} (hθ : 0 ≤ θ) {J : ℕ} (hYJ : Y < J) :
    Real.exp (θ * Y) ≤ 1 + ∑ j ∈ Finset.range J,
      (Real.exp (θ * ((j + 1 : ℕ) : ℝ)) - Real.exp (θ * (j : ℝ))) *
        (if (j : ℝ) ≤ Y then 1 else 0) := by
  rcases lt_or_ge Y 0 with hY | hY
  · have hz : ∀ j ∈ Finset.range J, (Real.exp (θ * ((j + 1 : ℕ) : ℝ)) - Real.exp (θ * (j : ℝ))) *
        (if (j : ℝ) ≤ Y then 1 else 0) = 0 := by
      intro j _
      have : ¬ ((j : ℝ) ≤ Y) := by
        have : (0 : ℝ) ≤ j := j.cast_nonneg
        linarith
      simp [this]
    rw [Finset.sum_eq_zero hz, add_zero, Real.exp_le_one_iff]
    nlinarith
  · set m := ⌊Y⌋₊ with hm
    have hmY : (m : ℝ) ≤ Y := Nat.floor_le hY
    have hYm : Y < m + 1 := Nat.lt_floor_add_one Y
    have hmJ : m < J := by exact_mod_cast hmY.trans_lt hYJ
    have hsum : ∑ j ∈ Finset.range J,
        (Real.exp (θ * ((j + 1 : ℕ) : ℝ)) - Real.exp (θ * (j : ℝ))) *
          (if (j : ℝ) ≤ Y then 1 else 0) =
        ∑ j ∈ Finset.range (m + 1),
          (Real.exp (θ * ((j + 1 : ℕ) : ℝ)) - Real.exp (θ * (j : ℝ))) := by
      simp only [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨_, hj⟩
        have : j ≤ m := Nat.le_floor hj
        omega
      · intro hj
        refine ⟨by omega, ?_⟩
        have : (j : ℝ) ≤ m := by exact_mod_cast (by omega : j ≤ m)
        linarith
    rw [hsum, Finset.sum_range_sub (fun j => Real.exp (θ * (j : ℝ))) (m + 1)]
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, add_sub_cancel]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith

/-- The constant of the binomial exponential-moment bound. -/
private def mnCbin (θ : ℝ) : ℝ := 1 + 2 * (Real.exp θ - 1) / (1 - Real.exp (θ - 1))

private lemma mn_one_le_Cbin {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) : 1 ≤ mnCbin θ := by
  unfold mnCbin
  have h1 : 0 ≤ Real.exp θ - 1 := by
    have := Real.add_one_le_exp θ
    linarith
  have h2 : 0 < 1 - Real.exp (θ - 1) := by
    have : Real.exp (θ - 1) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have : 0 ≤ 2 * (Real.exp θ - 1) / (1 - Real.exp (θ - 1)) := by positivity
  linarith

/-- Layer-cake: a tail bound `≤ 2e^{-y}` gives an exponential moment bound for `θ < 1`. -/
private lemma mn_layer_cake {T : Finset ℕ} {P Y : ℕ → ℝ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hP : ∀ s ∈ T, 0 ≤ P s) (hP1 : ∑ s ∈ T, P s ≤ 1)
    (htail : ∀ y : ℝ, ∑ s ∈ T.filter (fun s => y ≤ Y s), P s ≤ 2 * Real.exp (-y)) :
    ∑ s ∈ T, P s * Real.exp (θ * Y s) ≤ mnCbin θ := by
  set J : ℕ := ∑ s ∈ T, ⌈Y s⌉₊ + 1 with hJdef
  have hJ : ∀ s ∈ T, Y s < J := by
    intro s hs
    have h1 : ⌈Y s⌉₊ ≤ ∑ s ∈ T, ⌈Y s⌉₊ :=
      Finset.single_le_sum (f := fun s => ⌈Y s⌉₊) (fun _ _ => Nat.zero_le _) hs
    calc Y s ≤ ⌈Y s⌉₊ := Nat.le_ceil _
      _ ≤ (∑ s ∈ T, ⌈Y s⌉₊ : ℕ) := by exact_mod_cast h1
      _ < J := by rw [hJdef]; push_cast; linarith
  set c : ℕ → ℝ := fun j => Real.exp (θ * ((j + 1 : ℕ) : ℝ)) - Real.exp (θ * (j : ℝ)) with hc
  have hc0 : ∀ j, 0 ≤ c j := fun j => by
    simp only [hc]
    refine sub_nonneg.mpr (Real.exp_le_exp.mpr ?_)
    push_cast
    nlinarith
  have hr0 : 0 < Real.exp (θ - 1) := Real.exp_pos _
  have hr1 : Real.exp (θ - 1) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hE : 0 ≤ Real.exp θ - 1 := by
    have := Real.add_one_le_exp θ
    linarith
  calc ∑ s ∈ T, P s * Real.exp (θ * Y s)
      ≤ ∑ s ∈ T, P s * (1 + ∑ j ∈ Finset.range J, c j * (if (j : ℝ) ≤ Y s then 1 else 0)) :=
        Finset.sum_le_sum fun s hs =>
          mul_le_mul_of_nonneg_left (mn_layer_pointwise hθ0 (hJ s hs)) (hP s hs)
    _ = ∑ s ∈ T, P s + ∑ j ∈ Finset.range J,
          c j * ∑ s ∈ T.filter (fun s => (j : ℝ) ≤ Y s), P s := by
        simp only [mul_add, mul_one, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Finset.sum_filter]
        refine Finset.sum_congr rfl fun s _ => ?_
        split_ifs <;> ring
    _ ≤ 1 + ∑ j ∈ Finset.range J, c j * (2 * Real.exp (-(j : ℝ))) :=
        add_le_add hP1 (Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (htail j) (hc0 j))
    _ = 1 + 2 * (Real.exp θ - 1) * ∑ j ∈ Finset.range J, Real.exp (θ - 1) ^ j := by
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hc]
        rw [← Real.exp_nat_mul]
        push_cast
        rw [show θ * ((j : ℝ) + 1) = θ * j + θ by ring, Real.exp_add,
          show (j : ℝ) * (θ - 1) = θ * j + -(j : ℝ) by ring, Real.exp_add]
        ring
    _ ≤ 1 + 2 * (Real.exp θ - 1) * (1 - Real.exp (θ - 1))⁻¹ := by
        have hg : ∑ j ∈ Finset.range J, Real.exp (θ - 1) ^ j ≤ (1 - Real.exp (θ - 1))⁻¹ := by
          have := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) hr0.le hr1
          rwa [← Finset.range_eq_Ico, pow_zero, one_div] at this
        have h2E : 0 ≤ 2 * (Real.exp θ - 1) := by positivity
        have := mul_le_mul_of_nonneg_left hg h2E
        linarith
    _ = mnCbin θ := by unfold mnCbin; ring

/-- Binomial exponential moment of the relative entropy, uniform in `n` and `p`. -/
private lemma mn_binom_moment {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (n : ℕ) :
    ∑ s ∈ Finset.range (n + 1), (n.choose s : ℝ) * p ^ s * (1 - p) ^ (n - s) *
      Real.exp (θ * mnKl n s p) ≤ mnCbin θ := by
  refine mn_layer_cake (P := fun s => (n.choose s : ℝ) * p ^ s * (1 - p) ^ (n - s))
    (Y := fun s => mnKl n s p) hθ0 hθ1 (fun s _ => ?_) (le_of_eq ?_) (fun y => mn_tail hp0 hp1 n y)
  · have : 0 ≤ 1 - p := by linarith
    positivity
  · exact (Finset.sum_congr rfl fun s _ => by ring).trans (mn_binom_sum_one n p)

/-- The binomial bound in the form used in the induction on the number of colours. -/
private lemma mn_binom_moment_k {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (k n : ℕ) :
    ∑ s ∈ Finset.range (n + 1), (n.choose s : ℝ) *
      ((k : ℝ) ^ (n - s) * Real.exp (θ * mnKl n s (1 / ((k : ℝ) + 1)))) ≤
      mnCbin θ * ((k : ℝ) + 1) ^ n := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Finset.sum_eq_single n]
    · simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, one_mul, Nat.cast_zero,
        zero_add, div_one, mul_one, one_pow]
      have : mnKl n n 1 = 0 := by
        unfold mnKl
        rcases Nat.eq_zero_or_pos n with h | h
        · simp [h]
        · have : (n : ℝ) ≠ 0 := by positivity
          simp [this]
      rw [this, mul_zero, Real.exp_zero]
      exact mn_one_le_Cbin hθ0 hθ1
    · intro s hs hsn
      have : n - s ≠ 0 := by
        simp only [Finset.mem_range] at hs
        omega
      simp [zero_pow this]
    · intro h
      simp at h
  · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    set p : ℝ := 1 / ((k : ℝ) + 1) with hp
    have hp0 : 0 < p := by positivity
    have hp1 : p < 1 := by rw [hp, div_lt_one (by positivity)]; linarith
    have h1p : 1 - p = k / ((k : ℝ) + 1) := by rw [hp]; field_simp; ring
    have key := mn_binom_moment hθ0 hθ1 hp0 hp1 n
    have hK : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    calc ∑ s ∈ Finset.range (n + 1), (n.choose s : ℝ) *
          ((k : ℝ) ^ (n - s) * Real.exp (θ * mnKl n s p))
        = ((k : ℝ) + 1) ^ n * ∑ s ∈ Finset.range (n + 1), (n.choose s : ℝ) * p ^ s *
            (1 - p) ^ (n - s) * Real.exp (θ * mnKl n s p) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s hs => ?_
          have hsn : s ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
          rw [h1p, hp, div_pow, div_pow, one_pow]
          have : ((k : ℝ) + 1) ^ n = ((k : ℝ) + 1) ^ s * ((k : ℝ) + 1) ^ (n - s) := by
            rw [← pow_add, Nat.add_sub_cancel' hsn]
          rw [this]
          field_simp
      _ ≤ ((k : ℝ) + 1) ^ n * mnCbin θ := mul_le_mul_of_nonneg_left key (by positivity)
      _ = mnCbin θ * ((k : ℝ) + 1) ^ n := by ring

/-! ### Splitting off one colour -/

/-- Glue a colouring `g` of `Sᶜ` avoiding the colour `c` with the constant colour `c` on `S`. -/
private def mnGlue {ι κ : Type*} (c : κ) (S : Finset ι) (g : {i // i ∉ S} → {x : κ // x ≠ c}) :
    ι → κ :=
  fun i => if h : i ∈ S then c else (g ⟨i, h⟩).1

private lemma mn_glue_eq_c_iff {ι κ : Type*} (c : κ) (S : Finset ι)
    (g : {i // i ∉ S} → {x : κ // x ≠ c}) (i : ι) : mnGlue c S g i = c ↔ i ∈ S := by
  unfold mnGlue
  by_cases h : i ∈ S
  · simp [h]
  · simp only [h, dif_neg, not_false_eq_true, iff_false]
    exact (g ⟨i, h⟩).2

private lemma mn_fiberCard_glue_c {ι κ : Type*} [Fintype ι] (c : κ) (S : Finset ι)
    (g : {i // i ∉ S} → {x : κ // x ≠ c}) : fiberCard (mnGlue c S g) c = S.card := by
  unfold fiberCard
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact mn_glue_eq_c_iff c S g i

private lemma mn_fiberCard_glue_ne {ι κ : Type*} [Fintype ι] (c : κ) (S : Finset ι)
    (g : {i // i ∉ S} → {x : κ // x ≠ c}) (x : {x : κ // x ≠ c}) :
    fiberCard (mnGlue c S g) x.1 = fiberCard g x := by
  unfold fiberCard
  symm
  refine Finset.card_bij (fun a _ => a.1) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    simp [mnGlue, a.2, ha]
  · intro a _ b _ h
    exact Subtype.ext h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have hbS : b ∉ S := by
      intro hbS
      rw [← mn_glue_eq_c_iff c S g] at hbS
      exact x.2 (hb.symm.trans hbS)
    refine ⟨⟨b, hbS⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply Subtype.ext
    simpa [mnGlue, hbS] using hb

/-- A sum over colourings `ι → κ`, split according to the colour class `S` of `c`. -/
private lemma mn_sum_decomp {ι κ : Type*} [Fintype ι] [Fintype κ] (c : κ) (F : (ι → κ) → ℝ) :
    ∑ f : ι → κ, F f =
      ∑ S : Finset ι, ∑ g : {i // i ∉ S} → {x : κ // x ≠ c}, F (mnGlue c S g) := by
  rw [← Finset.sum_fiberwise Finset.univ
    (fun f : ι → κ => Finset.univ.filter (fun i => f i = c)) F]
  refine Finset.sum_congr rfl fun S _ => ?_
  symm
  refine Finset.sum_bij' (fun g _ => mnGlue c S g)
    (fun f hf => fun i => ⟨f i.1, fun hfc => ?_⟩) ?_ ?_ ?_ ?_ ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    apply i.2
    have hi : (i : ι) ∈ Finset.univ.filter (fun j => f j = c) := by simp [hfc]
    rwa [hf] at hi
  · intro g _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact mn_glue_eq_c_iff c S g i
  · intro f _
    exact Finset.mem_univ _
  · intro g _
    funext i
    apply Subtype.ext
    simp [mnGlue, i.2]
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    funext i
    by_cases h : i ∈ S
    · simp only [mnGlue, h, dif_pos]
      rw [← hf] at h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h.symm
    · simp [mnGlue, h]
  · intro g _
    rfl

/-- **Chain rule** for the empirical relative entropy when one colour is split off. -/
private lemma mn_chain {ι κ : Type*} [Fintype ι] [Fintype κ] (c : κ) (S : Finset ι)
    (g : {i // i ∉ S} → {x : κ // x ≠ c}) :
    (Fintype.card ι : ℝ) * empKL (mnGlue c S g) =
      mnKl (Fintype.card ι) S.card (1 / (Fintype.card κ : ℝ)) +
        (Fintype.card {i // i ∉ S} : ℝ) * empKL g := by
  have hm : Fintype.card {i // i ∉ S} = Fintype.card ι - S.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
  have hk : Fintype.card {x : κ // x ≠ c} = Fintype.card κ - 1 := by
    have := Fintype.card_subtype_compl (fun x : κ => x = c)
    rw [Fintype.card_subtype_eq] at this
    exact this
  have hK1 : 1 ≤ Fintype.card κ := Fintype.card_pos_iff.mpr ⟨c⟩
  have hSn : S.card ≤ Fintype.card ι := Finset.card_le_univ S
  rw [mn_card_mul_empKL, mn_card_mul_empKL, Fintype.sum_eq_add_sum_subtype_ne _ c]
  simp only [mn_fiberCard_glue_c, mn_fiberCard_glue_ne]
  have hsumM : ∑ x : {x : κ // x ≠ c}, (fiberCard g x : ℝ) = Fintype.card {i // i ∉ S} := by
    exact_mod_cast mn_sum_fiberCard g
  set n := Fintype.card ι with hn
  set K := Fintype.card κ with hK
  set m := Fintype.card {i // i ∉ S} with hm'
  set k := Fintype.card {x : κ // x ≠ c} with hk'
  have hmR : (m : ℝ) = (n : ℝ) - S.card := by rw [hm, Nat.cast_sub hSn]
  have hkR : (k : ℝ) = (K : ℝ) - 1 := by rw [hk, Nat.cast_sub hK1, Nat.cast_one]
  have hK0 : (K : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    linarith
  have hterm : ∀ x : {x : κ // x ≠ c},
      (fiberCard g x : ℝ) * Real.log (K * fiberCard g x / n) =
        (fiberCard g x : ℝ) * Real.log (k * fiberCard g x / m) +
          (fiberCard g x : ℝ) * Real.log (K * m / (k * n)) := by
    intro x
    rcases Nat.eq_zero_or_pos (fiberCard g x) with h0 | hpos
    · simp [h0]
    · have hMm : fiberCard g x ≤ m := mn_fiberCard_le g x
      have hm0 : 0 < m := lt_of_lt_of_le hpos hMm
      have hk0 : 0 < k := Fintype.card_pos_iff.mpr ⟨x⟩
      have hn0 : 0 < n := by omega
      have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
      have hk0' : (0 : ℝ) < k := by exact_mod_cast hk0
      have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
      have hM0' : (0 : ℝ) < fiberCard g x := by exact_mod_cast hpos
      have hKpos : (0 : ℝ) < K := by
        have : (1 : ℝ) ≤ K := by exact_mod_cast hK1
        linarith
      rw [← mul_add, ← Real.log_mul (by positivity) (by positivity)]
      congr 2
      field_simp
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_add_distrib, ← Finset.sum_mul, hsumM]
  unfold mnKl
  have e1 : (S.card : ℝ) * Real.log ((K : ℝ) * S.card / n) =
      (S.card : ℝ) * Real.log ((S.card : ℝ) / (n * (1 / (K : ℝ)))) := by
    congr 2
    field_simp
  have e2 : (m : ℝ) * Real.log ((K : ℝ) * m / (k * n)) =
      ((n : ℝ) - S.card) * Real.log (((n : ℝ) - S.card) / (n * (1 - 1 / (K : ℝ)))) := by
    rw [← hmR, hkR]
    congr 2
    rw [show (1 : ℝ) - 1 / K = (K - 1) / K by field_simp, mul_div_assoc', div_div_eq_mul_div]
    ring
  rw [e1, e2]
  ring

/-! ### Induction on the number of colours -/

/-- The induction on the number `k` of colours, with `C_{k+1} = C_k C_bin`. -/
private lemma mn_main_aux {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ι κ : Type) [Fintype ι] [Fintype κ], Fintype.card κ = k →
      ∑ f : ι → κ, Real.exp (θ * Fintype.card ι * empKL f) ≤ C * (k : ℝ) ^ Fintype.card ι := by
  induction k with
  | zero =>
    refine ⟨1, zero_le_one, fun ι κ _ _ hκ => ?_⟩
    have : IsEmpty κ := Fintype.card_eq_zero_iff.mp hκ
    have h1 : ∀ f : ι → κ, Real.exp (θ * Fintype.card ι * empKL f) = 1 := fun f => by
      have : empKL f = 0 := by
        unfold empKL
        simp
      rw [this, mul_zero, Real.exp_zero]
    rw [Finset.sum_congr rfl fun f _ => h1 f, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, hκ, nsmul_eq_mul, mul_one, one_mul]
    push_cast
    exact le_refl _
  | succ k ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    refine ⟨C * mnCbin θ, mul_nonneg hC0 (by linarith [mn_one_le_Cbin hθ0 hθ1]),
      fun ι κ _ _ hκ => ?_⟩
    obtain ⟨c⟩ : Nonempty κ := Fintype.card_pos_iff.mp (by omega)
    rw [mn_sum_decomp c]
    have hk' : Fintype.card {x : κ // x ≠ c} = k := by
      have := Fintype.card_subtype_compl (fun x : κ => x = c)
      rw [Fintype.card_subtype_eq, hκ] at this
      simpa using this
    have hstep : ∀ S : Finset ι, ∑ g : {i // i ∉ S} → {x : κ // x ≠ c},
        Real.exp (θ * Fintype.card ι * empKL (mnGlue c S g)) ≤
        Real.exp (θ * mnKl (Fintype.card ι) S.card (1 / ((k : ℝ) + 1))) *
          (C * (k : ℝ) ^ (Fintype.card ι - S.card)) := by
      intro S
      have hm : Fintype.card {i // i ∉ S} = Fintype.card ι - S.card := by
        rw [Fintype.card_subtype_compl, Fintype.card_coe]
      have hih := hC {i // i ∉ S} {x : κ // x ≠ c} hk'
      rw [hm] at hih
      calc ∑ g : {i // i ∉ S} → {x : κ // x ≠ c},
            Real.exp (θ * Fintype.card ι * empKL (mnGlue c S g))
          = ∑ g : {i // i ∉ S} → {x : κ // x ≠ c},
              Real.exp (θ * mnKl (Fintype.card ι) S.card (1 / ((k : ℝ) + 1))) *
                Real.exp (θ * ((Fintype.card ι - S.card : ℕ) : ℝ) * empKL g) := by
            refine Finset.sum_congr rfl fun g _ => ?_
            rw [mul_assoc, mn_chain, hκ, hm, ← Real.exp_add]
            congr 1
            push_cast
            ring
        _ = Real.exp (θ * mnKl (Fintype.card ι) S.card (1 / ((k : ℝ) + 1))) *
              ∑ g : {i // i ∉ S} → {x : κ // x ≠ c},
                Real.exp (θ * ((Fintype.card ι - S.card : ℕ) : ℝ) * empKL g) := by
            rw [Finset.mul_sum]
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
            refine (Finset.sum_congr ?_ (fun _ _ => rfl)).trans_le hih
            ext
            simp
    calc ∑ S : Finset ι, ∑ g : {i // i ∉ S} → {x : κ // x ≠ c},
          Real.exp (θ * Fintype.card ι * empKL (mnGlue c S g))
        ≤ ∑ S : Finset ι, Real.exp (θ * mnKl (Fintype.card ι) S.card (1 / ((k : ℝ) + 1))) *
            (C * (k : ℝ) ^ (Fintype.card ι - S.card)) := Finset.sum_le_sum fun S _ => hstep S
      _ = C * ∑ s ∈ Finset.range (Fintype.card ι + 1), ((Fintype.card ι).choose s : ℝ) *
            ((k : ℝ) ^ (Fintype.card ι - s) *
              Real.exp (θ * mnKl (Fintype.card ι) s (1 / ((k : ℝ) + 1)))) := by
          have := Finset.sum_powerset_apply_card
            (f := fun s => Real.exp (θ * mnKl (Fintype.card ι) s (1 / ((k : ℝ) + 1))) *
              (C * (k : ℝ) ^ (Fintype.card ι - s))) (x := (Finset.univ : Finset ι))
          rw [Finset.powerset_univ, Finset.card_univ] at this
          rw [this, Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [nsmul_eq_mul]
          ring
      _ ≤ C * (mnCbin θ * ((k : ℝ) + 1) ^ Fintype.card ι) :=
          mul_le_mul_of_nonneg_left (mn_binom_moment_k hθ0 hθ1 k _) hC0
      _ = C * mnCbin θ * ((k + 1 : ℕ) : ℝ) ^ Fintype.card ι := by push_cast; ring

/-- **Theorem 5.3 (`thm:multinomial-moment`)** for the uniform vector, with a constant
`C = C(θ, k)` uniform in `n`: `∑_{f : ι → κ} exp(θ n D(emp f ‖ u)) ≤ C k^n` for `|κ| = k`,
`n = |ι|`. -/
theorem exists_sum_exp_empKL_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (k : ℕ) :
    ∃ C : ℝ, ∀ (ι κ : Type) [Fintype ι] [Fintype κ], Fintype.card κ = k →
      ∑ f : ι → κ, Real.exp (θ * Fintype.card ι * empKL f) ≤ C * (k : ℝ) ^ Fintype.card ι := by
  obtain ⟨C, -, hC⟩ := mn_main_aux hθ0 hθ1 k
  exact ⟨C, hC⟩

/-! ### `klFun` away from its minimum -/

/-- `klFun` is bounded below away from `1`. -/
private lemma mn_klFun_ge_of_abs {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) (hε1 : ε < 1)
    (h : ε ≤ |x - 1|) :
    min (InformationTheory.klFun (1 + ε)) (InformationTheory.klFun (1 - ε)) ≤
      InformationTheory.klFun x := by
  have hcv := InformationTheory.convexOn_klFun
  have h1mem : (1 : ℝ) ∈ Set.Ici (0 : ℝ) := by simp
  have hxmem : x ∈ Set.Ici (0 : ℝ) := hx
  rcases le_or_gt 1 x with hx1 | hx1
  · -- `x ≥ 1 + ε`
    have hxe : ε ≤ x - 1 := by rwa [abs_of_nonneg (by linarith)] at h
    have hpos : 0 < x - 1 := by linarith
    set a := ε / (x - 1) with ha
    have ha0 : 0 < a := div_pos hε hpos
    have ha1 : a ≤ 1 := (div_le_one hpos).mpr hxe
    have hcomb : a • x + (1 - a) • (1 : ℝ) = 1 + ε := by
      simp only [smul_eq_mul, ha]
      field_simp
      ring
    have := hcv.le_left_of_right_le' (b := 1 - a) hxmem h1mem ha0 (by linarith) (by ring) (by
      rw [hcomb, InformationTheory.klFun_one]
      exact InformationTheory.klFun_nonneg (by linarith))
    rw [hcomb] at this
    exact (min_le_left _ _).trans this
  · have hxe : ε ≤ 1 - x := by rwa [abs_of_neg (by linarith), neg_sub] at h
    have hpos : 0 < 1 - x := by linarith
    set a := ε / (1 - x) with ha
    have ha0 : 0 < a := div_pos hε hpos
    have ha1 : a ≤ 1 := (div_le_one hpos).mpr hxe
    have hcomb : a • x + (1 - a) • (1 : ℝ) = 1 - ε := by
      simp only [smul_eq_mul, ha]
      field_simp
      ring
    have := hcv.le_left_of_right_le' (b := 1 - a) hxmem h1mem ha0 (by linarith) (by ring) (by
      rw [hcomb, InformationTheory.klFun_one]
      exact InformationTheory.klFun_nonneg (by linarith))
    rw [hcomb] at this
    exact (min_le_right _ _).trans this

private lemma mn_klFun_pos {x : ℝ} (hx : 0 ≤ x) (h1 : x ≠ 1) : 0 < InformationTheory.klFun x :=
  lt_of_le_of_ne (InformationTheory.klFun_nonneg hx)
    (fun h => h1 ((InformationTheory.klFun_eq_zero_iff hx).mp h.symm))

/-- Unbalanced colourings have empirical relative entropy bounded below. -/
theorem exists_empKL_ge_of_not_balanced {q : ℕ} (hq : 2 ≤ q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ κ > 0, ∀ (n : ℕ), 0 < n → ∀ σ : Fin n → Fin q, σ ∉ balanced q n δ → κ ≤ empKL σ := by
  have hq0 : (0 : ℝ) < q := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  set ε : ℝ := min (q * δ) (1 / 2) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by norm_num)
  have hε1 : ε < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨(q : ℝ)⁻¹ * min (InformationTheory.klFun (1 + ε)) (InformationTheory.klFun (1 - ε)),
    ?_, ?_⟩
  · refine mul_pos (by positivity) (lt_min ?_ ?_)
    · exact mn_klFun_pos (by linarith) (by linarith)
    · exact mn_klFun_pos (by linarith) (by linarith)
  intro n hn σ hσ
  simp only [balanced, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_le] at hσ
  obtain ⟨i, hi⟩ := hσ
  have hn' : 0 < Fintype.card (Fin n) := by simpa using hn
  rw [mn_empKL_eq_klFun σ hn']
  simp only [Fintype.card_fin]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans ?_ (Finset.single_le_sum (f := fun c => InformationTheory.klFun
    ((q : ℝ) * fiberCard σ c / n)) (fun c _ => InformationTheory.klFun_nonneg (by positivity))
    (Finset.mem_univ i))
  refine mn_klFun_ge_of_abs (by positivity) hε0 hε1 ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have : (q : ℝ) * fiberCard σ i / n - 1 = q * (colorFrac σ i - 1 / q) := by
    unfold colorFrac
    field_simp
  rw [this, abs_mul, abs_of_pos hq0]
  calc ε ≤ q * δ := min_le_left _ _
    _ ≤ q * |colorFrac σ i - 1 / q| := mul_le_mul_of_nonneg_left hi.le hq0.le

end

end ERZeroFreeness
