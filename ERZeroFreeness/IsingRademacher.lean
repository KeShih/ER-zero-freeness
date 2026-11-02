/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.IsingVBDefs
import ERZeroFreeness.TwoReplica

/-! # `IsingRademacher`: part of Theorem 1.5 (`thm:ising-applications`), zero-freeness

Proof plans for the statements of this module: `docs/ising-vb/blueprint.md`, section
"Module `IsingRademacher`" (and Appendix A for proofs already checked).  Frozen statements carry their
blueprint item numbers in the comments. -/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

-- [IR1] spins multiply under addition in `Fin 2 = ℤ/2` (overlap `η = σ τ`).
theorem isingSpin_add (a b : Fin 2) : isingSpin (a + b) = isingSpin a * isingSpin b := by
  fin_cases a <;> fin_cases b <;> simp [isingSpin]

-- [IR2] `A_{σ_u σ_v} = σ_u σ_v` for `q = 2`.
theorem edgeA_two_mk {V : Type*} (σ : V → Fin 2) (u v : V) :
    edgeA 2 σ s(u, v) = ((isingSpin (σ u) * isingSpin (σ v) : ℝ) : ℂ) := by
  unfold edgeA isingSpin
  simp only [Sym2.map_mk, Sym2.mk_isDiag_iff]
  rcases Fin.exists_fin_two.mp ⟨σ u, rfl⟩ with h | h <;>
  rcases Fin.exists_fin_two.mp ⟨σ v, rfl⟩ with h' | h' <;> simp [h, h'] <;> norm_num

/-- A spin squares to `1`. -/
private lemma IsingRademacher_spin_mul_self (a : Fin 2) : isingSpin a * isingSpin a = 1 := by
  fin_cases a <;> simp [isingSpin]

/-- `∑_{u<v} w_u w_v = ((∑_u w_u)² - n)/2` when every `w_u² = 1`. -/
private lemma IsingRademacher_sum_top {n : ℕ} (w : Fin n → ℝ) (hw : ∀ u, w u * w u = 1)
    (r : Sym2 (Fin n) → ℝ) (hr : ∀ u v, r s(u, v) = w u * w v) :
    ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, r e = ((∑ u, w u) ^ 2 - n) / 2 := by
  have h := TwoReplicaAux.two_mul_sum_top_add r
  have h1 : ∑ u, r s(u, u) = n := by
    simp only [hr, hw, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
  have h2 : ∑ u, ∑ v, r s(u, v) = (∑ u, w u) ^ 2 := by
    simp only [hr]
    rw [sq, Finset.sum_mul_sum]
  rw [h1, h2] at h
  linarith

-- [IR3] `∑_{u<v} σ_u σ_v = (S_σ² - n)/2`.
theorem sum_top_edgeA_two {n : ℕ} (σ : Fin n → Fin 2) :
    ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, edgeA 2 σ e =
      (((isingMag σ ^ 2 - n) / 2 : ℝ) : ℂ) := by
  have hr : ∀ u v, TwoReplicaAux.aRe 2 σ s(u, v) = isingSpin (σ u) * isingSpin (σ v) := by
    intro u v
    have h := edgeA_two_mk σ u v
    rw [TwoReplicaAux.edgeA_eq_ofReal, Complex.ofReal_inj] at h
    exact h
  simp_rw [TwoReplicaAux.edgeA_eq_ofReal]
  rw [← Complex.ofReal_sum, IsingRademacher_sum_top (fun u => isingSpin (σ u))
    (fun u => IsingRademacher_spin_mul_self _) _ hr]
  rfl

-- [IR4] `∑_{u<v} η_u η_v = (S_η² - n)/2` for the overlap `η = σ τ` (`σ + τ` in `Fin 2`).
theorem sum_top_edgeA_two_mul {n : ℕ} (σ τ : Fin n → Fin 2) :
    ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, edgeA 2 σ e * edgeA 2 τ e =
      (((isingMag (σ + τ) ^ 2 - n) / 2 : ℝ) : ℂ) := by
  have hr : ∀ u v, TwoReplicaAux.aRe 2 σ s(u, v) * TwoReplicaAux.aRe 2 τ s(u, v) =
      isingSpin ((σ + τ) u) * isingSpin ((σ + τ) v) := by
    intro u v
    have h1 := edgeA_two_mk σ u v
    have h2 := edgeA_two_mk τ u v
    rw [TwoReplicaAux.edgeA_eq_ofReal, Complex.ofReal_inj] at h1 h2
    rw [h1, h2, Pi.add_apply, Pi.add_apply, isingSpin_add, isingSpin_add]
    ring
  simp_rw [TwoReplicaAux.edgeA_eq_ofReal, ← Complex.ofReal_mul]
  rw [← Complex.ofReal_sum, IsingRademacher_sum_top (fun u => isingSpin ((σ + τ) u))
    (fun u => IsingRademacher_spin_mul_self _)
    (fun e => TwoReplicaAux.aRe 2 σ e * TwoReplicaAux.aRe 2 τ e) hr]
  rfl

-- [IR5] independence of the signs: `E_σ e^{cS} = cosh(c)^n`.
theorem sum_exp_mul_isingMag (n : ℕ) (c : ℝ) :
    ∑ σ : Fin n → Fin 2, Real.exp (c * isingMag σ) = (2 * Real.cosh c) ^ n := by
  have h1 : ∀ σ : Fin n → Fin 2,
      Real.exp (c * isingMag σ) = ∏ v, Real.exp (c * isingSpin (σ v)) := by
    intro σ
    rw [isingMag, Finset.mul_sum, Real.exp_sum]
  have h2 : ∑ a : Fin 2, Real.exp (c * isingSpin a) = 2 * Real.cosh c := by
    rw [Fin.sum_univ_two, Real.cosh_eq]
    simp [isingSpin]
    ring
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (a : Fin 2) => Real.exp (c * isingSpin a))]
  simp_rw [h2]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

-- [IR6] the Gaussian identity `E_g e^{yg} = e^{y²/2}` (completing the square).
theorem integral_exp_neg_sq_half_add (y : ℝ) :
    ∫ x : ℝ, Real.exp (-x ^ 2 / 2 + y * x) =
      Real.sqrt (2 * Real.pi) * Real.exp (y ^ 2 / 2) := by
  have h : ∀ x : ℝ, Real.exp (-x ^ 2 / 2 + y * x) =
      Real.exp (y ^ 2 / 2) * Real.exp (-(1 / 2) * (x - y) ^ 2) := by
    intro x
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [h]
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub_right_eq_self (fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2)) y,
    integral_gaussian, show Real.pi / (1 / 2) = 2 * Real.pi by ring, mul_comm]

/-- Integrability of `x ↦ e^{-x²/2 + yx}` (complete the square, as in IR6). -/
private lemma IsingRademacher_integrable_exp_quad (y : ℝ) :
    MeasureTheory.Integrable (fun x : ℝ => Real.exp (-x ^ 2 / 2 + y * x)) := by
  have h : (fun x : ℝ => Real.exp (-x ^ 2 / 2 + y * x)) =
      fun x => Real.exp (y ^ 2 / 2) * Real.exp (-(1 / 2) * (x - y) ^ 2) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h]
  exact ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).comp_sub_right y).const_mul _

-- [IR7a] the equality of `eq:rademacher-moment`, `E e^{λS²/(2n)} = E_g cosh(g√(λ/n))^n`
-- (every `n`, every `λ ≥ 0`; `E_g` is the standard Gaussian integral).
theorem rademacher_moment_eq {n : ℕ} {lam : ℝ} (h0 : 0 ≤ lam) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin 2, Real.exp (lam * isingMag σ ^ 2 / (2 * n)) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ x : ℝ, Real.exp (-x ^ 2 / 2) * Real.cosh (x * Real.sqrt (lam / n)) ^ n := by
  set c := Real.sqrt (lam / n) with hc
  have hc2 : c ^ 2 = lam / n := Real.sq_sqrt (div_nonneg h0 (Nat.cast_nonneg n))
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  -- each exponential is a Gaussian integral (IR6 with `y = c S_σ`)
  have h1 : ∀ σ : Fin n → Fin 2, Real.exp (lam * isingMag σ ^ 2 / (2 * n)) =
      (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x : ℝ, Real.exp (-x ^ 2 / 2 + (c * isingMag σ) * x) := by
    intro σ
    rw [integral_exp_neg_sq_half_add, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
    congr 1
    rw [mul_pow, hc2]
    ring
  -- the pointwise identity of the integrands (IR5 with `c ↦ x c`)
  have h2 : ∀ x : ℝ, ∑ σ : Fin n → Fin 2, Real.exp (-x ^ 2 / 2 + (c * isingMag σ) * x) =
      (2 : ℝ) ^ n * (Real.exp (-x ^ 2 / 2) * Real.cosh (x * c) ^ n) := by
    intro x
    have e : ∀ σ : Fin n → Fin 2, Real.exp (-x ^ 2 / 2 + (c * isingMag σ) * x) =
        Real.exp (-x ^ 2 / 2) * Real.exp ((x * c) * isingMag σ) := by
      intro σ
      rw [← Real.exp_add]
      congr 1
      ring
    simp_rw [e]
    rw [← Finset.mul_sum, sum_exp_mul_isingMag, mul_pow]
    ring
  have h3 : ∫ x : ℝ, Real.exp (-x ^ 2 / 2) * Real.cosh (x * c) ^ n =
      ((2 : ℝ) ^ n)⁻¹ *
        ∑ σ : Fin n → Fin 2, ∫ x : ℝ, Real.exp (-x ^ 2 / 2 + (c * isingMag σ) * x) := by
    rw [← MeasureTheory.integral_finsetSum _
        (fun σ _ => IsingRademacher_integrable_exp_quad (c * isingMag σ)),
      ← MeasureTheory.integral_const_mul]
    congr 1
    funext x
    rw [h2 x, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n two_ne_zero), one_mul]
  simp_rw [h1]
  rw [h3, ← Finset.mul_sum]
  ring

-- [IR7b] **`eq:rademacher-moment`**, the whole display:
-- `E e^{λS²/(2n)} = E_g cosh(g√(λ/n))^n ≤ E_g e^{λg²/2} = (1-λ)^{-1/2}` for `0 ≤ λ < 1`.
theorem rademacher_moment_display {n : ℕ} {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam < 1) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin 2, Real.exp (lam * isingMag σ ^ 2 / (2 * n)) =
        (Real.sqrt (2 * Real.pi))⁻¹ *
          ∫ x : ℝ, Real.exp (-x ^ 2 / 2) * Real.cosh (x * Real.sqrt (lam / n)) ^ n ∧
      (Real.sqrt (2 * Real.pi))⁻¹ *
          ∫ x : ℝ, Real.exp (-x ^ 2 / 2) * Real.cosh (x * Real.sqrt (lam / n)) ^ n ≤
        (Real.sqrt (2 * Real.pi))⁻¹ *
          ∫ x : ℝ, Real.exp (-x ^ 2 / 2) * Real.exp (lam * x ^ 2 / 2) ∧
      (Real.sqrt (2 * Real.pi))⁻¹ *
          ∫ x : ℝ, Real.exp (-x ^ 2 / 2) * Real.exp (lam * x ^ 2 / 2) =
        (Real.sqrt (1 - lam))⁻¹ := by
  have hb : 0 < (1 - lam) / 2 := by linarith
  have he : ∀ x : ℝ, Real.exp (-x ^ 2 / 2) * Real.exp (lam * x ^ 2 / 2) =
      Real.exp (-((1 - lam) / 2) * x ^ 2) := by
    intro x
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨rademacher_moment_eq h0, ?_, ?_⟩
  · -- `cosh(xc)^n ≤ e^{λx²/2}` pointwise, then integrate
    have hint : MeasureTheory.Integrable
        (fun x : ℝ => Real.exp (-x ^ 2 / 2) * Real.exp (lam * x ^ 2 / 2)) := by
      simp_rw [he]
      exact integrable_exp_neg_mul_sq hb
    have hpt : ∀ x : ℝ, Real.cosh (x * Real.sqrt (lam / n)) ^ n ≤
        Real.exp (lam * x ^ 2 / 2) := by
      intro x
      calc Real.cosh (x * Real.sqrt (lam / n)) ^ n
          ≤ Real.exp ((x * Real.sqrt (lam / n)) ^ 2 / 2) ^ n :=
            pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq _) n
        _ = Real.exp (n * ((x * Real.sqrt (lam / n)) ^ 2 / 2)) := (Real.exp_nat_mul _ n).symm
        _ ≤ Real.exp (lam * x ^ 2 / 2) := by
          apply Real.exp_le_exp.2
          rw [mul_pow, Real.sq_sqrt (div_nonneg h0 (Nat.cast_nonneg n))]
          rcases Nat.eq_zero_or_pos n with hn | hn
          · subst hn
            simp only [Nat.cast_zero, zero_mul]
            positivity
          · have hn' : (n : ℝ) ≠ 0 := by positivity
            have : (n : ℝ) * (x ^ 2 * (lam / n) / 2) = lam * x ^ 2 / 2 := by
              field_simp
            exact this.le
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (Real.sqrt_nonneg _))
    refine MeasureTheory.integral_mono_of_nonneg ?_ hint ?_
    · exact MeasureTheory.ae_of_all _ fun x =>
        mul_nonneg (Real.exp_pos _).le (pow_nonneg (Real.cosh_pos _).le _)
    · exact MeasureTheory.ae_of_all _ fun x =>
        mul_le_mul_of_nonneg_left (hpt x) (Real.exp_pos _).le
  · -- the Gaussian integral with variance `1/(1-λ)`
    have hs : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
    simp_rw [he]
    rw [integral_gaussian, div_div_eq_mul_div, mul_comm Real.pi 2,
      Real.sqrt_div' _ (by linarith : (0 : ℝ) ≤ 1 - lam), mul_div_assoc', inv_mul_cancel₀ hs,
      one_div]

-- [IR7] the bound of `eq:rademacher-moment` used in Steps 2–3:
-- `E e^{λ S²/(2n)} ≤ (1-λ)^{-1/2}` for `0 ≤ λ < 1`.
theorem rademacher_moment {n : ℕ} {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam < 1) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin 2, Real.exp (lam * isingMag σ ^ 2 / (2 * n)) ≤
      (Real.sqrt (1 - lam))⁻¹ := by
  obtain ⟨h₁, h₂, h₃⟩ := rademacher_moment_display (n := n) h0 h1
  exact (h₁.trans_le h₂).trans h₃.le

-- [IR8] the overlap `η = σ τ` of two independent uniform configurations is uniform.
theorem sum_sum_isingMag_add {n : ℕ} (f : ℝ → ℝ) :
    ∑ σ : Fin n → Fin 2, ∑ τ : Fin n → Fin 2, f (isingMag (σ + τ)) =
      2 ^ n * ∑ η : Fin n → Fin 2, f (isingMag η) := by
  have h : ∀ σ : Fin n → Fin 2, ∑ τ : Fin n → Fin 2, f (isingMag (σ + τ)) =
      ∑ η : Fin n → Fin 2, f (isingMag η) := fun σ =>
    Fintype.sum_equiv (Equiv.addLeft σ) _ _ (fun τ => rfl)
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  ring

end

end ERZeroFreeness
