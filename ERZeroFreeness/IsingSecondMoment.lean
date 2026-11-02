/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.IsingRademacher
import ERZeroFreeness.TwoReplica
import ERZeroFreeness.ErdosRenyi

/-!
# The second moment of the Ising antiferromagnet (Step 2 of Section 7)

Let `G_n ∼ G(n, d/n)` and `I_n = Ẑ_{G_n}` with `q = 2`, i.e. `I_n = 𝓘_{G_n,1}`.
`ising_second_moment` gives a constant `C = C(d,T)` with
`E|I_n(t)|² ≤ C (1 - Λ)^{-1/2}`, `Λ = d(|t|² + 2(Re t)_+)`,
for `n ≥ d`, `|t| ≤ T` and `Λ < 1` (Theorem 1.5(i), `thm:ising-applications`).

Proof.  `ising_two_replica_identity` averages the two-replica product over the graph edge by
edge; `ising_pair_bound` bounds the term of each pair `(σ, τ)` by
`C exp((d/(2n)) [(Re t)_+ (S_σ² + S_τ²) + |t|² S_η²])`, `η = στ`.  Where the paper applies
Hölder's inequality, the proof uses the pointwise convexity bound `exp_wsum3_le` with weights
`d(Re t)_+/Λ, d(Re t)_+/Λ, d|t|²/Λ`; since `S_σ`, `S_τ` and `S_η` are each distributed as the
magnetization of a uniform configuration (`sum_sum_isingMag_add`), `rademacher_moment`
(`eq:rademacher-moment`) bounds each of the three terms by `(1 - Λ)^{-1/2}`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- The averaged two-replica edge factor: with `A^σ_e = edgeA 2 σ e` (`= σ_u σ_v` on `e = uv`),
`(1 - p) + p (1 + t A^σ_e) conj(1 + t A^τ_e) = 1 + p (t A^σ_e + t̄ A^τ_e + |t|² A^σ_e A^τ_e)`. -/
theorem ising_edge_factor_eq {V : Type*} (p : ℝ) (t : ℂ) (σ τ : V → Fin 2) (e : Sym2 V) :
    algebraMap ℝ ℂ (1 - p) + algebraMap ℝ ℂ p *
        ((1 + t * edgeA 2 σ e) * (starRingEnd ℂ) (1 + t * edgeA 2 τ e)) =
      1 + (p : ℂ) * (t * edgeA 2 σ e + (starRingEnd ℂ) t * edgeA 2 τ e +
        ((‖t‖ ^ 2 : ℝ) : ℂ) * (edgeA 2 σ e * edgeA 2 τ e)) := by
  rw [TwoReplicaAux.edgeA_eq_ofReal 2 σ e, TwoReplicaAux.edgeA_eq_ofReal 2 τ e]
  have h : t * (starRingEnd ℂ) t = ((‖t‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [Complex.coe_algebraMap, map_add, map_one, map_mul, Complex.conj_ofReal,
    Complex.ofReal_sub, Complex.ofReal_one]
  linear_combination (p : ℂ) * ((TwoReplicaAux.aRe 2 σ e : ℝ) : ℂ) *
    ((TwoReplicaAux.aRe 2 τ e : ℝ) : ℂ) * h

/-- `zhat_eval` on `Fin n` with `q = 2`, with the `Fintype` instance of this file. -/
private lemma IsingSecondMoment_zhat_eval {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℂ) :
    (zhat G 2).eval t = (((2 : ℕ) : ℂ) ^ n)⁻¹ *
      ∑ σ : Fin n → Fin 2, ∏ e ∈ G.edgeFinset, (1 + t * edgeA 2 σ e) := by
  rw [zhat_eval]
  simp only [Fintype.card_fin]
  congr 1
  exact Finset.sum_congr (Finset.ext fun σ => by simp) fun _ _ => rfl

/-- The exact two-replica identity for `G(n,p)`:
`E|I_n(t)|² = E_{σ,τ} ∏_{u<v} {1 + p (t σ_uσ_v + t̄ τ_uτ_v + |t|² η_uη_v)}`, `η = στ`. -/
theorem ising_two_replica_identity (n : ℕ) (p : ℝ) (t : ℂ) :
    ((erExp n p (fun G => ‖(zhat G 2).eval t‖ ^ 2) : ℝ) : ℂ) =
      ((4 : ℂ) ^ n)⁻¹ * ∑ σ : Fin n → Fin 2, ∑ τ : Fin n → Fin 2,
        ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
          (1 + (p : ℂ) * (t * edgeA 2 σ e + (starRingEnd ℂ) t * edgeA 2 τ e +
            ((‖t‖ ^ 2 : ℝ) : ℂ) * (edgeA 2 σ e * edgeA 2 τ e))) := by
  have hcc : (starRingEnd ℂ) (((2 : ℕ) : ℂ) ^ n)⁻¹ = (((2 : ℕ) : ℂ) ^ n)⁻¹ := by
    rw [map_inv₀, map_pow, map_natCast]
  -- `|Ẑ|² = Ẑ · conj Ẑ`, expanded into a double sum over `σ, τ`
  have hz : ∀ G : SimpleGraph (Fin n),
      ((‖(zhat G 2).eval t‖ ^ 2 : ℝ) : ℂ) =
        ((((2 : ℕ) : ℂ) ^ n)⁻¹) ^ 2 * ∑ σ : Fin n → Fin 2, ∑ τ : Fin n → Fin 2,
          ∏ e ∈ G.edgeFinset,
            ((1 + t * edgeA 2 σ e) * (starRingEnd ℂ) (1 + t * edgeA 2 τ e)) := by
    intro G
    have h0 := TwoReplicaAux.mul_conj_sum_prod (((2 : ℕ) : ℂ) ^ n)⁻¹ hcc
      (Finset.univ : Finset (Fin n → Fin 2)) G.edgeFinset (fun σ e => 1 + t * edgeA 2 σ e)
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, IsingSecondMoment_zhat_eval]
    exact h0
  have h1 : ((erExp n p (fun G => ‖(zhat G 2).eval t‖ ^ 2) : ℝ) : ℂ) =
      ∑ G : SimpleGraph (Fin n), (erWeight n p G : ℂ) *
        (((((2 : ℕ) : ℂ) ^ n)⁻¹) ^ 2 * ∑ σ : Fin n → Fin 2, ∑ τ : Fin n → Fin 2,
          ∏ e ∈ G.edgeFinset,
            ((1 + t * edgeA 2 σ e) * (starRingEnd ℂ) (1 + t * edgeA 2 τ e))) := by
    unfold erExp
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun G _ => ?_
    rw [Complex.ofReal_mul, hz G]
  have hc2 : ((((2 : ℕ) : ℂ) ^ n)⁻¹) ^ 2 = ((4 : ℂ) ^ n)⁻¹ := by
    rw [inv_pow, ← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h1, TwoReplicaAux.sum_mul_mul_sum_sum, hc2]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
  have h3 := sum_erWeight_mul_prod (n := n) (p := p) (R := ℂ)
    (fun e => (1 + t * edgeA 2 σ e) * (starRingEnd ℂ) (1 + t * edgeA 2 τ e))
  simp only [Complex.coe_algebraMap] at h3
  rw [h3]
  refine Finset.prod_congr rfl fun e _ => ?_
  have h4 := ising_edge_factor_eq p t σ τ e
  simp only [Complex.coe_algebraMap] at h4
  exact h4

/-- `y_e - 1 = t A_e + t̄ B_e + |t|² A_e B_e` for `y_e = (1 + tA_e) conj(1 + tB_e)`
(`ising_edge_factor_eq` with `p = 1`). -/
private lemma IsingSecondMoment_y_sub_one {V : Type*} (t : ℂ) (σ τ : V → Fin 2) (e : Sym2 V) :
    (1 + t * edgeA 2 σ e) * (starRingEnd ℂ) (1 + t * edgeA 2 τ e) - 1 =
      t * edgeA 2 σ e + (starRingEnd ℂ) t * edgeA 2 τ e +
        ((‖t‖ ^ 2 : ℝ) : ℂ) * (edgeA 2 σ e * edgeA 2 τ e) := by
  have h := ising_edge_factor_eq 1 t σ τ e
  simp only [sub_self, map_zero, map_one, one_mul, zero_add, Complex.ofReal_one] at h
  rw [h]
  ring

/-- `sum_top_edgeA_two` for the real values `aRe`. -/
private lemma IsingSecondMoment_sum_aRe {n : ℕ} (σ : Fin n → Fin 2) :
    ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, TwoReplicaAux.aRe 2 σ e =
      (isingMag σ ^ 2 - n) / 2 := by
  have h := sum_top_edgeA_two σ
  simp_rw [TwoReplicaAux.edgeA_eq_ofReal] at h
  rw [← Complex.ofReal_sum] at h
  exact Complex.ofReal_inj.mp h

/-- `sum_top_edgeA_two_mul` for the real values `aRe`. -/
private lemma IsingSecondMoment_sum_aRe_mul {n : ℕ} (σ τ : Fin n → Fin 2) :
    ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
        TwoReplicaAux.aRe 2 σ e * TwoReplicaAux.aRe 2 τ e =
      (isingMag (σ + τ) ^ 2 - n) / 2 := by
  have h := sum_top_edgeA_two_mul σ τ
  simp_rw [TwoReplicaAux.edgeA_eq_ofReal, ← Complex.ofReal_mul] at h
  rw [← Complex.ofReal_sum] at h
  exact Complex.ofReal_inj.mp h

/-- The final real inequality of `ising_pair_bound` (`x = n`; `a, b, c` are the squared
magnetizations). -/
private lemma IsingSecondMoment_final_ineq {d T r s a b c Q M x : ℝ} (hd : 0 < d) (hx : 0 < x)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s) (hr : -r ≤ T) (hQ : Q ≤ d ^ 2 * M ^ 2 / 2) :
    d / x * (r * ((a - x) / 2) + r * ((b - x) / 2) + s * ((c - x) / 2)) + Q ≤
      d * T + d ^ 2 * M ^ 2 / 2 + d / (2 * x) * (max r 0 * (a + b) + s * c) := by
  have e1 : d / x * (r * ((a - x) / 2) + r * ((b - x) / 2) + s * ((c - x) / 2)) =
      d / (2 * x) * (r * (a + b)) + d / (2 * x) * (s * c) - d * r - d * s / 2 := by
    field_simp
    ring
  have e2 : d / (2 * x) * (r * (a + b)) ≤ d / (2 * x) * (max r 0 * (a + b)) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg ha hb)) (by positivity)
  have e3 : d / (2 * x) * (max r 0 * (a + b) + s * c) =
      d / (2 * x) * (max r 0 * (a + b)) + d / (2 * x) * (s * c) := by ring
  have e4 : -(d * r) ≤ d * T := by
    have := mul_le_mul_of_nonneg_left hr hd.le
    linarith
  have e5 : 0 ≤ d * s := mul_nonneg hd.le hs
  rw [e1, e3]
  linarith

/-- The bound for a fixed pair `(σ, τ)`, for `n ≥ d` and `|t| ≤ T`:
`|∏_{u<v} {1 + (d/n)(…)}| ≤ C exp((d/(2n)) [(Re t)_+ (S_σ² + S_τ²) + |t|² S_η²])`.  Apply
`|1 + w| ≤ exp(Re w + |w|²/2)` to each factor; the quadratic terms and the diagonal terms
`-d Re t - d|t|²/2` are absorbed into `C = C(d,T)`, and `Re t` is bounded by `(Re t)_+`. -/
theorem ising_pair_bound {d : ℝ} (hd : 0 < d) {T : ℝ} (hT : 0 ≤ T) :
    ∃ C > 0, ∀ n : ℕ, d ≤ n → ∀ (σ τ : Fin n → Fin 2) (t : ℂ), ‖t‖ ≤ T →
      ‖∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
          (1 + ((d / n : ℝ) : ℂ) * (t * edgeA 2 σ e + (starRingEnd ℂ) t * edgeA 2 τ e +
            ((‖t‖ ^ 2 : ℝ) : ℂ) * (edgeA 2 σ e * edgeA 2 τ e)))‖ ≤
        C * Real.exp (d / (2 * n) * (max t.re 0 * (isingMag σ ^ 2 + isingMag τ ^ 2) +
          ‖t‖ ^ 2 * isingMag (σ + τ) ^ 2)) := by
  refine ⟨Real.exp (d * T + d ^ 2 * TwoReplicaAux.Mc 2 T ^ 2 / 2), Real.exp_pos _,
    fun n hn σ τ t ht => ?_⟩
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hd hn
  have hfac : ∀ e : Sym2 (Fin n),
      1 + ((d / n : ℝ) : ℂ) * (t * edgeA 2 σ e + (starRingEnd ℂ) t * edgeA 2 τ e +
        ((‖t‖ ^ 2 : ℝ) : ℂ) * (edgeA 2 σ e * edgeA 2 τ e)) =
      1 + ((d / n : ℝ) : ℂ) *
        ((1 + t * edgeA 2 σ e) * (starRingEnd ℂ) (1 + t * edgeA 2 τ e) - 1) := by
    intro e
    rw [IsingSecondMoment_y_sub_one]
  rw [Finset.prod_congr rfl (fun e _ => hfac e), norm_prod, ← Real.exp_add]
  refine (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    (fun e _ => TwoReplicaAux.norm_one_add_le_exp _)).trans ?_
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.2 ?_
  rw [Finset.sum_add_distrib]
  have hM : ∀ e : Sym2 (Fin n),
      ‖(1 + t * edgeA 2 σ e) * (starRingEnd ℂ) (1 + t * edgeA 2 τ e) - 1‖ ≤
        TwoReplicaAux.Mc 2 T := fun e => TwoReplicaAux.norm_y_le_Mc le_rfl hT ht σ τ e
  have hquad := TwoReplicaAux.sum_quad_le hd hn
    (fun e => (1 + t * edgeA 2 σ e) * (starRingEnd ℂ) (1 + t * edgeA 2 τ e)) hM
  have hre : ∀ e : Sym2 (Fin n),
      (((d / n : ℝ) : ℂ) *
        ((1 + t * edgeA 2 σ e) * (starRingEnd ℂ) (1 + t * edgeA 2 τ e) - 1)).re =
        d / n * (t.re * TwoReplicaAux.aRe 2 σ e + t.re * TwoReplicaAux.aRe 2 τ e +
          ‖t‖ ^ 2 * (TwoReplicaAux.aRe 2 σ e * TwoReplicaAux.aRe 2 τ e)) := by
    intro e
    rw [Complex.re_ofReal_mul, TwoReplicaAux.edgeA_eq_ofReal, TwoReplicaAux.edgeA_eq_ofReal,
      TwoReplicaAux.re_y_sub_one]
  have hlin : ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
      (((d / n : ℝ) : ℂ) *
        ((1 + t * edgeA 2 σ e) * (starRingEnd ℂ) (1 + t * edgeA 2 τ e) - 1)).re =
      d / n * (t.re * ((isingMag σ ^ 2 - n) / 2) + t.re * ((isingMag τ ^ 2 - n) / 2) +
        ‖t‖ ^ 2 * ((isingMag (σ + τ) ^ 2 - n) / 2)) := by
    rw [Finset.sum_congr rfl (fun e _ => hre e), ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      IsingSecondMoment_sum_aRe, IsingSecondMoment_sum_aRe, IsingSecondMoment_sum_aRe_mul]
  rw [hlin]
  have hr : -t.re ≤ T :=
    (neg_le_abs t.re).trans ((Complex.abs_re_le_norm t).trans ht)
  exact IsingSecondMoment_final_ineq hd hn0 (sq_nonneg _) (sq_nonneg _) (sq_nonneg _) hr hquad

/-- Three-point Jensen inequality for `exp`: `e^{ax+by+cz} ≤ a e^x + b e^y + c e^z` for weights
`a, b, c ≥ 0` with `a + b + c = 1`.  It takes the place of Hölder's inequality in Step 2. -/
theorem exp_wsum3_le {a b c x y z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 1) :
    Real.exp (a * x + b * y + c * z) ≤ a * Real.exp x + b * Real.exp y + c * Real.exp z := by
  have h := (convexOn_exp).map_sum_le (t := (Finset.univ : Finset (Fin 3)))
    (w := ![a, b, c]) (p := ![x, y, z]) (fun i _ => by fin_cases i <;> simp [ha, hb, hc])
    (by simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ]; linarith) (fun i _ => Set.mem_univ _)
  simpa [Fin.sum_univ_succ, smul_eq_mul, add_assoc] using h

/-- A real number whose complex cast is `c ∑_σ ∑_τ F σ τ` is at most `‖c‖ ∑_σ ∑_τ ‖F σ τ‖`. -/
private lemma IsingSecondMoment_le_of_eq {ι : Type*} [Fintype ι] {x : ℝ} {c : ℂ}
    {F : ι → ι → ℂ} (h : (x : ℂ) = c * ∑ σ, ∑ τ, F σ τ) :
    x ≤ ‖c‖ * ∑ σ, ∑ τ, ‖F σ τ‖ := by
  calc x ≤ ‖(x : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
    _ = ‖c * ∑ σ, ∑ τ, F σ τ‖ := by rw [h]
    _ ≤ ‖c‖ * ∑ σ, ∑ τ, ‖F σ τ‖ := by
      rw [norm_mul]
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => norm_sum_le _ _)

/-- `∑_τ c = 2^n c` over `τ : Fin n → Fin 2`. -/
private lemma IsingSecondMoment_sum_const {n : ℕ} (c : ℝ) :
    ∑ _τ : Fin n → Fin 2, c = 2 ^ n * c := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  ring

/-- The convexity step of `ising_second_moment` (in place of Hölder): with `Λ = d(s + 2m)`,
`∑_{σ,τ} e^{X_{σ,τ}} ≤ 2^n ∑_σ e^{Λ S_σ²/(2n)}`, where
`X_{σ,τ} = (d/(2n)) (m(S_σ² + S_τ²) + s S_{σ+τ}²)`. -/
private lemma IsingSecondMoment_jensen_sum {n : ℕ} {d m s Λ : ℝ} (hd : 0 < d)
    (hn : (0 : ℝ) < n) (hm : 0 ≤ m) (hs : 0 ≤ s) (hΛ : Λ = d * (s + 2 * m)) :
    ∑ σ : Fin n → Fin 2, ∑ τ : Fin n → Fin 2,
        Real.exp (d / (2 * n) * (m * (isingMag σ ^ 2 + isingMag τ ^ 2) +
          s * isingMag (σ + τ) ^ 2)) ≤
      2 ^ n * ∑ σ : Fin n → Fin 2, Real.exp (Λ * isingMag σ ^ 2 / (2 * n)) := by
  have hA1 : ∑ σ : Fin n → Fin 2, ∑ _τ : Fin n → Fin 2,
      Real.exp (Λ * isingMag σ ^ 2 / (2 * n)) =
        2 ^ n * ∑ σ : Fin n → Fin 2, Real.exp (Λ * isingMag σ ^ 2 / (2 * n)) := by
    simp_rw [IsingSecondMoment_sum_const]
    rw [← Finset.mul_sum]
  have hA2 : ∑ _σ : Fin n → Fin 2, ∑ τ : Fin n → Fin 2,
      Real.exp (Λ * isingMag τ ^ 2 / (2 * n)) =
        2 ^ n * ∑ σ : Fin n → Fin 2, Real.exp (Λ * isingMag σ ^ 2 / (2 * n)) :=
    IsingSecondMoment_sum_const _
  have hA3 : ∑ σ : Fin n → Fin 2, ∑ τ : Fin n → Fin 2,
      Real.exp (Λ * isingMag (σ + τ) ^ 2 / (2 * n)) =
        2 ^ n * ∑ σ : Fin n → Fin 2, Real.exp (Λ * isingMag σ ^ 2 / (2 * n)) :=
    sum_sum_isingMag_add (fun x => Real.exp (Λ * x ^ 2 / (2 * n)))
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  rcases hΛ0.lt_or_eq with hpos | hzero
  · -- `Λ > 0`: three-point Jensen with weights `dm/Λ, dm/Λ, ds/Λ`
    have hsum : d * m / Λ + d * m / Λ + d * s / Λ = 1 := by
      rw [← add_div, ← add_div, div_eq_one_iff_eq hpos.ne', hΛ]
      ring
    have hpt : ∀ σ τ : Fin n → Fin 2,
        Real.exp (d / (2 * n) * (m * (isingMag σ ^ 2 + isingMag τ ^ 2) +
          s * isingMag (σ + τ) ^ 2)) ≤
        d * m / Λ * Real.exp (Λ * isingMag σ ^ 2 / (2 * n)) +
          d * m / Λ * Real.exp (Λ * isingMag τ ^ 2 / (2 * n)) +
          d * s / Λ * Real.exp (Λ * isingMag (σ + τ) ^ 2 / (2 * n)) := by
      intro σ τ
      have heq : d / (2 * n) * (m * (isingMag σ ^ 2 + isingMag τ ^ 2) +
          s * isingMag (σ + τ) ^ 2) =
          d * m / Λ * (Λ * isingMag σ ^ 2 / (2 * n)) +
            d * m / Λ * (Λ * isingMag τ ^ 2 / (2 * n)) +
            d * s / Λ * (Λ * isingMag (σ + τ) ^ 2 / (2 * n)) := by
        field_simp
      rw [heq]
      exact exp_wsum3_le (by positivity) (by positivity) (by positivity) hsum
    calc ∑ σ : Fin n → Fin 2, ∑ τ : Fin n → Fin 2,
          Real.exp (d / (2 * n) * (m * (isingMag σ ^ 2 + isingMag τ ^ 2) +
            s * isingMag (σ + τ) ^ 2))
        ≤ ∑ σ : Fin n → Fin 2, ∑ τ : Fin n → Fin 2,
          (d * m / Λ * Real.exp (Λ * isingMag σ ^ 2 / (2 * n)) +
            d * m / Λ * Real.exp (Λ * isingMag τ ^ 2 / (2 * n)) +
            d * s / Λ * Real.exp (Λ * isingMag (σ + τ) ^ 2 / (2 * n))) :=
          Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun τ _ => hpt σ τ
      _ = d * m / Λ * ∑ σ : Fin n → Fin 2, ∑ _τ : Fin n → Fin 2,
            Real.exp (Λ * isingMag σ ^ 2 / (2 * n)) +
          d * m / Λ * ∑ _σ : Fin n → Fin 2, ∑ τ : Fin n → Fin 2,
            Real.exp (Λ * isingMag τ ^ 2 / (2 * n)) +
          d * s / Λ * ∑ σ : Fin n → Fin 2, ∑ τ : Fin n → Fin 2,
            Real.exp (Λ * isingMag (σ + τ) ^ 2 / (2 * n)) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = (d * m / Λ + d * m / Λ + d * s / Λ) *
          (2 ^ n * ∑ σ : Fin n → Fin 2, Real.exp (Λ * isingMag σ ^ 2 / (2 * n))) := by
          rw [hA1, hA2, hA3]
          ring
      _ = 2 ^ n * ∑ σ : Fin n → Fin 2, Real.exp (Λ * isingMag σ ^ 2 / (2 * n)) := by
          rw [hsum, one_mul]
  · -- `Λ = 0`: then `m = s = 0` and both exponents vanish
    have h0 : s + 2 * m = 0 := by
      rcases mul_eq_zero.mp (hΛ ▸ hzero.symm) with h | h
      · exact absurd h hd.ne'
      · exact h
    have hs0 : s = 0 := by linarith
    have hm0 : m = 0 := by linarith
    have hpt : ∀ σ τ : Fin n → Fin 2,
        Real.exp (d / (2 * n) * (m * (isingMag σ ^ 2 + isingMag τ ^ 2) +
          s * isingMag (σ + τ) ^ 2)) = Real.exp (Λ * isingMag σ ^ 2 / (2 * n)) := by
      intro σ τ
      rw [← hzero, hs0, hm0]
      simp
    simp_rw [hpt]
    exact hA1.le

/-- **The second-moment bound of Step 2** (Section 7): `E|I_n(t)|² ≤ C (1 - Λ)^{-1/2}`,
`Λ = d(|t|² + 2(Re t)_+)`, for `|t| ≤ T`, `Λ < 1` and `n ≥ d`. -/
theorem ising_second_moment {d : ℝ} (hd : 0 < d) {T : ℝ} (hT : 0 ≤ T) :
    ∃ C > 0, ∀ n : ℕ, d ≤ n → ∀ t : ℂ, ‖t‖ ≤ T → d * (‖t‖ ^ 2 + 2 * max t.re 0) < 1 →
      erExp n (d / n) (fun G => ‖(zhat G 2).eval t‖ ^ 2) ≤
        C * (Real.sqrt (1 - d * (‖t‖ ^ 2 + 2 * max t.re 0)))⁻¹ := by
  obtain ⟨C, hC, hCb⟩ := ising_pair_bound hd hT
  refine ⟨C, hC, fun n hn t ht hΛ => ?_⟩
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hd hn
  have hΛ0 : 0 ≤ d * (‖t‖ ^ 2 + 2 * max t.re 0) := by positivity
  -- `ising_two_replica_identity` with `p = d/n`, then the triangle inequality
  have hE := IsingSecondMoment_le_of_eq (ising_two_replica_identity n (d / n) t)
  -- `ising_pair_bound` for every pair
  have hP : ∀ σ τ : Fin n → Fin 2,
      ‖∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
          (1 + ((d / n : ℝ) : ℂ) * (t * edgeA 2 σ e + (starRingEnd ℂ) t * edgeA 2 τ e +
            ((‖t‖ ^ 2 : ℝ) : ℂ) * (edgeA 2 σ e * edgeA 2 τ e)))‖ ≤
        C * Real.exp (d / (2 * n) * (max t.re 0 * (isingMag σ ^ 2 + isingMag τ ^ 2) +
          ‖t‖ ^ 2 * isingMag (σ + τ) ^ 2)) := fun σ τ => hCb n hn σ τ t ht
  -- the convexity step and `eq:rademacher-moment`
  have hJ := IsingSecondMoment_jensen_sum (n := n) hd hn0 (le_max_right t.re 0)
    (sq_nonneg ‖t‖) rfl
  have hR := rademacher_moment (n := n) hΛ0 hΛ
  have h4 : ‖((4 : ℂ) ^ n)⁻¹‖ = ((4 : ℝ) ^ n)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_ofNat]
  have h42 : ((4 : ℝ) ^ n)⁻¹ * 2 ^ n = ((2 : ℝ) ^ n)⁻¹ := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, mul_inv, mul_assoc,
      inv_mul_cancel₀ (by positivity), mul_one]
  refine hE.trans ?_
  rw [h4]
  calc ((4 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin 2, ∑ τ : Fin n → Fin 2,
        ‖∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
          (1 + ((d / n : ℝ) : ℂ) * (t * edgeA 2 σ e + (starRingEnd ℂ) t * edgeA 2 τ e +
            ((‖t‖ ^ 2 : ℝ) : ℂ) * (edgeA 2 σ e * edgeA 2 τ e)))‖
      ≤ ((4 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin 2, ∑ τ : Fin n → Fin 2,
          C * Real.exp (d / (2 * n) * (max t.re 0 * (isingMag σ ^ 2 + isingMag τ ^ 2) +
            ‖t‖ ^ 2 * isingMag (σ + τ) ^ 2)) := by
        gcongr with σ _ τ _
        exact hP σ τ
    _ = C * (((4 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin 2, ∑ τ : Fin n → Fin 2,
          Real.exp (d / (2 * n) * (max t.re 0 * (isingMag σ ^ 2 + isingMag τ ^ 2) +
            ‖t‖ ^ 2 * isingMag (σ + τ) ^ 2))) := by
        simp_rw [← Finset.mul_sum]
        ring
    _ ≤ C * (((4 : ℝ) ^ n)⁻¹ * (2 ^ n * ∑ σ : Fin n → Fin 2,
          Real.exp (d * (‖t‖ ^ 2 + 2 * max t.re 0) * isingMag σ ^ 2 / (2 * n)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJ (by positivity)) hC.le
    _ = C * (((2 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin 2,
          Real.exp (d * (‖t‖ ^ 2 + 2 * max t.re 0) * isingMag σ ^ 2 / (2 * n))) := by
        rw [← mul_assoc ((4 : ℝ) ^ n)⁻¹, h42]
    _ ≤ C * (Real.sqrt (1 - d * (‖t‖ ^ 2 + 2 * max t.re 0)))⁻¹ :=
        mul_le_mul_of_nonneg_left hR hC.le

end

end ERZeroFreeness
