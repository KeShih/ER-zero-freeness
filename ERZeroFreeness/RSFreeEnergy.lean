/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSPoisSplit
import ERZeroFreeness.RSBetheBasic
import ERZeroFreeness.RSTilt

/-!
# Appendix C: the planted free energy below condensation (`eq:rs-input`, Lemma C.3, last assertion)

* `rs_FlogF_le_cbar`: `E_{𝖯_s}[F log F] ≤ ∑_m Pois(sn/2)(m) c̄_m + s` for `n ≥ 2`, `x ∈ (0,1)`;
* `rs_FlogF_ge`: `E_{𝖯_s}[F log F] ≥ -1` (the paper has `-e⁻¹`; `-1` suffices);
* `rs_free_energy` (**`eq:rs-input`**, proved from the two bounds, `CKPZProp36` with `η = 0` and
  `rs_bethePsi_nonpos_of_lt_dCond`): `E_{𝖯_s}[F_G(x) log F_G(x)] = o(n)` for `x ∈ (0,1)` and
  `0 < s < d_cond(q,x)`.

## Proof of the two bounds

This is the paper's proof of Lemma C.3 ("Free energy").  Fix `x ∈ (0,1)`, `t = t(x)`; for an edge
list `e : Fin m → [n]²` write `F_e = rsSeqF q t e`, so `0 < F_e ≤ (3/2)^m` (`rs_rsF_bounds` via
`rs_rsF_edgeCount`).  Let `ā_m = n^{-2m} ∑_e F_e`, so that
`c̄_m = rsCbar q n m x = (n^{-2m} ∑_e F_e log F_e)/ā_m`.  The auxiliary lemmas are in the namespace
`RSFreeEnergyAux`.
* `ā_m ∈ [(1 - 1/n)^m, 1]` (`sum_seqF_bounds`): `∑_e F_e = q^{-n} ∑_σ G(σ)^m` with
  `G(σ) = ∑_{c ∈ [n]²} M_t(σ_{c.1}, σ_{c.2}) = n² + t ∑_{u,v} A_{σ_uσ_v} ∈ [0, n²]`
  (`Fintype.sum_pow`), so `ā_m = E_σ (1 + t q ‖α(σ) - u‖²)^m`.  Since `∑_σ A_{σ_uσ_v} = 0` for
  `u ≠ v` (`Equiv.funSplitAt`), `∑_σ G(σ) = q^n (n² + t n (q-1))`; the power-mean inequality
  `Real.pow_arith_mean_le_arith_mean_pow` (Jensen) and `t(q-1) ≥ -1` give the lower bound.
* `c̄_m ≥ log ā_m` (Jensen for `v log v`, as the summed tangent line `v log a + v - a ≤ v log v`
  at `a = ā_m`), and `c̄_m ≤ m log(3/2)`.
* `ā_m c̄_m ≤ c̄_m - log ā_m ≤ c̄_m + 2m/n` (`ā ≤ 1`, `ā log ā ≤ 0`, `-log(1 - 1/n) ≤ 2/n` for
  `n ≥ 2`), and `|c̄_m| ≤ m` (`per_m`).
* `rs_poisson_split` with `Φ = F log F` (summability: `|v log v| ≤ 1 + v²` and `F ≤ (3/2)^m`)
  gives `E_{𝖯_s}[F log F] = ∑_m Pois(sn/2)(m) ā_m c̄_m`; sum the previous bound
  (`∑_m Pois(sn/2)(m) · 2m/n = s`, `poisExp_natCast`; `|c̄_m| ≤ m` gives summability).
* Lower bound: `v log v ≥ v - 1 ≥ -1` pointwise, and `𝖯_s` has total mass one.
-/

open Polynomial Filter Topology Asymptotics

namespace ERZeroFreeness

open scoped Classical

noncomputable section

namespace RSFreeEnergyAux

/-- `|v log v| ≤ 1 + v²` for `v ≥ 0`. -/
lemma abs_mulLog_le {v : ℝ} (hv : 0 ≤ v) : |v * Real.log v| ≤ 1 + v ^ 2 := by
  rcases hv.eq_or_lt with rfl | hv'
  · simp
  · have h1 := Real.log_le_sub_one_of_pos hv'
    have h2 := Real.one_sub_inv_le_log_of_pos hv'
    have h3 : v * (1 - v⁻¹) ≤ v * Real.log v := mul_le_mul_of_nonneg_left h2 hv
    have h4 : v * Real.log v ≤ v * (v - 1) := mul_le_mul_of_nonneg_left h1 hv
    rw [mul_sub, mul_one, mul_inv_cancel₀ hv'.ne'] at h3
    rw [abs_le]
    constructor <;> nlinarith

/-- The edge list `e : Fin m → [n]²` has `m` edges. -/
lemma rsEdges_rsEdgeCount {n m : ℕ} (e : Fin m → Fin n × Fin n) :
    rsEdges (rsEdgeCount e) = m := by
  unfold rsEdges rsEdgeCount
  rw [← Finset.card_eq_sum_card_fiberwise (fun j _ => Finset.mem_univ (e j))]
  simp

/-- `0 < F_e ≤ (3/2)^m`. -/
lemma seqF_bounds {q n m : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (e : Fin m → Fin n × Fin n) :
    0 < rsSeqF q (tRe q x) e ∧ rsSeqF q (tRe q x) e ≤ (3 / 2) ^ m := by
  have h := rs_rsF_bounds hq hx0 hx1 (rsEdgeCount e)
  rw [rs_rsF_edgeCount, rsEdges_rsEdgeCount] at h
  exact ⟨lt_of_lt_of_le (pow_pos hx0 _) h.1, h.2⟩

/-- `∑_e F_e = q^{-n} ∑_σ (∑_c M_t(σ_{c.1}, σ_{c.2}))^m`. -/
lemma sum_seqF_eq (q n m : ℕ) (t : ℝ) :
    ∑ e : Fin m → Fin n × Fin n, rsSeqF q t e =
      ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q,
        (∑ c : Fin n × Fin n, rsM q t (σ c.1) (σ c.2)) ^ m := by
  unfold rsSeqF
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_pow]

lemma sum_sigma_rsA_of_ne {n q : ℕ} {u v : Fin n} (h : u ≠ v) :
    ∑ σ : Fin n → Fin q, ((rsA q (σ u) (σ v) : ℤ) : ℝ) = 0 := by
  rw [← (Equiv.funSplitAt v (Fin q)).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.funSplitAt_symm_apply, dif_pos, dif_neg h]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun σ' _ => rs_sum_rsA _ _

lemma sum_sigma_sum_rsA (n q : ℕ) :
    ∑ σ : Fin n → Fin q, ∑ u, ∑ v, ((rsA q (σ u) (σ v) : ℤ) : ℝ) =
      (q : ℝ) ^ n * (n * ((q : ℝ) - 1)) := by
  rw [Finset.sum_comm]
  have hu : ∀ u : Fin n, ∑ σ : Fin n → Fin q, ∑ v, ((rsA q (σ u) (σ v) : ℤ) : ℝ) =
      (q : ℝ) ^ n * ((q : ℝ) - 1) := by
    intro u
    rw [Finset.sum_comm, Finset.sum_eq_single u]
    · simp [rsA]
      ring
    · intro v _ hv
      exact sum_sigma_rsA_of_ne (Ne.symm hv)
    · simp
  rw [Finset.sum_congr rfl fun u _ => hu u]
  simp
  ring

lemma sum_rsM_eq (q n : ℕ) (t : ℝ) (σ : Fin n → Fin q) :
    ∑ c : Fin n × Fin n, rsM q t (σ c.1) (σ c.2) =
      (n : ℝ) ^ 2 + t * ∑ u, ∑ v, ((rsA q (σ u) (σ v) : ℤ) : ℝ) := by
  unfold rsM
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, mul_one]
  ring

/-- `0 ≤ G(σ) ≤ n²`, `G(σ) = ∑_{c ∈ [n]²} M_x(σ_{c.1}, σ_{c.2})`. -/
lemma G_bounds {q n : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (σ : Fin n → Fin q) :
    0 ≤ ∑ c : Fin n × Fin n, rsM q (tRe q x) (σ c.1) (σ c.2) ∧
      ∑ c : Fin n × Fin n, rsM q (tRe q x) (σ c.1) (σ c.2) ≤ (n : ℝ) ^ 2 := by
  constructor
  · exact Finset.sum_nonneg fun c _ => hx0.trans (rs_rsM_mem hq hx0 hx1 _ _).1
  · rw [sum_rsM_eq]
    have ht := rs_tRe_nonpos (by omega : 2 ≤ q) hx0 hx1
    have hA : 0 ≤ ∑ u, ∑ v, ((rsA q (σ u) (σ v) : ℤ) : ℝ) := by
      simp_rw [rs_rsA_cast_eq_aa]
      exact TwoReplicaAux.sum_aa_nonneg (by omega) σ
    nlinarith

/-- `∑_σ G(σ) = q^n (n² + t n (q-1))`. -/
lemma sum_G (q n : ℕ) (t : ℝ) :
    ∑ σ : Fin n → Fin q, ∑ c : Fin n × Fin n, rsM q t (σ c.1) (σ c.2) =
      (q : ℝ) ^ n * ((n : ℝ) ^ 2 + t * (n * ((q : ℝ) - 1))) := by
  simp_rw [sum_rsM_eq]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_sigma_sum_rsA]
  simp
  ring

/-- `(n² - n)^m ≤ ∑_e F_e ≤ (n²)^m`, i.e. `ā_m ∈ [(1 - 1/n)^m, 1]`. -/
lemma sum_seqF_bounds {q n : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    ((n : ℝ) ^ 2 - n) ^ m ≤ ∑ e : Fin m → Fin n × Fin n, rsSeqF q (tRe q x) e ∧
      ∑ e : Fin m → Fin n × Fin n, rsSeqF q (tRe q x) e ≤ ((n : ℝ) ^ 2) ^ m := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hQ : (0 : ℝ) < (q : ℝ) ^ n := pow_pos hq0 n
  have hcard : ((Finset.univ : Finset (Fin n → Fin q)).card : ℝ) = (q : ℝ) ^ n := by simp
  have hG := fun σ => G_bounds (n := n) hq hx0 hx1 σ
  rw [sum_seqF_eq]
  constructor
  · have hw : ∑ _σ ∈ (Finset.univ : Finset (Fin n → Fin q)), ((q : ℝ) ^ n)⁻¹ = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard, mul_inv_cancel₀ hQ.ne']
    have hpm := Real.pow_arith_mean_le_arith_mean_pow (Finset.univ : Finset (Fin n → Fin q))
      (fun _ => ((q : ℝ) ^ n)⁻¹)
      (fun σ => ∑ c : Fin n × Fin n, rsM q (tRe q x) (σ c.1) (σ c.2))
      (fun _ _ => by positivity) hw (fun σ _ => (hG σ).1) m
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_G, inv_mul_cancel_left₀ hQ.ne'] at hpm
    refine le_trans ?_ hpm
    have hnn : (0 : ℝ) ≤ (n : ℝ) ^ 2 - n := by
      have : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
        rcases Nat.eq_zero_or_pos n with h | h
        · simp [h]
        · have : (1 : ℝ) ≤ n := by exact_mod_cast h
          nlinarith
      linarith
    apply pow_le_pow_left₀ hnn
    have ht := rs_tRe_ge (by omega : 2 ≤ q) hx0
    have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
      have : (3 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    have htq : 0 ≤ tRe q x * ((q : ℝ) - 1) + 1 := by
      rw [div_le_iff₀ hq1] at ht
      linarith
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_nonneg hn0 htq]
  · rw [inv_mul_le_iff₀ hQ]
    calc ∑ σ : Fin n → Fin q, (∑ c : Fin n × Fin n, rsM q (tRe q x) (σ c.1) (σ c.2)) ^ m
        ≤ ∑ _σ : Fin n → Fin q, ((n : ℝ) ^ 2) ^ m :=
          Finset.sum_le_sum fun σ _ => pow_le_pow_left₀ (hG σ).1 (hG σ).2 m
      _ = (q : ℝ) ^ n * ((n : ℝ) ^ 2) ^ m := by rw [Finset.sum_const, nsmul_eq_mul, hcard]

/-- Tangent line of `v log v` at `a > 0`: `v log a + v - a ≤ v log v` for `v ≥ 0`. -/
lemma mulLog_tangent {v a : ℝ} (hv : 0 ≤ v) (ha : 0 < a) :
    v * Real.log a + v - a ≤ v * Real.log v := by
  rcases hv.eq_or_lt with rfl | hv'
  · simp
    linarith
  · have h := Real.one_sub_inv_le_log_of_pos (div_pos hv' ha)
    rw [Real.log_div hv'.ne' ha.ne', inv_div] at h
    have h2 : v * (1 - a / v) ≤ v * (Real.log v - Real.log a) := mul_le_mul_of_nonneg_left h hv
    have h3 : v * (a / v) = a := by field_simp
    rw [mul_sub, mul_one, h3, mul_sub] at h2
    linarith

/-- Jensen for `v log v` on a finite family: `S log(S/K) ≤ ∑_i v_i log v_i`, where
`S = ∑_i v_i > 0` and `K = #ι`. -/
lemma sum_mulLog_ge {ι : Type*} [Fintype ι] (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hS : 0 < ∑ i, v i) :
    (∑ i, v i) * Real.log ((∑ i, v i) / Fintype.card ι) ≤ ∑ i, v i * Real.log (v i) := by
  have hK : (0 : ℝ) < Fintype.card ι := by
    rcases isEmpty_or_nonempty ι with h | h
    · simp at hS
    · exact_mod_cast Fintype.card_pos
  set a := (∑ i, v i) / Fintype.card ι with ha_def
  have ha : 0 < a := div_pos hS hK
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => mulLog_tangent (hv i) ha
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at h
  have hKa : (Fintype.card ι : ℝ) * a = ∑ i, v i := by
    rw [ha_def]
    field_simp
  linarith

/-- Per-`m` bound (proof of Lemma C.3, "Free energy"): with `S = ∑_e F_e`, `T = ∑_e F_e log F_e`,
`K = n^{2m}`, `ā = S/K ∈ [(1-1/n)^m, 1]` and `c̄ = T/S ≥ log ā`:
`T/K = ā c̄ ≤ c̄ + 2m/n` and `|c̄| ≤ m` (`n ≥ 2`). -/
lemma per_m {q n : ℕ} (hq : 3 ≤ q) (hn : 2 ≤ n) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (m : ℕ) :
    ((n : ℝ) ^ (2 * m))⁻¹ * ∑ e : Fin m → Fin n × Fin n,
        rsSeqF q (tRe q x) e * Real.log (rsSeqF q (tRe q x) e) ≤
      rsCbar q n m x + 2 * m / n ∧ |rsCbar q n m x| ≤ m := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set S := ∑ e : Fin m → Fin n × Fin n, rsSeqF q (tRe q x) e with hSdef
  set T := ∑ e : Fin m → Fin n × Fin n,
    rsSeqF q (tRe q x) e * Real.log (rsSeqF q (tRe q x) e) with hTdef
  have hc : rsCbar q n m x = T / S := rfl
  rw [hc]
  set K := (n : ℝ) ^ (2 * m) with hKdef
  have hK2 : K = ((n : ℝ) ^ 2) ^ m := by rw [hKdef, pow_mul]
  have hK0 : 0 < K := by positivity
  have hcard : (Fintype.card (Fin m → Fin n × Fin n) : ℝ) = K := by
    rw [hK2]
    simp [Fintype.card_prod, Fintype.card_fin]
    ring
  have hF := fun e : Fin m → Fin n × Fin n => seqF_bounds hq hx0 hx1 e
  obtain ⟨hSlo, hSup⟩ := sum_seqF_bounds (n := n) hq hx0.le hx1 m
  set r := 1 - 1 / (n : ℝ) with hr
  have hr0 : 1 / 2 ≤ r := by
    have : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn'
    rw [hr]
    linarith
  have hnr : (n : ℝ) ^ 2 - n = (n : ℝ) ^ 2 * r := by
    rw [hr]
    field_simp
  have hSlo' : K * r ^ m ≤ S := by
    rw [hK2, ← mul_pow, ← hnr]
    exact hSlo
  have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hSlo'
  set a := S / K with ha_def
  have ha0 : 0 < a := div_pos hS0 hK0
  have ha1 : a ≤ 1 := by
    rw [ha_def, div_le_one hK0, hK2]
    exact hSup
  have har : r ^ m ≤ a := by
    rw [ha_def, le_div_iff₀ hK0]
    linarith [hSlo']
  have hlogr : -(2 / (n : ℝ)) ≤ Real.log r := by
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < r by linarith)
    have hrn : r = ((n : ℝ) - 1) / n := by
      rw [hr]
      field_simp
    have hinv : r⁻¹ = (n : ℝ) / ((n : ℝ) - 1) := by rw [hrn, inv_div]
    have h2 : r⁻¹ ≤ 1 + 2 / (n : ℝ) := by
      rw [hinv, div_le_iff₀ (by linarith : (0 : ℝ) < n - 1)]
      have e : (1 + 2 / (n : ℝ)) * ((n : ℝ) - 1) = n + 1 - 2 / n := by
        field_simp
        ring
      rw [e]
      have : 2 / (n : ℝ) ≤ 1 := by
        rw [div_le_one hn0]
        exact hn'
      linarith
    linarith
  have hloga : -(2 * m / (n : ℝ)) ≤ Real.log a := by
    have h1 : Real.log (r ^ m) ≤ Real.log a := Real.log_le_log (by positivity) har
    rw [Real.log_pow] at h1
    have h2 : (m : ℝ) * (-(2 / (n : ℝ))) ≤ m * Real.log r := mul_le_mul_of_nonneg_left hlogr hm0
    have h3 : (m : ℝ) * (-(2 / (n : ℝ))) = -(2 * m / n) := by ring
    linarith
  have hloga0 : Real.log a ≤ 0 := Real.log_nonpos ha0.le ha1
  have hJ : S * Real.log a ≤ T := by
    have h := sum_mulLog_ge (fun e : Fin m → Fin n × Fin n => rsSeqF q (tRe q x) e)
      (fun e => (hF e).1.le) hS0
    rw [hcard] at h
    exact h
  have hca : Real.log a ≤ T / S := by
    rw [le_div_iff₀ hS0]
    linarith
  have hlog32 : Real.log (3 / 2) ≤ 1 / 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
    linarith
  have hT : T ≤ S * (m * Real.log (3 / 2)) := by
    rw [hTdef, hSdef, Finset.sum_mul]
    refine Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left ?_ (hF e).1.le
    rw [← Real.log_pow]
    exact Real.log_le_log (hF e).1 (hF e).2
  have hcu : T / S ≤ m / 2 := by
    rw [div_le_iff₀ hS0]
    have : (m : ℝ) * Real.log (3 / 2) ≤ m * (1 / 2) := mul_le_mul_of_nonneg_left hlog32 hm0
    nlinarith
  have hTK : K⁻¹ * T = a * (T / S) := by
    rw [ha_def]
    field_simp
  constructor
  · rw [hTK]
    have h1 : (a - 1) * (T / S - Real.log a) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    have h2 : a * Real.log a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha0.le hloga0
    nlinarith
  · rw [abs_le]
    have : 2 * (m : ℝ) / n ≤ m := by
      rw [div_le_iff₀ hn0]
      nlinarith
    constructor <;> linarith

end RSFreeEnergyAux

open RSFreeEnergyAux

/-- Upper bound of the Poisson free energy by the planted free energy of the `m`-edge model:
`E_{𝖯_s}[F log F] ≤ ∑_m Pois(sn/2)(m) c̄_m + s` (`n ≥ 2`, `x ∈ (0,1)`, `s ≥ 0`). -/
theorem rs_FlogF_le_cbar {q n : ℕ} (hq : 3 ≤ q) (hn : 2 ≤ n) {x s : ℝ} (hx0 : 0 < x)
    (hx1 : x < 1) (hs : 0 ≤ s) :
    rsExp n s (fun N => rsF q (tRe q x) N * Real.log (rsF q (tRe q x) N)) ≤
      (∑' m : ℕ, poisPMF (s * n / 2) m * rsCbar q n m x) + s := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlam : 0 ≤ s * n / 2 := by positivity
  have hpois : ∀ m, 0 ≤ poisPMF (s * n / 2) m := poisPMF_nonneg hlam
  have hF := fun (m : ℕ) (e : Fin m → Fin n × Fin n) => seqF_bounds hq hx0 hx1.le e
  -- the dominating series `∑_m Pois(m) (1 + (9/4)^m)`
  have hdom : Summable fun m : ℕ => poisPMF (s * n / 2) m * (1 + (9 / 4) ^ m) := by
    have h := (hasSum_poisPMF hlam).summable.add
      (RSPoisPiAux.hasSum_poisPMF_mul_pow (lam := s * n / 2) (9 / 4)).summable
    refine h.congr fun m => ?_
    ring
  have hinner : ∀ m : ℕ, ((n : ℝ) ^ (2 * m))⁻¹ * ∑ e : Fin m → Fin n × Fin n,
      |rsSeqF q (tRe q x) e * Real.log (rsSeqF q (tRe q x) e)| ≤ 1 + (9 / 4) ^ m := by
    intro m
    have hK0 : (0 : ℝ) < (n : ℝ) ^ (2 * m) := by positivity
    have hcard : ((Finset.univ : Finset (Fin m → Fin n × Fin n)).card : ℝ) =
        (n : ℝ) ^ (2 * m) := by
      rw [pow_mul]
      simp [Fintype.card_prod, Fintype.card_fin]
      ring
    rw [inv_mul_le_iff₀ hK0]
    calc ∑ e : Fin m → Fin n × Fin n, |rsSeqF q (tRe q x) e * Real.log (rsSeqF q (tRe q x) e)|
        ≤ ∑ _e : Fin m → Fin n × Fin n, (1 + (9 / 4 : ℝ) ^ m) := by
          refine Finset.sum_le_sum fun e _ => ?_
          have h1 := abs_mulLog_le (hF m e).1.le
          have h2 : rsSeqF q (tRe q x) e ^ 2 ≤ ((3 / 2 : ℝ) ^ m) ^ 2 :=
            pow_le_pow_left₀ (hF m e).1.le (hF m e).2 2
          have h3 : ((3 / 2 : ℝ) ^ m) ^ 2 = (9 / 4) ^ m := by
            rw [← pow_mul, mul_comm, pow_mul]
            norm_num
          linarith
      _ = (n : ℝ) ^ (2 * m) * (1 + (9 / 4) ^ m) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have hΦ' : Summable fun m : ℕ => poisPMF (s * n / 2) m *
      (((n : ℝ) ^ (2 * m))⁻¹ * ∑ e : Fin m → Fin n × Fin n,
        |rsSeqF q (tRe q x) e * Real.log (rsSeqF q (tRe q x) e)|) := by
    refine hdom.of_nonneg_of_le (fun m => mul_nonneg (hpois m) (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun e _ => abs_nonneg _))) (fun m => ?_)
    exact mul_le_mul_of_nonneg_left (hinner m) (hpois m)
  have hΦ : Summable fun m : ℕ => poisPMF (s * n / 2) m *
      (((n : ℝ) ^ (2 * m))⁻¹ * ∑ e : Fin m → Fin n × Fin n,
        |(fun N : RSGraph n => rsF q (tRe q x) N * Real.log (rsF q (tRe q x) N))
          (rsEdgeCount e)|) := by
    simpa only [rs_rsF_edgeCount] using hΦ'
  obtain ⟨_, hsplit⟩ := rs_poisson_split hs
    (fun N : RSGraph n => rsF q (tRe q x) N * Real.log (rsF q (tRe q x) N)) hΦ
  rw [hsplit]
  simp only [rs_rsF_edgeCount]
  -- summability of the three series
  have hPm : Summable fun m : ℕ => poisPMF (s * n / 2) m * (m : ℝ) := by
    simpa using summable_poisPMF_mul_pow hlam 1
  have hA : Summable fun m : ℕ => poisPMF (s * n / 2) m * rsCbar q n m x := by
    refine Summable.of_norm_bounded hPm fun m => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpois m)]
    exact mul_le_mul_of_nonneg_left (per_m hq hn hx0 hx1.le m).2 (hpois m)
  have hB : Summable fun m : ℕ => poisPMF (s * n / 2) m * (2 * m / n) := by
    refine (hPm.mul_left (2 / (n : ℝ))).congr fun m => ?_
    ring
  have hL : Summable fun m : ℕ => poisPMF (s * n / 2) m *
      (((n : ℝ) ^ (2 * m))⁻¹ * ∑ e : Fin m → Fin n × Fin n,
        rsSeqF q (tRe q x) e * Real.log (rsSeqF q (tRe q x) e)) := by
    refine Summable.of_norm_bounded hΦ' fun m => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hpois m)]
    refine mul_le_mul_of_nonneg_left ?_ (hpois m)
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
  have hBval : ∑' m : ℕ, poisPMF (s * n / 2) m * (2 * m / n) = s := by
    have h := poisExp_natCast hlam
    unfold poisExp at h
    calc ∑' m : ℕ, poisPMF (s * n / 2) m * (2 * m / n)
        = ∑' m : ℕ, 2 / n * (poisPMF (s * n / 2) m * m) := tsum_congr fun m => by ring
      _ = 2 / n * (s * n / 2) := by rw [tsum_mul_left, h]
      _ = s := by field_simp
  calc ∑' m : ℕ, poisPMF (s * n / 2) m *
        (((n : ℝ) ^ (2 * m))⁻¹ * ∑ e : Fin m → Fin n × Fin n,
          rsSeqF q (tRe q x) e * Real.log (rsSeqF q (tRe q x) e))
      ≤ ∑' m : ℕ, (poisPMF (s * n / 2) m * rsCbar q n m x +
          poisPMF (s * n / 2) m * (2 * m / n)) := by
        refine Summable.tsum_le_tsum (fun m => ?_) hL (hA.add hB)
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (per_m hq hn hx0 hx1.le m).1 (hpois m)
    _ = (∑' m : ℕ, poisPMF (s * n / 2) m * rsCbar q n m x) + s := by
        rw [hA.tsum_add hB, hBval]

/-- `E_{𝖯_s}[F log F] ≥ -1` at a real anchor `x ∈ (0,1]`. -/
theorem rs_FlogF_ge {q n : ℕ} (hq : 3 ≤ q) {x s : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hs : 0 ≤ s) :
    -1 ≤ rsExp n s (fun N => rsF q (tRe q x) N * Real.log (rsF q (tRe q x) N)) := by
  have hlam : ∀ i, 0 ≤ rsMean n s i := fun i => by
    unfold rsMean
    positivity
  have hF := fun N : RSGraph n => rs_rsF_bounds hq hx0 hx1 N
  have hFpos : ∀ N : RSGraph n, 0 < rsF q (tRe q x) N := fun N =>
    lt_of_lt_of_le (pow_pos hx0 _) (hF N).1
  have hsum : Summable fun N => poisPi (rsMean n s) N *
      (rsF q (tRe q x) N * Real.log (rsF q (tRe q x) N)) := by
    refine rs_summable_poisPi_of_abs_le hlam (A := 2) (c := 9 / 4) (by norm_num) fun N => ?_
    have h1 := abs_mulLog_le (hFpos N).le
    have h2 : rsF q (tRe q x) N ^ 2 ≤ ((3 / 2 : ℝ) ^ rsEdges N) ^ 2 :=
      pow_le_pow_left₀ (hFpos N).le (hF N).2 2
    have h3 : ((3 / 2 : ℝ) ^ rsEdges N) ^ 2 = (9 / 4) ^ (∑ i, N i) := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
      rfl
    have h4 : (1 : ℝ) ≤ (9 / 4) ^ (∑ i, N i) := one_le_pow₀ (by norm_num)
    linarith
  have hc : Summable fun N => poisPi (rsMean n s) N * (-1 : ℝ) :=
    (rs_hasSum_poisPi hlam).summable.mul_right _
  calc (-1 : ℝ) = poisPiExp (rsMean n s) (fun _ => -1) := (rs_poisPiExp_const hlam (-1)).symm
    _ ≤ poisPiExp (rsMean n s) (fun N => rsF q (tRe q x) N * Real.log (rsF q (tRe q x) N)) := by
        refine rs_poisPiExp_mono hlam hc hsum fun N => ?_
        have := Real.self_sub_one_le_mul_log (hFpos N).le
        linarith [hFpos N]

/-- **`eq:rs-input` (Lemma C.3).** Assuming [CKPZ, Prop. 3.6] (`CKPZProp36`), for `x ∈ (0,1)` and
`0 < s < d_cond(q,x)`: `E_{𝖯_s}[F_G(x) log F_G(x)] = o(n)`.  The hypothesis is proved by
`ckpz_prop36` (`CKMain`); the unconditional form is `rs_free_energy_unconditional` (`AppendixC`). -/
theorem rs_free_energy {q : ℕ} (hq : 3 ≤ q) (hCKPZ : CKPZProp36 q) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 1) {s : ℝ} (hs0 : 0 < s) (hs : s < dCond q x) :
    (fun n : ℕ => rsExp n s (fun N => rsF q (tRe q x) N * Real.log (rsF q (tRe q x) N)))
      =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  rw [isLittleO_iff]
  intro ε hε
  have hck := hCKPZ x hx0 hx1 s hs0 0 (rs_bethePsi_nonpos_of_lt_dCond hs0 hs) (ε / 2)
    (half_pos hε)
  filter_upwards [hck, eventually_ge_atTop 2, eventually_ge_atTop ⌈2 * s / ε⌉₊,
    eventually_ge_atTop ⌈1 / ε⌉₊] with n hn hn2 hns hn1
  have hup := rs_FlogF_le_cbar hq hn2 hx0 hx1 hs0.le
  have hlo := rs_FlogF_ge (n := n) hq hx0 hx1.le hs0.le
  have h1 : 1 ≤ ε * n := by
    have : 1 / ε ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn1)
    rw [div_le_iff₀ hε] at this
    linarith
  have h2 : 2 * s ≤ ε * n := by
    have : 2 * s / ε ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hns)
    rw [div_le_iff₀ hε] at this
    linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Nat.abs_cast, abs_le]
  constructor <;> nlinarith

end

end ERZeroFreeness
