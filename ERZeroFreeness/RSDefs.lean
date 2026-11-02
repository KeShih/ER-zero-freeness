/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs

/-!
# Appendix C (`app:rs-extension`): definitions

Definitions for Appendix C of the paper, *Extension to the condensation threshold*:
zero-freeness of the Potts partition function on `G(n, d/n)` near `[x_*, 1]` for every
`d < d_cond(q, x_*)` (Theorem C.1 `thm:rs-extension`, zero-freeness part; the counting part is
not formalized).  This file defines the objects shared by the Appendix C modules and the
hypothesis `CKPZProp36` ([CKPZ, Prop. 3.6]).

## Conventions

* **The `t`-plane.**  `M_z = J + t(z) A` depends on `z` only through `t = t(z) = (z-1)/(z+q-1)`
  (`tOf`).  All multigraph objects (`rsW`, `rsF`, `rsH`, …) are therefore functions of `t`
  (over `ℝ` at real anchors, over `ℂ` near them), and Lemma C.4 is stated in the `t`-plane
  around `I_{s_*} = t([x_*,1]) = [t(x_*), 0]`.  A real anchor `x ∈ (0,1]` corresponds to
  `t = tRe q x ∈ (-1/(q-1), 0]`.
* **Expectations are explicit sums.**  Laws on the countable spaces `ι → ℕ` are explicit product
  mass functions (`poisPi`), expectations are real `tsum`s (`poisPiExp`, `rsExp`, `cpExp`); there
  are no conditional expectations.  A real `tsum` has the junk value `0` on non-summable
  families; every family occurring in the main statements is summable (all integrands are
  bounded by `A·c^m`, `m` the number of edges), and results used as upper bounds either include
  the summability or leave it to be derived from `rs_summable_poisPi_of_abs_le`.
* **No `sSup` of possibly unbounded sets.**  "`sup_ν Ψ(ν) > 0`" is encoded as
  "`∃ ν ∈ 𝒫_u, Ψ(ν) > 0`" and "`sup_ν Ψ(ν) ≤ η`" as "`∀ ν ∈ 𝒫_u, Ψ(ν) ≤ η`".  The only `sInf` is
  `dCond`, the infimum of a set of positive reals; it is nonempty for `x ∈ [0,1)` by the
  Kesten–Stigum certificate `rs_ks_certificate`, so Lean's `sInf ∅ = 0` is never reached there.
* **Multigraphs** are `RSGraph n = Fin n × Fin n → ℕ`: edge counts on all `n²` ordered pairs,
  loops included, exactly as in the paper (`𝖯_s` before `eq:rs-model`).
-/

open Polynomial Filter Topology MeasureTheory

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-! ## The edge matrix `M_t = J + tA` -/

section Matrix

/-- The entries `A_{ab} = q·[a = b] - 1` of `A = q·Id - J` (Section 2 of the paper), as integers so
that they can be cast into `ℝ` and `ℂ`. -/
def rsA (q : ℕ) (a b : Fin q) : ℤ := if a = b then (q : ℤ) - 1 else -1

/-- `M_t(a,b) = 1 + t·A_{ab}`, i.e. the normalized edge matrix `M = J + tA`, over any ring.
The paper's `M_z` (Appendix C, before `eq:bethe-condensation`) is `rsM q (tOf q z)`; for
`z ≠ -(q-1)` its diagonal entries are `z / b(z)` and its off-diagonal entries `1 / b(z)`, and all
its row sums equal `q`.  At a real point `x ∈ [0,1]` the paper's `M_x` is `rsM q (tRe q x)`, whose
entries lie in `[x, 3/2]` when `q ≥ 3`. -/
def rsM {R : Type*} [Ring R] (q : ℕ) (t : R) (a b : Fin q) : R := 1 + t * (rsA q a b : R)

/-- The real transformed parameter `t(x) = (x - 1)/(x + q - 1)` (Section 2); for real `x`,
`tOf q (x : ℂ) = (tRe q x : ℂ)`.  For `q ≥ 3` it maps `[0,1]` increasingly onto `[-1/(q-1), 0]`. -/
def tRe (q : ℕ) (x : ℝ) : ℝ := (x - 1) / (x + q - 1)

end Matrix

/-! ## The Bethe functional and the condensation threshold (`eq:bethe-condensation`) -/

section Bethe

/-- The probability simplex `{μ ∈ [0,1]^q : ∑_a μ_a = 1}` as a (compact, Borel) measurable space. -/
abbrev rsSimplex (q : ℕ) : Type := ↥(stdSimplex ℝ (Fin q))

/-- `(M_t μ)_a = ∑_b M_t(a,b) μ_b`. -/
def betheMvec (q : ℕ) (t : ℝ) (μ : Fin q → ℝ) (a : Fin q) : ℝ := ∑ b, rsM q t a b * μ b

/-- `V_k = q⁻¹ ∑_a ∏_{i<k} (M_t μ_i)_a` (`eq:bethe-condensation`; `V_0 = 1`). -/
def betheV (q : ℕ) (t : ℝ) {k : ℕ} (μ : Fin k → Fin q → ℝ) : ℝ :=
  (q : ℝ)⁻¹ * ∑ a, ∏ i, betheMvec q t (μ i) a

/-- `E = μ₁ᵀ M_t μ₂` (`eq:bethe-condensation`, `E_x` at `t = t(x)`). -/
def betheE (q : ℕ) (t : ℝ) (μ₁ μ₂ : Fin q → ℝ) : ℝ := ∑ a, μ₁ a * betheMvec q t μ₂ a

/-- `𝒫_u`: the Borel probability measures `ν` on the simplex with mean
`E_{μ∼ν}[μ] = u = (1/q, …, 1/q)` (CKPZ's `𝒫²_*([q])`). -/
def rsPu (q : ℕ) : Set (ProbabilityMeasure (rsSimplex q)) :=
  {ν | ∀ a : Fin q, ∫ μ, (μ : Fin q → ℝ) a ∂(ν : Measure (rsSimplex q)) = (q : ℝ)⁻¹}

/-- **`eq:bethe-condensation`, first line.** The normalized Potts Bethe functional
`Ψ_{r,x}(ν) = E[V_D log V_D] - (r/2) E[E_x log E_x]` (with `0 log 0 = 0`), where
`μ_1, μ_2, … ∼ ν` are i.i.d. and independent of `D ∼ Pois(r)`.  The random degree is written out:
`E[V_D log V_D] = ∑_k P(D = k) ∫ V_k log V_k dν^{⊗k}` (a `poisPMF`-weighted `tsum` of integrals
against the finite product measures `ν^{⊗k}`), and `E_x = μ_1ᵀ M_x μ_2` is integrated against
`ν^{⊗2}`.  Here `M_x = rsM q (tRe q x)`.  For `x ∈ [0,1]` and `q ≥ 3` all integrands are bounded
continuous functions on compact spaces (`0 ≤ V_k ≤ (3/2)^k`, `0 ≤ E_x ≤ 3/2`) and the `k`-series
converges absolutely (`rs_summable_bethe_series`); for other `x` the value is not used. -/
def bethePsi (q : ℕ) (r x : ℝ) (ν : ProbabilityMeasure (rsSimplex q)) : ℝ :=
  (∑' k : ℕ, poisPMF r k *
      ∫ μ : Fin k → rsSimplex q,
        betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)) *
          Real.log (betheV q (tRe q x) (fun i => (μ i : Fin q → ℝ)))
        ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q)))) -
    r / 2 * ∫ μ : Fin 2 → rsSimplex q,
        betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ) *
          Real.log (betheE q (tRe q x) (μ 0 : Fin q → ℝ) (μ 1 : Fin q → ℝ))
        ∂(Measure.pi fun _ => (ν : Measure (rsSimplex q)))

/-- **`eq:bethe-condensation`, second line.** The Erdős–Rényi Potts condensation threshold
`d_cond(q,x) = inf {r > 0 : sup_{ν ∈ 𝒫_u} Ψ_{r,x}(ν) > 0}`, with "`sup_ν Ψ > 0`" encoded as
"`∃ ν ∈ 𝒫_u, Ψ(ν) > 0`".  The set is bounded below by `0`; for `x ∈ [0,1)` it is nonempty
(`rs_ks_certificate`), so this is the true infimum (Lean's `sInf ∅ = 0` would only make the
hypothesis `d < dCond q x` unsatisfiable, never a theorem false). -/
def dCond (q : ℕ) (x : ℝ) : ℝ :=
  sInf {r : ℝ | 0 < r ∧ ∃ ν ∈ rsPu q, 0 < bethePsi q r x ν}

end Bethe

/-! ## Product Poisson laws and conditional-Poisson multigraphs -/

section PoissonField

/-- The product Poisson mass function on `ι → ℕ`: independent `N_i ∼ Pois(lam_i)`.  On `ι = Fin r`
it is `poisProd`; on `ι = Fin n × Fin n` it is the law of an ordered Poisson multigraph. -/
def poisPi {ι : Type*} [Fintype ι] (lam : ι → ℝ) (N : ι → ℕ) : ℝ :=
  ∏ i, poisPMF (lam i) (N i)

/-- `E f(N)` for independent `N_i ∼ Pois(lam_i)`, as a real `tsum` (junk value `0` when the family
`N ↦ poisPi lam N * f N` is not summable). -/
def poisPiExp {ι : Type*} [Fintype ι] (lam : ι → ℝ) (f : (ι → ℕ) → ℝ) : ℝ :=
  ∑' N, poisPi lam N * f N

/-- `f` changes by at most `B` when a single coordinate is increased by one (one added edge, loops
included): the bounded-difference hypothesis `|f(G+e) - f(G)| ≤ B` of Lemma C.6.  Stated without
`Pi.single` so that no `DecidableEq ι` instance is involved. -/
def EdgeLip {ι : Type*} (B : ℝ) (f : (ι → ℕ) → ℝ) : Prop :=
  ∀ (N N' : ι → ℕ) (i : ι), (∀ j, j ≠ i → N' j = N j) → N' i = N i + 1 → |f N' - f N| ≤ B

/-- `Φ` changes by at most `c` when a single label is changed. -/
def BddDiff {ι S : Type*} (c : ℝ) (Φ : (ι → S) → ℝ) : Prop :=
  ∀ (ξ ξ' : ι → S) (v : ι), (∀ w, w ≠ v → ξ' w = ξ w) → |Φ ξ' - Φ ξ| ≤ c

end PoissonField

/-! ## Ordered Poisson multigraphs, weights and partition functions (`eq:rs-model`) -/

section Multigraph

/-- An ordered multigraph on `[n]`: edge counts `N_{uv}` on all `n²` ordered pairs `(u,v)`,
loops included (Appendix C, before `eq:rs-model`). -/
abbrev RSGraph (n : ℕ) : Type := Fin n × Fin n → ℕ

/-- The number of edges `m = |E(G)| = ∑_{(u,v)} N_{uv}`. -/
def rsEdges {n : ℕ} (N : RSGraph n) : ℕ := ∑ uv, N uv

/-- The edge means `s/(2n)` of the ordered Poisson multigraph `𝖯_s` (so `m ∼ Pois(sn/2)`). -/
def rsMean (n : ℕ) (s : ℝ) : Fin n × Fin n → ℝ := fun _ => s / (2 * n)

/-- `E_{𝖯_s}[f(G)]`: independent `N_{uv} ∼ Pois(s/(2n))` on all ordered pairs, loops included. -/
def rsExp (n : ℕ) (s : ℝ) (f : RSGraph n → ℝ) : ℝ := poisPiExp (rsMean n s) f

/-- Edge means `K(ξ_u, ξ_v)/(2n)` of a multigraph whose edge counts are Poisson given vertex labels
`ξ` (Lemma C.6 `lem:rs-conc`).  The tilted laws of `app:rs-poisson` are instances:
`𝖯^σ_s = cpMean (fun a b => s * rsM q t a b) σ` and
`𝖯^{σ,τ}_s = cpMean (rsPairK q s t) (fun v => (σ v, τ v))`. -/
def cpMean {n : ℕ} {S : Type*} (K : S → S → ℝ) (ξ : Fin n → S) : Fin n × Fin n → ℝ :=
  fun e => K (ξ e.1) (ξ e.2) / (2 * n)

/-- `E F(ξ, G)` when the labels `ξ_v ∼ p v` are independent and, given `ξ`, the multigraph `G` has
independent `Pois(K(ξ_u,ξ_v)/(2n))` edge counts (the model of Lemma C.6).  The nested finite sum
over labels and `tsum` over multigraphs replace all conditional expectations.  With uniform labels
(`p = fun _ _ => (q : ℝ)⁻¹` on `Fin q`) this is `E_σ E_{𝖯^σ_s}`, and on `Fin q × Fin q` it is the
law `𝖰` of Lemma C.5(ii). -/
def cpExp {n : ℕ} {S : Type*} [Fintype S] (p : Fin n → S → ℝ) (K : S → S → ℝ)
    (F : (Fin n → S) → RSGraph n → ℝ) : ℝ :=
  ∑ ξ : Fin n → S, (∏ v, p v (ξ v)) * poisPiExp (cpMean K ξ) (F ξ)

/-- **`eq:rs-model`.** The weight `w_{G,t}(σ) = ∏_{(u,v) ∈ [n]²} M_t(σ_u, σ_v)^{N_{uv}}` (the
paper's `w_{G,z}` is `rsW q (tOf q z)`). -/
def rsW {R : Type*} [CommRing R] (q : ℕ) {n : ℕ} (t : R) (N : RSGraph n)
    (σ : Fin n → Fin q) : R :=
  ∏ uv : Fin n × Fin n, rsM q t (σ uv.1) (σ uv.2) ^ N uv

/-- **`eq:rs-model`.** The partition function `F_G = q^{-n} ∑_{σ ∈ [q]^n} w_{G,t}(σ)` (the paper's
`F_G(z)` is `rsF q (tOf q z) N`; at a real anchor `x`, `F = F_G(x)` is `rsF q (tRe q x) N`).
For a simple `G` with underlying graph `Ḡ`, `rsF q t N = (zhat Ḡ q).eval t`. -/
def rsF {R : Type*} [Field R] (q : ℕ) {n : ℕ} (t : R) (N : RSGraph n) : R :=
  ((q : R) ^ n)⁻¹ * ∑ σ : Fin n → Fin q, rsW q t N σ

/-- `κ_s(σ) = (s/(2n))·t·∑_{u,v} A_{σ_u σ_v}`, which equals `½ s n t q ‖α(σ) - u‖²` (before
`eq:rs-first-moment`); it is `≤ 0` for `t ≤ 0`. -/
def rsKappa (q n : ℕ) (s t : ℝ) (σ : Fin n → Fin q) : ℝ :=
  s / (2 * n) * (t * ∑ u, ∑ v, (rsA q (σ u) (σ v) : ℝ))

end Multigraph

/-! ## The `m`-edge model and the planted free-energy bound [CKPZ, Prop. 3.6] -/

section CKPZ

/-- The ordered multigraph with edge list `e : Fin m → [n]²`: `N_c = #{j : e_j = c}`. -/
def rsEdgeCount {n m : ℕ} (e : Fin m → Fin n × Fin n) : RSGraph n :=
  fun c => (Finset.univ.filter fun j => e j = c).card

/-- `F` of the multigraph with edge list `e`, i.e. `q^{-n} Z(G)` for the factor graph of CKPZ
(Section 2 there) with spins `[q]`, arity `2`, constraint neighbourhoods `∂a_j = e_j` and the single
weight function `M_t`. -/
def rsSeqF (q : ℕ) {n m : ℕ} (t : ℝ) (e : Fin m → Fin n × Fin n) : ℝ :=
  ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q, ∏ j, rsM q t (σ (e j).1) (σ (e j).2)

/-- The planted free energy of the `m`-edge model at the real point `x` (proof of Lemma C.3):
`c̄_m = E[F log F | m] / E[F | m]`, where given `m` the `m` edges are i.i.d. uniform ordered pairs
of `[n]²` (CKPZ's null model `G(n,m,p)`, Definition 2.5) and `F = rsSeqF q (tRe q x) e`; the
normalizations `n^{-2m}` of the two averages cancel.  Since `ln Z = n ln q + ln F`, CKPZ's
`E[ln Z(Ĝ(n,m,p))] = n ln q + c̄_m`, where `Ĝ` reweights by `Z` separately for each `m`
(CKPZ (3.4)). -/
def rsCbar (q n m : ℕ) (x : ℝ) : ℝ :=
  (∑ e : Fin m → Fin n × Fin n, rsSeqF q (tRe q x) e * Real.log (rsSeqF q (tRe q x) e)) /
    ∑ e : Fin m → Fin n × Fin n, rsSeqF q (tRe q x) e

/-- **The planted free-energy bound [CKPZ, Proposition 3.6] for the Potts antiferromagnet
`M_x`.**

Faithful specialization of Coja-Oghlan–Krzakala–Perkins–Zdeborová, Prop. 3.6
(`liminf_n -n⁻¹ E ln Z(Ĝ) ≥ -sup_{π ∈ 𝒫²_*(Ω)} B(d,π)` under SYM and BAL), to spins `Ω = [q]`,
arity `k = 2` and the single weight function `ψ = M_x`, `x ∈ (0,1)` (entries in
`(0, 3/2] ⊂ (0,2)`, `ξ = 1`; SYM: all row/column sums equal `q`; BAL: `μ ↦ μᵀ M_x μ` is concave
and maximal at `u`).  With `m ∼ Pois(sn/2)` constraints on i.i.d. uniform ordered pairs,
`E ln Z(Ĝ) = n ln q + ∑_m P(m) c̄_m` and `B(s,π) = ln q + Ψ_{s,x}(π)` on `𝒫_u` (see the proof of
Lemma C.3 in the paper), so, after these two exact identifications (made in the paper; the Lean
proof does not need them, since `ckpz_prop36` proves this statement directly), Prop. 3.6 reads
`limsup_n n⁻¹ ∑_m P(m) c̄_m ≤ sup_{ν ∈ 𝒫_u} Ψ_{s,x}(ν)`.  It is written without `limsup` and
`sup`: for every `x ∈ (0,1)`, `s > 0`, every upper bound `η` of `Ψ_{s,x}` on `𝒫_u` and every
`ε > 0`, eventually `∑_m Pois(sn/2)(m) · c̄_m ≤ (η + ε) n`.

The `RS*` modules prove Appendix C from this hypothesis and use it only through
`rs_free_energy` (`eq:rs-input`); the `CK*` modules prove it for every `q ≥ 2` (`ckpz_prop36`),
and `AppendixC` discharges it.  It is meaningful for `q ≥ 2` (for `q = 0` the simplex is empty
and the statement is false); every result taking it as a hypothesis assumes `3 ≤ q`. -/
def CKPZProp36 (q : ℕ) : Prop :=
  ∀ x : ℝ, 0 < x → x < 1 → ∀ s : ℝ, 0 < s → ∀ η : ℝ, (∀ ν ∈ rsPu q, bethePsi q s x ν ≤ η) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∑' m : ℕ, poisPMF (s * n / 2) m * rsCbar q n m x ≤ (η + ε) * n

end CKPZ

/-! ## Pairs of colourings: overlaps, the window, local pair sums (`app:rs-poisson`, `app:rs-local`)
-/

section Pairs

/-- `‖R_{σ,τ} - R̄‖_F²`, with the overlap matrix `R_{σ,τ}` of `eq:overlap-def` and `R̄ = u uᵀ`. -/
def rsOvDev {n q : ℕ} (σ τ : Fin n → Fin q) : ℝ :=
  ∑ a, ∑ b, (overlap σ τ a b - 1 / (q : ℝ) ^ 2) ^ 2

/-- The window `{(σ,τ) : ‖R_{σ,τ} - R̄‖_F < η}` (for `η > 0`), written with squares. -/
def rsWindow (q n : ℕ) (η : ℝ) : Finset ((Fin n → Fin q) × (Fin n → Fin q)) :=
  Finset.univ.filter fun x => rsOvDev x.1 x.2 < η ^ 2

/-- **The local pair sum** `H_G(t) = q^{-2n} ∑_{‖R_{σ,τ} - R̄‖_F < η} w_{G,t}(σ) conj(w_{G,t}(τ))`
(`app:rs-local`; the paper's `H_G(z)` is `rsH q η (tOf q z) N`).  It is real (exchanging `σ` and `τ`
conjugates the summand), and is stored as the sum of the real parts. -/
def rsH {n : ℕ} (q : ℕ) (η : ℝ) (t : ℂ) (N : RSGraph n) : ℝ :=
  (((q : ℝ) ^ n)⁻¹) ^ 2 *
    ∑ x ∈ rsWindow q n η, (rsW q t N x.1 * starRingEnd ℂ (rsW q t N x.2)).re

/-- `H = H_G(x) ∈ [0, F²]` at a real anchor, with `t = tRe q x` (`rs_rsH_ofReal` links it to
`rsH`). -/
def rsHR {n : ℕ} (q : ℕ) (η t : ℝ) (N : RSGraph n) : ℝ :=
  (((q : ℝ) ^ n)⁻¹) ^ 2 * ∑ x ∈ rsWindow q n η, rsW q t N x.1 * rsW q t N x.2

/-- `Y = (F² - H)/F = F · Pr_{μ_G^{⊗2}}[‖R_{σ,τ} - R̄‖_F ≥ η] ∈ [0, F]`, the `F`-weighted mass of
the pairs outside the window (`app:rs-local`). -/
def rsY {n : ℕ} (q : ℕ) (η t : ℝ) (N : RSGraph n) : ℝ :=
  (rsF q t N ^ 2 - rsHR q η t N) / rsF q t N

/-- The pair kernel `s·M_t(a,a')·M_t(b,b')` on labels `(a,b), (a',b') ∈ [q]²`: the edge means of
`𝖯^{σ,τ}_s` are `cpMean (rsPairK q s t) (fun v => (σ v, τ v))`. -/
def rsPairK (q : ℕ) (s t : ℝ) (a b : Fin q × Fin q) : ℝ := s * rsM q t a.1 b.1 * rsM q t a.2 b.2

/-- `n φ^s_{t,t̄}(R_{σ,τ}) = (s/(2n)) ∑_{u,v} (M_t(σ_u,σ_v) conj(M_t(τ_u,τ_v)) - 1)`
(`eq:rs-two-tilt` with `z' = z̄`). -/
def rsPairExpo (q n : ℕ) (s : ℝ) (t : ℂ) (σ τ : Fin n → Fin q) : ℂ :=
  ((s / (2 * n) : ℝ) : ℂ) *
    ∑ u, ∑ v, (rsM q t (σ u) (σ v) * starRingEnd ℂ (rsM q t (τ u) (τ v)) - 1)

/-- `n φ^s_{x,x}(R_{σ,τ}) = (s/(2n)) ∑_{u,v} (M_t(σ_u,σ_v) M_t(τ_u,τ_v) - 1)` at a real `t`
(`eq:rs-pair-tilt`). -/
def rsPairExpoR (q n : ℕ) (s t : ℝ) (σ τ : Fin n → Fin q) : ℝ :=
  s / (2 * n) * ∑ u, ∑ v, (rsM q t (σ u) (σ v) * rsM q t (τ u) (τ v) - 1)

/-- `Pr_𝖰[G ∈ E]` for the law `𝖰` of Lemma C.5(ii): `σ, τ` independent and uniform, and given them
`G ∼ 𝖯^{σ,τ}_d` (labels `ξ_v = (σ_v, τ_v)` uniform on `[q]²`). -/
def rsQProb (q n : ℕ) (d t : ℝ) (E : Set (RSGraph n)) : ℝ :=
  cpExp (fun (_ : Fin n) (_ : Fin q × Fin q) => ((q : ℝ) ^ 2)⁻¹) (rsPairK q d t)
    (fun _ N => E.indicator (fun _ => (1 : ℝ)) N)

/-- `θ_* = d t_*² (1 + q² η)` (`eq:rs-parameters`). -/
def rsTheta (q : ℕ) (d tstar η : ℝ) : ℝ := d * tstar ^ 2 * (1 + (q : ℝ) ^ 2 * η)

end Pairs

/-! ## Objects of the proof of Lemma C.7 (`app:rs-bad`) -/

section Anchor

/-- `ℓ = log(e/x) = 1 - log x` (`x > 0`): adding one edge changes `log F_G(x)` by at most `ℓ`. -/
def rsEll (x : ℝ) : ℝ := Real.log (Real.exp 1 / x)

/-- `‖α(σ) - u‖²`, `α(σ)` the colour-proportion vector. -/
def rsDevSq {n q : ℕ} (σ : Fin n → Fin q) : ℝ := ∑ a, (colorFrac σ a - 1 / (q : ℝ)) ^ 2

/-- `‖R_{σ,τ} - α βᵀ‖_F²` with `α = α(σ)`, `β = α(τ)` (proof of Lemma C.7, Step 2). -/
def rsCorrDev {n q : ℕ} (σ τ : Fin n → Fin q) : ℝ :=
  ∑ a, ∑ b, (overlap σ τ a b - colorFrac σ a * colorFrac τ b) ^ 2

/-- `⟨e_a - β, e_b - β⟩` with `β = α(τ)`. -/
def rsTestCoef {n q : ℕ} (τ : Fin n → Fin q) (a b : Fin q) : ℝ :=
  ∑ c, ((if a = c then (1 : ℝ) else 0) - colorFrac τ c) *
    ((if b = c then (1 : ℝ) else 0) - colorFrac τ c)

/-- The test statistic `S_τ(G') = t q ∑_{(u,v)} N'_{uv} ⟨e_{τ_u} - β, e_{τ_v} - β⟩` of Lemma C.7,
Step 2. -/
def rsTestStat {n : ℕ} (q : ℕ) (t : ℝ) (τ : Fin n → Fin q) (N : RSGraph n) : ℝ :=
  t * q * ∑ uv : Fin n × Fin n, (N uv : ℝ) * rsTestCoef τ (τ uv.1) (τ uv.2)

/-- `f̄_n = E_σ E_{𝖯^σ_s} log F` (Lemma C.7, Step 1), `σ` uniform. -/
def rsFbar (q n : ℕ) (s t : ℝ) : ℝ :=
  cpExp (fun (_ : Fin n) (_ : Fin q) => (q : ℝ)⁻¹) (fun a b => s * rsM q t a b)
    (fun _ N => Real.log (rsF q t N))

end Anchor

end

end ERZeroFreeness
