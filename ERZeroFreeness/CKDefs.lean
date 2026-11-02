/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSDefs

/-!
# Proof of [CKPZ, Prop. 3.6]: definitions

Appendix C is formalized in two layers.  The RS* modules prove Theorem C.1 from the explicit
hypothesis `CKPZProp36 q` (`RSDefs`), the Potts case of the planted free-energy bound of
Coja-Oghlan, Krzakala, Perkins and Zdeborová [CKPZ, Prop. 3.6].  The CK* modules prove that
hypothesis for every `q ≥ 2` from first principles (`ckpz_prop36` in `CKMain`), following the
self-contained proof in `docs/ckpz-proof.md`, which gives every lemma, constant and order of
limits.  Section numbers (§k) and the numbers of facts, lemmas, propositions and corollaries in
the CK* modules refer to that document.

This file collects the objects of that proof: the constants of §0.2, the notation of §0.3 and
Lemma 1.5, the Bethe functional at finitely supported laws (Fact 0.2), and the objects of §§3–7.

## Conventions

* **The parameter `t`.**  The CK* modules work with `t` and the hypothesis `CKPar q t`
  (`q ≥ 2`, `t < 0`, `-1 < t(q-1)`) instead of `x ∈ (0,1)`; `ckPar_tRe` gives
  `CKPar q (tRe q x)` for `x ∈ (0,1)`, which connects them with `CKPZProp36`, stated in terms
  of `x`.
* **Vertex sets** are `Fin n`; multigraphs are `RSGraph n` (edge counts on all `n²` ordered
  pairs, loops included).
* **Laws are mass functions.**  A probability measure on `[q]^V` is a function
  `μ : (Fin n → Fin q) → ℝ` with `IsPMF μ`; Poisson laws are `poisPMF` and `poisPi`, random
  vertex sets are weighted by `ckBern`, and expectations are finite sums and `tsum`s (`ckQExp` is
  `E_𝖰`).  Pin probabilities are scalars `π : ℝ`.
* **Entropy** is written in the cylinder form `h_μ(S) = -∑_τ μ(τ) log μ(τ'_S = τ_S)` (`ckH`),
  which equals the entropy of the marginal of `τ_S` and needs no subtype of `Fin n`.
* **`Λ` and `kl`.**  `Λ(y) = y log y` is `ckLam` (`Λ(0) = 0` since `Real.log 0 = 0`), and
  `kl(y) = Λ(y) - y + 1` is `InformationTheory.klFun`.
-/

open Filter Topology MeasureTheory

namespace ERZeroFreeness

open scoped Classical

noncomputable section


/-- The parameters: `q ≥ 2`, `t < 0` and `-1 < t(q-1)`, i.e. `t = t(x)` for some `x ∈ (0,1)`
(§0.1). -/
structure CKPar (q : ℕ) (t : ℝ) : Prop where
  two_le : 2 ≤ q
  neg : t < 0
  gt : -1 < t * ((q : ℝ) - 1)

/-- The diagonal entry `m₋ = M(a,a) = 1 + t(q-1)` (§0.2). -/
def ckMm (q : ℕ) (t : ℝ) : ℝ := 1 + t * ((q : ℝ) - 1)

/-- The off-diagonal entry `m₊ = M(a,b) = 1 - t`, `a ≠ b` (§0.2). -/
def ckMp (t : ℝ) : ℝ := 1 - t

/-- The logarithmic size `ℓ₀ = log(1/m₋)` (§0.2). -/
def ckEll (q : ℕ) (t : ℝ) : ℝ := -Real.log (ckMm q t)

/-- `Λ(y) = y log y`; `kl(y) = Λ(y) - y + 1` is `InformationTheory.klFun`. -/
def ckLam (y : ℝ) : ℝ := y * Real.log y

/-- A probability mass function on a finite type. -/
def IsPMF {α : Type*} [Fintype α] (μ : α → ℝ) : Prop := (∀ a, 0 ≤ μ a) ∧ ∑ a, μ a = 1

/-- The marginal `μ_v(a) = μ(τ_v = a)`. -/
def ckMarg {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) (v : Fin n) (a : Fin q) : ℝ :=
  ∑ τ with τ v = a, μ τ

/-- `dev(μ) = ⟨‖λ_τ - u‖₂⟩_μ`, `λ_τ` the colour-proportion vector of `τ`. -/
def ckDev {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) : ℝ := ∑ τ, μ τ * Real.sqrt (rsDevSq τ)

/-- `τ` agrees with `σ` on `S`: `τ_S = σ_S`. -/
def ckAgree {n q : ℕ} (S : Finset (Fin n)) (σ τ : Fin n → Fin q) : Prop := ∀ v ∈ S, τ v = σ v

/-- The cylinder probability `μ(τ'_S = τ_S)`. -/
def ckCyl {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) (S : Finset (Fin n)) (τ : Fin n → Fin q) : ℝ :=
  ∑ τ' with ckAgree S τ τ', μ τ'

/-- `h_μ(S) = H(τ_S)`, written as `-∑_τ μ(τ) log μ(τ'_S = τ_S)`. -/
def ckH {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) (S : Finset (Fin n)) : ℝ :=
  -∑ τ, μ τ * Real.log (ckCyl μ S τ)

/-- The conditional mutual information
`I(τ_A; τ_B | τ_S) = h(A ∪ S) + h(B ∪ S) - h(A ∪ B ∪ S) - h(S)` (Lemma 1.5). -/
def ckMI {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) (A B S : Finset (Fin n)) : ℝ :=
  ckH μ (A ∪ S) + ckH μ (B ∪ S) - ckH μ (A ∪ B ∪ S) - ckH μ S

/-- `μ(· | τ_S = ξ_S)` (zero if the conditioning event is null). -/
def ckCond {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) (S : Finset (Fin n)) (ξ : Fin n → Fin q)
    (τ : Fin n → Fin q) : ℝ :=
  if ckAgree S ξ τ then μ τ / ckCyl μ S ξ else 0

/-- `𝒥_μ(W | S) = ∑_{w ∈ W} I(τ_w; τ_{W∖w} | τ_S)` (§6). -/
def ckJ {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) (W S : Finset (Fin n)) : ℝ :=
  ∑ w ∈ W, ckMI μ {w} (W.erase w) S

/-- `B_π(U)`: weight of `U` under `Bern(π)^V`. -/
def ckBern {n : ℕ} (π : ℝ) (U : Finset (Fin n)) : ℝ := ∏ v, if v ∈ U then π else 1 - π

/-- `𝒥̄_p(μ) = E_{W ∼ Bern(p)} 𝒥_μ(W | ∅)` (Corollary 6.2). -/
def ckJbar {n q : ℕ} (p : ℝ) (μ : (Fin n → Fin q) → ℝ) : ℝ :=
  ∑ W : Finset (Fin n), ckBern p W * ckJ μ W ∅

/-- `ι₂(μ) = (n⁻² ∑_{v ≠ w} I(τ_v; τ_w))^{1/2}` (Lemma 5.4). -/
def ckIota2 {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) : ℝ :=
  Real.sqrt (((n : ℝ) ^ 2)⁻¹ * ∑ v, ∑ w ∈ Finset.univ.erase v, ckMI μ {v} {w} ∅)

/-- `ν = ∑_j w_j δ_{μ_j}` is a finitely supported law on the simplex. -/
def ckFinLaw (q : ℕ) {K : ℕ} (w : Fin K → ℝ) (μ : Fin K → Fin q → ℝ) : Prop :=
  (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ ∀ j, μ j ∈ stdSimplex ℝ (Fin q)

/-- `ν = ∑_j w_j δ_{μ_j}` is a finitely supported law on the simplex with mean `u`, i.e. a
finitely supported member of `𝒫_u`. -/
def ckFinPu (q : ℕ) {K : ℕ} (w : Fin K → ℝ) (μ : Fin K → Fin q → ℝ) : Prop :=
  ckFinLaw q w μ ∧ ∀ a, ∑ j, w j * μ j a = (q : ℝ)⁻¹

/-- `BV_r(ν)` at `ν = ∑_j w_j δ_{μ_j}` (Fact 0.2). -/
def ckBV (q : ℕ) (t r : ℝ) {K : ℕ} (w : Fin K → ℝ) (μ : Fin K → Fin q → ℝ) : ℝ :=
  ∑' d : ℕ, poisPMF r d *
    ∑ y : Fin d → Fin K, (∏ i, w (y i)) * ckLam (betheV q t fun i => μ (y i))

/-- `BE(ν)` at `ν = ∑_j w_j δ_{μ_j}` (Fact 0.2). -/
def ckBE (q : ℕ) (t : ℝ) {K : ℕ} (w : Fin K → ℝ) (μ : Fin K → Fin q → ℝ) : ℝ :=
  ∑ j, ∑ k, w j * w k * ckLam (betheE q t (μ j) (μ k))

/-- `Ψ_r(ν) = BV_r(ν) - (r/2) BE(ν)` at `ν = ∑_j w_j δ_{μ_j}` (Fact 0.2). -/
def ckPsi (q : ℕ) (t r : ℝ) {K : ℕ} (w : Fin K → ℝ) (μ : Fin K → Fin q → ℝ) : ℝ :=
  ckBV q t r w μ - r / 2 * ckBE q t w μ

/-- `n² φ(σ) = ∑_{(v,w)} M(σ_v, σ_w)` (Lemma 1.4(f)). -/
def ckZ1 (q : ℕ) (t : ℝ) {n : ℕ} (σ : Fin n → Fin q) : ℝ :=
  ∑ e : Fin n × Fin n, rsM q t (σ e.1) (σ e.2)

/-- `g(σ, m) = E_{e ∼ p_σ^{⊗m}} log F_e`, where `p_σ(v,w) = M(σ_v, σ_w)/(n² φ(σ))` is the
single-edge law (§3). -/
def ckg (q : ℕ) (t : ℝ) {n : ℕ} (σ : Fin n → Fin q) (m : ℕ) : ℝ :=
  (ckZ1 q t σ ^ m)⁻¹ * ∑ e : Fin m → Fin n × Fin n,
    (∏ j, rsM q t (σ (e j).1) (σ (e j).2)) * Real.log (rsSeqF q t e)

/-- `S(τ) = ∑_e (M_e(τ) - 1)` (Definition 4.1). -/
def ckS (q : ℕ) (t : ℝ) {n : ℕ} (τ : Fin n → Fin q) : ℝ :=
  ∑ e : Fin n × Fin n, (rsM q t (τ e.1) (τ e.2) - 1)

/-- The likelihood ratio `L_ϱ(G, τ) = e^{-ϱ S(τ)} w_G(τ) = d𝖯^τ_ϱ / d𝖯_ϱ` (Definition 4.1). -/
def ckL (q : ℕ) (t ϱ : ℝ) {n : ℕ} (G : RSGraph n) (τ : Fin n → Fin q) : ℝ :=
  Real.exp (-(ϱ * ckS q t τ)) * rsW q t G τ

/-- The edge means `ϱ M_e(σ)` of the planted law: `𝖯^σ_ϱ(G) = poisPi (ckPl q t ϱ σ) G`
(Definition 4.1). -/
def ckPl (q : ℕ) (t ϱ : ℝ) {n : ℕ} (σ : Fin n → Fin q) (e : Fin n × Fin n) : ℝ :=
  ϱ * rsM q t (σ e.1) (σ e.2)

/-- The pinned partition function `F̃_ϱ(G, U, ς) = q^{-n} ∑_{τ_U = ς_U} L_ϱ(G, τ)`
(Definition 4.1). -/
def ckFt (q : ℕ) (t ϱ : ℝ) {n : ℕ} (G : RSGraph n) (U : Finset (Fin n))
    (ς : Fin n → Fin q) : ℝ :=
  ((q : ℝ) ^ n)⁻¹ * ∑ τ with ckAgree U ς τ, ckL q t ϱ G τ

/-- The pinned posterior `post_{G,U,ς}(τ) ∝ 1[τ_U = ς_U] L_ϱ(G, τ)` (Definition 4.1). -/
def ckPost (q : ℕ) (t ϱ : ℝ) {n : ℕ} (G : RSGraph n) (U : Finset (Fin n)) (ς : Fin n → Fin q)
    (τ : Fin n → Fin q) : ℝ :=
  if ckAgree U ς τ then ckL q t ϱ G τ / ∑ τ' with ckAgree U ς τ', ckL q t ϱ G τ' else 0

/-- `E_𝖰 f(σ, G, U)` for the planted triple law `𝖰 = 𝖰_{[n],ϱ,π}`: `σ` is uniform, `G ∼ 𝖯^σ_ϱ`
given `σ`, and `U ∼ Bern(π)^{[n]}` independently (Definition 4.1). -/
def ckQExp (q : ℕ) (t ϱ π : ℝ) (n : ℕ)
    (f : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ) : ℝ :=
  ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q, ∑ U : Finset (Fin n),
    ckBern π U * ∑' G : RSGraph n, poisPi (ckPl q t ϱ σ) G * f σ G U

/-- Domination `|f(σ, G, U)| ≤ A c^{|G|}`; it makes the `G`-series in `ckQExp` summable when the
edge means are nonnegative (`rs_summable_poisPi_of_abs_le`). -/
def CKDom {n q : ℕ} (f : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ) : Prop :=
  ∃ A c : ℝ, 0 ≤ c ∧ ∀ σ G U, |f σ G U| ≤ A * c ^ rsEdges G

/-- The pinned planted free energy `𝒦_{[n]}(ϱ, π) = E_𝖰 log F̃_ϱ(G, U, σ)` (Definition 4.1). -/
def ckK (q : ℕ) (t ϱ π : ℝ) (n : ℕ) : ℝ :=
  ckQExp q t ϱ π n fun σ G U => Real.log (ckFt q t ϱ G U σ)

/-- `π_k(N) = 1 - e^{-ks/N}` (Definition 4.8). -/
def ckPin (s : ℝ) (k N : ℕ) : ℝ := 1 - Real.exp (-(k * s / N))

/-- `a_N(k) = 𝒦_{[N]}(s/(2N), π_k(N))` (Definition 4.8). -/
def ckA (q : ℕ) (t s : ℝ) (N k : ℕ) : ℝ := ckK q t (s / (2 * N)) (ckPin s k N) N

/-- `Ξ_δ(μ) = ∑_H 𝖯_δ(H) Λ(⟨L_δ(H, ·)⟩_μ)` (§5). -/
def ckXi (q : ℕ) (t δ : ℝ) {n : ℕ} (μ : (Fin n → Fin q) → ℝ) : ℝ :=
  ∑' H : RSGraph n, poisPi (fun _ => δ) H * ckLam (∑ τ, μ τ * ckL q t δ H τ)

/-- The edge term `∑_e kl(⟨M_e⟩_μ)` (Lemma 5.3). -/
def ckEdgeKL (q : ℕ) (t : ℝ) {n : ℕ} (μ : (Fin n → Fin q) → ℝ) : ℝ :=
  ∑ e : Fin n × Fin n, InformationTheory.klFun (∑ τ, μ τ * rsM q t (τ e.1) (τ e.2))

/-- The cavity quantity `X_μ(D, N₀) = κ(N₀) q⁻¹ ∑_c ⟨e^{δ_c(τ)} ∏_v M(τ_v, c)^{D_v}⟩_μ` at rate
`ϱ` per ordered pair, with `κ(N₀) = e^{ϱ(1 - m₋)} m₋^{N₀}` and
`δ_c(τ) = -2ϱ ∑_v (M(τ_v, c) - 1)` (§7). -/
def ckX (q : ℕ) (t ϱ : ℝ) {n : ℕ} (μ : (Fin n → Fin q) → ℝ) (D : Fin n → ℕ) (N0 : ℕ) : ℝ :=
  Real.exp (ϱ * (1 - ckMm q t)) * ckMm q t ^ N0 *
    ((q : ℝ)⁻¹ * ∑ c : Fin q, ∑ τ, μ τ *
      (Real.exp (-(2 * ϱ) * ∑ v, (rsM q t (τ v) c - 1)) * ∏ v, rsM q t (τ v) c ^ D v))

/-- The vertex term `Vert(μ) = E⁰ Λ(X_μ(D,N₀))`, `D_v ∼ Pois(2ϱ)` i.i.d., `N₀ ∼ Pois(ϱ)`
(§7). -/
def ckVert (q : ℕ) (t ϱ : ℝ) {n : ℕ} (μ : (Fin n → Fin q) → ℝ) : ℝ :=
  ∑' z : (Fin n → ℕ) × ℕ,
    poisPi (fun _ => 2 * ϱ) z.1 * poisPMF ϱ z.2 * ckLam (ckX q t ϱ μ z.1 z.2)

end

end ERZeroFreeness
