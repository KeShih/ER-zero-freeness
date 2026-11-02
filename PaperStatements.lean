/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib
import EndStatement

/-!
# Further statements of the paper

Statements of *Zero-Freeness and Deterministic Counting on Erdős–Rényi Random Graphs* (Ke Shi)
beyond the claims of `EndStatement.lean`, each as a proposition, with the definitions that they use.
This file imports Mathlib and `EndStatement.lean` alone and contains no proofs.  It uses the
definitions of `EndStatement.lean` (`pottsZ`, `erProb`, `d2`, `signedPoly`, `vbZ`, `ellCoeff`,
`vbApprox`, `ConnSetBound`, `sgProb`, `boolSign`, `rsM`, `tRe`, `rsPu`, `poisPMF`, `bethePsi`,
`dCond`, …) and defines only the further objects that the statements need.
`Challenge/PaperStatements.lean` asserts the propositions with `sorry`, and
`Solution/PaperStatements.lean` proves them from the library; the claims of `EndStatement.lean` do
not depend on this file.

| Statement | Paper |
|---|---|
| `Eq_1_4` | (1.4): the Ising antiferromagnet through `𝓘_{G,1}` |
| `Eq_1_5` | (1.5): the Viana–Bray partition function through `𝓘_{G,J}` |
| `Eq_2_2` | (2.2): `Z_G(q,z) = q^{|V|} b(z)^{|E|} Ẑ_G(t(z))` |
| `Proposition_6_1_tplane` | Proposition 6.1, the `t`-plane conclusion (6.2) |
| `Proposition_6_1` | Proposition 6.1, the `z`-plane conclusion |
| `Proposition_6_1_return_to_z` | Proposition 6.1, proof: from the `t`-plane to the `z`-plane |
| `Eq_5_11` | (5.11): the uniform first-moment bound for `d < d₂(q)` |
| `Lemma_8_2` | Lemma 8.2: connected-set counts |
| `Section_8_interpolation` | Section 8: the interpolation estimate before Proposition 8.4 |
| `Proposition_8_4_ii` | Proposition 8.4 (ii), at the level of coefficients |
| `Appendix_A_d2_asymptotic` | Appendix A: `d₂(q) ∼ 2q log q` |
| `Appendix_A_d2_strictMono` | Appendix A: `d₂` is strictly increasing on `[3,∞)` |
| `Appendix_A_dnc_strictMono` | Appendix A: `d_nc` is increasing |
| `Appendix_A_dnc_lt_d2_succ` | Appendix A: `d₂(q+1) > 2q log q > d_nc(q)` |
| `Appendix_A_disjoint` | Appendix A: the intervals `[d₂(q), d_nc(q))` are pairwise disjoint |
| `Corollary_1_4_noncolorable` | Appendix A: no proper `q`-coloring for `d ≥ d_nc(q)` |
| `Appendix_B_tplane` | Appendix B: zero-freeness of `Ẑ_{G_n}` on a tube around `t([x₀,1])` |
| `Proposition_C_2` | Proposition C.2: complex first moment below condensation |
| `Proposition_C_2_tube` | Proposition C.2, `t`-plane form |
| `Lemma_C_3_monotone` | Lemma C.3: `x ↦ d_cond(q,x)` is nondecreasing |
| `Lemma_C_3_ks_bound` | Lemma C.3: `d_cond(q,x) ≤ t(x)^{-2}` |
| `Lemma_C_3_free_energy` | Lemma C.3: (C.5), the planted free energy (with its series convergent) |
| `CKPZ_Proposition_3_6` | [CKPZ, Proposition 3.6] for the Potts antiferromagnet |

**How the statements are to be read.**
* As in `EndStatement.lean`, `G(n,p)` is the explicit finite law `erWeight`; `erProb` and `erExp`
  are probabilities and expectations under it, and "with probability tending to one" is a limit
  `Tendsto … atTop (𝓝 1)` along `n` with `p = d/n`.  A bound "`sup_n …`" ranges over `n ≥ d`.
* The constants that the paper fixes before `n` (`ρ`, `r`, `B`, `C`, `W`, …) are chosen before `n`.
* A graph on an arbitrary finite vertex set is a `SimpleGraph V` with `V : Type` and `Fintype V`
  (`Eq_1_4`, `Eq_1_5`, `Eq_2_2`); Lemma 8.1, on induced subgraphs, is `EndStatement.Lemma_8_1`.
* `ℓ_j` is `EndStatement.ellCoeff`, the `j`-th coefficient of Mathlib's formal logarithm
  `PowerSeries.logOf`; it enters this file through `vbApprox` (`Proposition_8_4_ii`) and the
  interpolation estimate.  The library computes it by the recursion of the proof of Lemma 8.3 and
  proves that the two agree.  Every definition below other than the statements (`zhat`, `bFac`,
  `tOf`, `tube`, `erExp`, `poisPi`, `poisPiExp`, `RSGraph`, `rsMean`, `rsExp`, `rsW`, `rsF`,
  `rsSeqF`, `rsCbar`, `CKPZProp36`) is a verbatim copy of the library's definition of the same
  name.
* Expectations over Poisson laws are real `tsum`s, which Lean sets to `0` on non-summable families.
  `Lemma_C_3_free_energy` states that its series converges.  The series in `CKPZProp36` converge as
  well (for `x ∈ (0,1)` the entries of `M_x` lie in `[x, 2]`, so `x^m ≤ F ≤ 2^m` on a multigraph
  with `m` edges), but this is argued here, not stated.
* Lemmas 4.1 (`lem:cycle-counts`) and 4.2 (`lem:jets`) are proved in the library
  (`cycleCounts_tendsto_poisson`, `zhat_coeff_eq_cyclePoly_whp`) but not stated here: the library
  counts cycles through a quotient type of cyclic sequences, which would have to be copied.
-/

open Filter Topology Polynomial

namespace PaperStatements

open EndStatement

open scoped Classical

noncomputable section

/-! ## Section 2: definitions -/

section Potts

variable {V : Type*} [Fintype V]

/-- **(2.1) `eq:normalized-colors`.** The normalized partition polynomial
`Ẑ_G(t) = E_σ ∏_{uv ∈ E(G)} (1 + t A_{σ_u σ_v})`, with `σ` uniform on `[q]^V` and
`A = q·Id - J` (`edgeA`). -/
def zhat (G : SimpleGraph V) (q : ℕ) : ℂ[X] :=
  C (((q : ℂ) ^ Fintype.card V)⁻¹) *
    ∑ σ : V → Fin q, ∏ e ∈ G.edgeFinset, (1 + C (edgeA q σ e) * X)

/-- The average edge weight `b(z) = (z + q - 1)/q`. -/
def bFac (q : ℕ) (z : ℂ) : ℂ := (z + q - 1) / q

/-- The transformed parameter `t(z) = (z - 1)/(z + q - 1)`; at real points it is `tRe`. -/
def tOf (q : ℕ) (z : ℂ) : ℂ := (z - 1) / (z + q - 1)

end Potts

/-- The closed `r`-neighborhood `L_r(I_s)` of `I_s = [-s, 0]` in `ℂ`. -/
def tube (s r : ℝ) : Set ℂ :=
  {t | ∃ x : ℝ, x ∈ Set.Icc (-s) 0 ∧ ‖t - x‖ ≤ r}

/-- `E_{G ∼ G(n,p)}[f(G)]`. -/
def erExp (n : ℕ) (p : ℝ) (f : SimpleGraph (Fin n) → ℝ) : ℝ :=
  ∑ G : SimpleGraph (Fin n), erWeight n p G * f G

/-! ## Sections 1 and 2: statements -/

/-- **(1.4) `eq:ising-af-relation`.** "Setting `J_e = 1` for every edge recovers the zero-field
Ising antiferromagnet (`q = 2` in (1.1)) through the forest relation
`Z_G(2,z) = 2^n ((1+z)/2)^{|E(G)|} 𝓘_{G,1}((z-1)/(z+1))`."  For every graph `G` on a finite type
and every `z ≠ -1`, where the right side is defined; `𝓘_{G,1}` is
`signedPoly G 2 (fun _ => 1)`. -/
def Eq_1_4 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (z : ℂ), z + 1 ≠ 0 →
    pottsZ G 2 z = 2 ^ Fintype.card V * ((1 + z) / 2) ^ G.edgeFinset.card *
      (signedPoly G 2 (fun _ => 1)).eval ((z - 1) / (z + 1))

/-- **(1.5) `eq:viana-bray`.** "its partition function satisfies
`Z^VB_{G,J}(β) = ∑_{σ ∈ {-1,1}^{V(G)}} exp(β ∑_{uv ∈ E(G)} J_{uv} σ_u σ_v)`
`= 2^n (cosh β)^{|E(G)|} 𝓘_{G,J}(tanh β)` for all `β ∈ ℂ` with `cosh β ≠ 0`."  For every graph `G`
on a finite type and integer signs `J` that are `±1` on the edges of `G` (values off `E(G)` do not
matter). -/
def Eq_1_5 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (J : Sym2 V → ℤ),
    (∀ e ∈ G.edgeFinset, J e = 1 ∨ J e = -1) → ∀ β : ℂ, Complex.cosh β ≠ 0 →
      vbZ G J β = 2 ^ Fintype.card V * Complex.cosh β ^ G.edgeFinset.card *
        (signedPoly G 2 J).eval (Complex.tanh β)

/-- **(2.2) `eq:transformation`.** "`Ẑ_G(t(z)) = Z_G(q,z) / (q^{|V|} b(z)^{|E|})`", where
`b(z) = (z+q-1)/q` and `t(z) = (z-1)/(z+q-1)` (Section 2.1 fixes `q ≥ 2`).  Multiplied out:
`Z_G(q,z) = q^{|V|} b(z)^{|E|} Ẑ_G(t(z))` for every graph `G` on a finite type, every integer
`q ≥ 1` and every `z ≠ -(q-1)`. -/
def Eq_2_2 : Prop :=
  ∀ (V : Type) [Fintype V] (q : ℕ), 1 ≤ q → ∀ (G : SimpleGraph V) (z : ℂ), z + q - 1 ≠ 0 →
    pottsZ G q z =
      (q : ℂ) ^ Fintype.card V * bFac q z ^ G.edgeFinset.card * (zhat G q).eval (tOf q z)

/-! ## Section 6: statements -/

/-- **Proposition 6.1 (`prop:zero-free-moment`), the `t`-plane conclusion (6.2).** "Fix an
integer `q ≥ 2` and `d > 0`. Let `0 < s < 1` satisfy `(q-1)s ≤ 1` and `ds² < 1`, and put
`I_s = [-s,0]` … Suppose that, for some `r > 0`, `sup_n sup_{t ∈ L_r(I_s)} E|Ẑ_{G_n}(t)| < ∞`
(6.1). Then there exists `ρ' ∈ (0,r/4]` such that …
`Pr[Ẑ_{G_n}(t) ≠ 0 for every t ∈ L_{ρ'}(I_s)] → 1` (6.2)."  Here (6.1) is a bound `B` for all
`n ≥ d` and `t ∈ L_r(I_s)` (`tube s r`), the conclusion gives some `ρ > 0` (any smaller one also
works, so `ρ ≤ r/4` costs nothing), and the convergence in distribution of `Ẑ_{G_n}` to `𝒲`, also
asserted there, is not stated. -/
def Proposition_6_1_tplane : Prop :=
  ∀ q : ℕ, 2 ≤ q → ∀ d : ℝ, 0 < d → ∀ s : ℝ, 0 < s → s < 1 → ((q : ℝ) - 1) * s ≤ 1 →
    d * s ^ 2 < 1 → ∀ r B : ℝ, 0 < r →
    (∀ n : ℕ, d ≤ n → ∀ t ∈ tube s r, erExp n (d / n) (fun G => ‖(zhat G q).eval t‖) ≤ B) →
    ∃ ρ > 0, Tendsto (fun n : ℕ => erProb n (d / n)
      {G | ∀ t ∈ tube s ρ, (zhat G q).eval t ≠ 0}) atTop (𝓝 1)

/-- **Proposition 6.1 (`prop:zero-free-moment`), the `z`-plane conclusion.** "Moreover, there
exists `ρ_z > 0` such that `Pr[Z_{G_n}(q,z) ≠ 0 whenever dist(z,[x_s,1]) ≤ ρ_z] → 1`", where
`x_s = (1-(q-1)s)/(1+s)`.  Under the hypotheses of `Proposition_6_1_tplane`, written the same
way. -/
def Proposition_6_1 : Prop :=
  ∀ q : ℕ, 2 ≤ q → ∀ d : ℝ, 0 < d → ∀ s : ℝ, 0 < s → s < 1 → ((q : ℝ) - 1) * s ≤ 1 →
    d * s ^ 2 < 1 → ∀ r B : ℝ, 0 < r →
    (∀ n : ℕ, d ≤ n → ∀ t ∈ tube s r, erExp n (d / n) (fun G => ‖(zhat G q).eval t‖) ≤ B) →
    ∃ ρz > 0, Tendsto (fun n : ℕ => erProb n (d / n)
      {G | ∀ z : ℂ, (∃ x : ℝ, x ∈ Set.Icc ((1 - ((q : ℝ) - 1) * s) / (1 + s)) 1 ∧
        ‖z - x‖ ≤ ρz) → pottsZ G q z ≠ 0}) atTop (𝓝 1)

/-- **Proposition 6.1 (`prop:zero-free-moment`), the return to the `z`-plane** (last paragraph of
its proof). "By continuity of `b` and `t` near `[x_s,1]` and compactness, there exists `ρ_z > 0`
such that `b(z) ≠ 0` and `t(z) ∈ L_{ρ'}(I_s)` whenever `dist(z,[x_s,1]) ≤ ρ_z`. On the event in
(6.2), `Z_{G_n}(q,z) ≠ 0` for all such `z`."  Deterministic and uniform in the graph: for `q ≥ 2`,
`s ≥ 0` with `(q-1)s ≤ 1` and `ρ > 0` there is `ρ_z > 0` such that every graph `G` on `[n]` whose
`Ẑ_G` has no zero on `L_ρ(I_s)` has `Z_G(q,z) ≠ 0` whenever `dist(z,[x_s,1]) ≤ ρ_z`. -/
def Proposition_6_1_return_to_z : Prop :=
  ∀ q : ℕ, 2 ≤ q → ∀ s ρ : ℝ, 0 ≤ s → ((q : ℝ) - 1) * s ≤ 1 → 0 < ρ →
    ∃ ρz > 0, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), (∀ t ∈ tube s ρ, (zhat G q).eval t ≠ 0) →
      ∀ z : ℂ, (∃ x : ℝ, x ∈ Set.Icc ((1 - ((q : ℝ) - 1) * s) / (1 + s)) 1 ∧ ‖z - x‖ ≤ ρz) →
        pottsZ G q z ≠ 0

/-- **(5.11) `eq:potts-first-moment`.** "`sup_{n ≥ d} sup_{t ∈ L_{4ρ}} E|Ẑ_{G_n}(t)| < ∞`" for an
integer `q ≥ 3` and `0 < d < d₂(q)`, the hypothesis of Proposition 6.1 for the interval
`I = [-1/(q-1), 0]`: on some tube `L_r(I)`, `r > 0`, the first moment is bounded uniformly in
`n ≥ d`. -/
def Eq_5_11 : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ d : ℝ, 0 < d → d < d2 q →
    ∃ r > 0, ∃ B : ℝ, ∀ n : ℕ, d ≤ n → ∀ t ∈ tube (1 / ((q : ℝ) - 1)) r,
      erExp n (d / n) (fun G => ‖(zhat G q).eval t‖) ≤ B

/-! ## Section 8 (Lemma 8.1 is `EndStatement.Lemma_8_1`) -/

/-- **Lemma 8.2 (`lem:connected-sets`).** "For every fixed `B > 2e(d+1)`, with probability
`1 - O(n^{-1})` over `G_n ∼ G(n,d/n)`, simultaneously for all integers `s ≥ 1`,
`N_s(G_n) ≤ n² B^s` (8.5)."  The `O(n^{-1})` is a constant `C` such that (8.5) fails with
probability at most `C/n` for every `n ≥ d`. -/
def Lemma_8_2 : Prop :=
  ∀ d : ℝ, 0 < d → ∀ B : ℝ, 2 * Real.exp 1 * (d + 1) < B →
    ∃ C : ℝ, ∀ n : ℕ, d ≤ n → erProb n (d / n) {G | ¬ ConnSetBound B G} ≤ C / n

/-- **The interpolation estimate of Section 8 (`sec:interpolation`)**, in the paragraph before
Proposition 8.4. "If a polynomial `p` with `p(0) ≠ 0` has no zeros in the open disk of radius `M`
about `0` and `|t_1| < M`, then the exponential of the degree-`k` Taylor polynomial of `log p` at
`0`, evaluated at `t_1`, is a multiplicative `ε`-approximation to `p(t_1)` in the sense of
[PR, Definition 1.1] once `k ≥ max{1, log(deg(p)/ε)}/(1-|t_1|/M)`."  Normalized to `p(0) = 1`,
with the Taylor coefficients of `log p` those of the formal logarithm `PowerSeries.logOf p`, and
with the approximation written as `p(t_1) = exp(∑_{j=1}^{k} ℓ_j t_1^j + E)` with `|E| ≤ ε`, which
implies the multiplicative `ε`-approximation of [PR, Definition 1.1] (modulus ratio in
`[e^{-ε}, e^ε]`, angle at most `ε`). -/
def Section_8_interpolation : Prop :=
  ∀ p : ℂ[X], p.eval 0 = 1 → ∀ M : ℝ, (∀ z : ℂ, ‖z‖ < M → p.eval z ≠ 0) →
    ∀ t : ℂ, ‖t‖ < M → ∀ ε : ℝ, 0 < ε → ∀ k : ℕ,
      max 1 (Real.log (p.natDegree / ε)) / (1 - ‖t‖ / M) ≤ k →
      ∃ E : ℂ, p.eval t = Complex.exp (∑ j ∈ Finset.Icc 1 k,
          PowerSeries.coeff j (PowerSeries.logOf (p : PowerSeries ℂ)) * t ^ j + E) ∧
        ‖E‖ ≤ ε

/-- **Proposition 8.4 (ii) (`prop:counting`), at the level of coefficients.** "Let `q = 2`, let
`J` assign independent uniform signs to the edges of `G_n`, let `β_* > 0`, and suppose that, for
some `r > tanh β_*`, with probability tending to one `𝓘_{G_n,J}` has no zeros in `{|t| ≤ r}`. Then
the conclusion of (i) holds for `Z^VB_{G_n,J}(β)` in place of `Z_{G_n}(q,x)`, simultaneously for
all `β ∈ [-β_*,β_*]` and `ε ∈ (0,1)`."  The algorithm and its running time are not formalized;
stated is what it rests on: for every `B > 2e(d+1)` there is `C` such that, with probability
tending to one, (8.5) holds and, for all `β ∈ [-β_*,β_*]`, `ε ∈ (0,1)` and `k ≥ C log(n/ε)`,
`Z̃_k(β) = 2^n cosh(β)^{|E|} exp(∑_{j ≤ k} ℓ_j tanh(β)^j)` is real and within a factor `1 ± ε` of
`Z^VB_{G_n,J}(β)`.  Here `C` is the constant of the truncation order `k = O(log(n/ε))`, not the
running-time exponent `C(d,β_*,r)` of the paper. -/
def Proposition_8_4_ii : Prop :=
  ∀ d : ℝ, 0 < d → ∀ βs r : ℝ, 0 < βs → Real.tanh βs < r →
    Tendsto (fun n : ℕ => sgProb n (d / n)
      {GJ | ∀ t : ℂ, ‖t‖ ≤ r → (signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))).eval t ≠ 0})
      atTop (𝓝 1) →
    ∀ B : ℝ, 2 * Real.exp 1 * (d + 1) < B →
    ∃ C : ℝ, Tendsto (fun n : ℕ => sgProb n (d / n)
      {GJ | ConnSetBound B GJ.1 ∧
        ∀ β ∈ Set.Icc (-βs) βs, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ k : ℕ,
          C * Real.log (n / ε) ≤ k →
            ∃ x y : ℝ, vbApprox GJ.1 (fun e => boolSign (GJ.2 e)) k β = x ∧
              vbZ GJ.1 (fun e => boolSign (GJ.2 e)) β = y ∧
              (1 - ε) * y ≤ x ∧ x ≤ (1 + ε) * y}) atTop (𝓝 1)

/-! ## Appendices A and B: statements -/

/-- **Appendix A (`app:colorability`), proof of Corollary 1.3 (`cor:range`).** "Since
`d_2(q) ∼ 2q log q` as `q → ∞`, …"  As a limit along the integers: `d_2(q) / (2q log q) → 1`.
The proof applies this at the non-integer point `q_0 = (1/2+η) d/log d`; that real-variable step
is not stated here (the library proves Corollary 1.3 through `eventually_lt_two_mul_log` and
`two_mul_log_lt_d2`). -/
def Appendix_A_d2_asymptotic : Prop :=
  Tendsto (fun q : ℕ => d2 q / (2 * q * Real.log q)) atTop (𝓝 1)

/-- **Appendix A (`app:colorability`), proof of Corollary 1.3 (`cor:range`).** "Direct
differentiation shows that `d_2` is strictly increasing on `[3,∞)`."  Stated for the real
variable `x`; `d2 q` is this function at `x = q` (by definition). -/
def Appendix_A_d2_strictMono : Prop :=
  StrictMonoOn (fun x : ℝ => 2 * (x - 1) ^ 3 * Real.log (x - 1) / (x * (x - 2))) (Set.Ici 3)

/-- **Appendix A (`app:colorability`), proof of Corollary 1.4 (`cor:all-but-one`).** "Because
`d_nc(q)` is increasing in `q` …", where `d_nc(q) = (2q-1) log q`.  Strictly increasing on the
integers `q ≥ 1`. -/
def Appendix_A_dnc_strictMono : Prop :=
  StrictMonoOn (fun q : ℕ => (2 * (q : ℝ) - 1) * Real.log q) (Set.Ici 1)

/-- **Appendix A (`app:colorability`), proof of Corollary 1.4 (`cor:all-but-one`).**
"`d_2(q+1) = 2q³ log q/(q²-1) > 2q log q > d_nc(q)`."  The two inequalities, for every integer
`q ≥ 2`. -/
def Appendix_A_dnc_lt_d2_succ : Prop :=
  ∀ q : ℕ, 2 ≤ q → (2 * (q : ℝ) - 1) * Real.log q < 2 * q * Real.log q ∧
    2 * (q : ℝ) * Real.log q < d2 (q + 1)

/-- **Appendix A (`app:colorability`), proof of Corollary 1.4 (`cor:all-but-one`).** "the
intervals `[d_2(q), d_nc(q))` for `q ≥ 3` are pairwise disjoint. Hence at most one integer
`q_d ≥ 3` can fall into this uncovered range."  For every `d`, at most one integer `q ≥ 3` has
`d_2(q) ≤ d < d_nc(q)`. -/
def Appendix_A_disjoint : Prop :=
  ∀ d : ℝ, {q : ℕ | 3 ≤ q ∧ d2 q ≤ d ∧ d < (2 * (q : ℝ) - 1) * Real.log q}.Subsingleton

/-- **The non-colorability input of Corollary 1.4 (`cor:all-but-one`)**, in its proof in
Appendix A. "if `d ≥ d_nc(q)`, output `0`, which is exact on the high-probability event that `G_n`
is not `q`-colorable [AN, Theorems 1 and 2]", where `d_nc(q) = (2q-1) log q`.  For every integer
`q ≥ 2` and every `d ≥ d_nc(q)`, `Pr[Z_{G_n}(q,0) = 0] → 1`; `Z_G(q,0)` is the number of proper
`q`-colorings.  The paper uses this for `q ≥ 3` (and treats `q = 2` by an exact algorithm); the
cited result is proved here, not assumed. -/
def Corollary_1_4_noncolorable : Prop :=
  ∀ q : ℕ, 2 ≤ q → ∀ d : ℝ, (2 * (q : ℝ) - 1) * Real.log q ≤ d →
    Tendsto (fun n : ℕ => erProb n (d / n) {G | pottsZ G q 0 = 0}) atTop (𝓝 1)

/-- **Appendix B (`app:positive-temperature`), the `t`-plane statement.** "Proposition 6.1 with
`r = 4ρ` gives `ρ' ∈ (0,ρ]` such that, with probability tending to one, `Ẑ_{G_n}` has no zeros in
`L_{ρ'}(I_s)`", where `s = |t(x_0)| = (1-x_0)/(q-1+x_0)`, so that `I_s = t([x_0,1])`, for an
integer `q ≥ 3`, `x_0 ∈ (0,1)` and `0 < d < d_2(q) ((q-1+x_0)/((q-1)(1-x_0)))²` (1.2).  The
conclusion gives some `ρ > 0`. -/
def Appendix_B_tplane : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ x0 : ℝ, 0 < x0 → x0 < 1 → ∀ d : ℝ, 0 < d →
    d < d2 q * (((q : ℝ) - 1 + x0) / (((q : ℝ) - 1) * (1 - x0))) ^ 2 →
    ∃ ρ > 0, Tendsto (fun n : ℕ => erProb n (d / n)
      {G | ∀ t ∈ tube ((1 - x0) / ((q : ℝ) - 1 + x0)) ρ, (zhat G q).eval t ≠ 0}) atTop (𝓝 1)

/-! ## Appendix C: definitions -/

/-- The product Poisson mass function on `ι → ℕ`: independent `N_i ∼ Pois(lam_i)`. -/
def poisPi {ι : Type*} [Fintype ι] (lam : ι → ℝ) (N : ι → ℕ) : ℝ :=
  ∏ i, poisPMF (lam i) (N i)

/-- `E f(N)` for independent `N_i ∼ Pois(lam_i)`, as a real `tsum`. -/
def poisPiExp {ι : Type*} [Fintype ι] (lam : ι → ℝ) (f : (ι → ℕ) → ℝ) : ℝ :=
  ∑' N, poisPi lam N * f N

/-- An ordered multigraph on `[n]`: edge counts `N_{uv}` on all `n²` ordered pairs `(u,v)`, loops
included. -/
abbrev RSGraph (n : ℕ) : Type := Fin n × Fin n → ℕ

/-- The edge means `s/(2n)` of the ordered Poisson multigraph `𝖯_s`. -/
def rsMean (n : ℕ) (s : ℝ) : Fin n × Fin n → ℝ := fun _ => s / (2 * n)

/-- `E_{𝖯_s}[f(G)]`: independent `N_{uv} ∼ Pois(s/(2n))` on all ordered pairs, loops included. -/
def rsExp (n : ℕ) (s : ℝ) (f : RSGraph n → ℝ) : ℝ := poisPiExp (rsMean n s) f

/-- **(C.3) `eq:rs-model`.** The weight `w_{G,t}(σ) = ∏_{(u,v) ∈ [n]²} M_t(σ_u, σ_v)^{N_{uv}}` (the
paper's `w_{G,z}` is `rsW q (tOf q z)`; at a real anchor `x` it is `rsW q (tRe q x)`). -/
def rsW {R : Type*} [CommRing R] (q : ℕ) {n : ℕ} (t : R) (N : RSGraph n)
    (σ : Fin n → Fin q) : R :=
  ∏ uv : Fin n × Fin n, rsM q t (σ uv.1) (σ uv.2) ^ N uv

/-- **(C.3) `eq:rs-model`.** The partition function `F_G = q^{-n} ∑_{σ ∈ [q]^n} w_{G,t}(σ)`; the
paper's `F_G(x)` at a real point `x` is `rsF q (tRe q x)`. -/
def rsF {R : Type*} [Field R] (q : ℕ) {n : ℕ} (t : R) (N : RSGraph n) : R :=
  ((q : R) ^ n)⁻¹ * ∑ σ : Fin n → Fin q, rsW q t N σ

/-- `F` of the multigraph with edge list `e : Fin m → [n]²`:
`q^{-n} ∑_σ ∏_j M_t(σ_{u_j}, σ_{v_j})` with `e_j = (u_j, v_j)`. -/
def rsSeqF (q : ℕ) {n m : ℕ} (t : ℝ) (e : Fin m → Fin n × Fin n) : ℝ :=
  ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q, ∏ j, rsM q t (σ (e j).1) (σ (e j).2)

/-- `c̄_m = E[F log F | m] / E[F | m]` at the real point `x` (proof of Lemma C.3), where, given
`m`, the `m` edges are independent uniform ordered pairs of `[n]²` and `F = F_G(x)`; the
normalizations `n^{-2m}` of the two averages cancel. -/
def rsCbar (q n m : ℕ) (x : ℝ) : ℝ :=
  (∑ e : Fin m → Fin n × Fin n, rsSeqF q (tRe q x) e * Real.log (rsSeqF q (tRe q x) e)) /
    ∑ e : Fin m → Fin n × Fin n, rsSeqF q (tRe q x) e

/-- [CKPZ, Proposition 3.6] for the Potts weight `M_x` with `q` colors, as read in the proof of
Lemma C.3, `limsup_n n⁻¹ ∑_m P(m) c̄_m ≤ sup_{ν ∈ 𝒫_u} Ψ_{s,x}(ν)` with `m ∼ Pois(sn/2)`, written
without `limsup` and `sup`: for every `x ∈ (0,1)`, `s > 0`, every upper bound `η` of `Ψ_{s,x}`
on `𝒫_u` and every `ε > 0`, eventually `∑_m P(m) c̄_m ≤ (η + ε) n`. -/
def CKPZProp36 (q : ℕ) : Prop :=
  ∀ x : ℝ, 0 < x → x < 1 → ∀ s : ℝ, 0 < s → ∀ η : ℝ, (∀ ν ∈ rsPu q, bethePsi q s x ν ≤ η) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∑' m : ℕ, poisPMF (s * n / 2) m * rsCbar q n m x ≤ (η + ε) * n

/-! ## Appendix C: statements -/

/-- **Proposition C.2 (`prop:rs-first-moment`).** "Fix an integer `q ≥ 3`, `x_* ∈ [0,1)`, and
`0 < d < d_cond(q,x_*)`, and let `G_n ∼ G(n,d/n)`. Then `d t(x_*)² < 1`, and there exists an open
neighborhood `W ⊂ ℂ \ {-(q-1)}` of `[x_*,1]` such that
`sup_n sup_{z ∈ W} E|Ẑ_{G_n}(t(z))| < ∞` (C.2)."  The supremum is a bound `B` for all `n ≥ d`
and `z ∈ W`. -/
def Proposition_C_2 : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ xs : ℝ, 0 ≤ xs → xs < 1 → ∀ d : ℝ, 0 < d → d < dCond q xs →
    d * tRe q xs ^ 2 < 1 ∧
      ∃ W : Set ℂ, IsOpen W ∧ (∀ x ∈ Set.Icc xs 1, (x : ℂ) ∈ W) ∧
        (∀ z ∈ W, z + q - 1 ≠ 0) ∧
        ∃ B : ℝ, ∀ n : ℕ, d ≤ n → ∀ z ∈ W,
          erExp n (d / n) (fun G => ‖(zhat G q).eval (tOf q z)‖) ≤ B

/-- **Proposition C.2 (`prop:rs-first-moment`), `t`-plane form**, as the proof of Theorem C.1
uses it: "`L_r(I_{s_*}) ⊂ t(W)` for some `r > 0`, and (C.2) gives (6.1)", where
`I_{s_*} = t([x_*,1]) = [t(x_*), 0]`.  Under the hypotheses of Proposition C.2: `d t(x_*)² < 1`,
and for some `r > 0` and `B`, `E|Ẑ_{G_n}(t)| ≤ B` for all `n ≥ d` and `t ∈ L_r(I_{s_*})`. -/
def Proposition_C_2_tube : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ xs : ℝ, 0 ≤ xs → xs < 1 → ∀ d : ℝ, 0 < d → d < dCond q xs →
    d * tRe q xs ^ 2 < 1 ∧ ∃ r > 0, ∃ B : ℝ, ∀ n : ℕ, d ≤ n →
      ∀ t ∈ tube (-tRe q xs) r, erExp n (d / n) (fun G => ‖(zhat G q).eval t‖) ≤ B

/-- **Lemma C.3 (`lem:rs-ckpz`), monotonicity.** "Fix an integer `q ≥ 3`. The threshold
`x ↦ d_cond(q,x)` is nondecreasing on `[0,1)` …" -/
def Lemma_C_3_monotone : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ x y : ℝ, 0 ≤ y → y ≤ x → x < 1 → dCond q y ≤ dCond q x

/-- **Lemma C.3 (`lem:rs-ckpz`), Kesten–Stigum bound.** "… and satisfies
`d_cond(q,x) ≤ t(x)^{-2}`."  For every `x ∈ [0,1)`, where `t(x) ≠ 0`. -/
def Lemma_C_3_ks_bound : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ x : ℝ, 0 ≤ x → x < 1 → dCond q x ≤ (tRe q x ^ 2)⁻¹

/-- **Lemma C.3 (`lem:rs-ckpz`), planted free energy.** "Moreover, for every `x ∈ (0,1)` and
`0 < s < d_cond(q,x)`, `E_{𝖯_s}[F_G(x) log F_G(x)] = o(n)` (C.5)."  `𝖯_s` is the ordered Poisson
multigraph defined before (C.3), with independent `Pois(s/(2n))` edge counts on all `n²` ordered
pairs, loops included, and `o(n)` is Mathlib's `=o[atTop]`. -/
def Lemma_C_3_free_energy : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ x : ℝ, 0 < x → x < 1 → ∀ s : ℝ, 0 < s → s < dCond q x →
    (∀ n : ℕ, Summable fun N : RSGraph n =>
        poisPi (rsMean n s) N * (rsF q (tRe q x) N * Real.log (rsF q (tRe q x) N))) ∧
    (fun n : ℕ => rsExp n s (fun N => rsF q (tRe q x) N * Real.log (rsF q (tRe q x) N)))
      =o[atTop] (fun n : ℕ => (n : ℝ))

/-- **[CKPZ, Proposition 3.6] for the Potts antiferromagnet**, as the proof of Lemma C.3 applies
it: "[CKPZ, Proposition 3.6] reads `limsup_n n^{-1} E c̄_m ≤ sup_ν Ψ_{s,x}(ν)`."  For every
integer `q ≥ 2`, in the form `CKPZProp36 q`; the paper identifies the quantities of [CKPZ] with
these (`ln Z = n ln q + ln F`, Bethe functional `ln q + Ψ_{s,x}`), and the statement here is the
identified form, which the library proves rather than cites. -/
def CKPZ_Proposition_3_6 : Prop :=
  ∀ q : ℕ, 2 ≤ q → CKPZProp36 q

end

end PaperStatements
