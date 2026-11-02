/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSMain
import ERZeroFreeness.CKMain

/-!
# Appendix C without external hypotheses

Appendix C is proved in two layers.  The `RS*` modules (main results in `RSMain` and
`RSFreeEnergy`) prove Lemma C.3, Proposition C.2 and Theorem C.1 of the paper from the single
explicit hypothesis `CKPZProp36 q`, the planted free-energy bound [CKPZ, Prop. 3.6].  The `CK*`
modules prove that hypothesis for every `q ≥ 2` (`ckpz_prop36` in `CKMain`), following the
self-contained proof in `docs/ckpz-proof.md`.  This file discharges the hypothesis, so the
statements below depend only on Mathlib and Lean's standard axioms.

* `rs_free_energy_unconditional` — Lemma C.3 (`eq:rs-input`);
* `rs_first_moment_tube_unconditional`, `rs_first_moment_zplane_unconditional` —
  Proposition C.2 (`prop:rs-first-moment`), `t`-plane and `z`-plane forms;
* `potts_zero_free_up_to_condensation` — Theorem C.1 (`thm:rs-extension`), zero-freeness part.

The hypothesis range `0 < d < d_cond(q,x_*)` is nonempty: `rs_dCond_pos` (`RSBethePos`) proves
`d_cond(q,x) > 0` for `x ∈ [0,1)` (its proof gives `d_cond(q,x) ≥ 1/9`), so none of these
statements is vacuous.
-/

open Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- **Lemma C.3 (`eq:rs-input`).** For `q ≥ 3`, `x ∈ (0,1)` and `0 < s < d_cond(q,x)`:
`E_{𝖯_s}[F_G(x) log F_G(x)] = o(n)`. -/
theorem rs_free_energy_unconditional {q : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {s : ℝ} (hs0 : 0 < s) (hs : s < dCond q x) :
    (fun n : ℕ => rsExp n s (fun N => rsF q (tRe q x) N * Real.log (rsF q (tRe q x) N)))
      =o[atTop] (fun n : ℕ => (n : ℝ)) :=
  rs_free_energy hq (ckpz_prop36 (by omega)) hx0 hx1 hs0 hs

/-- **Proposition C.2 (`prop:rs-first-moment`), `t`-plane form.** For `q ≥ 3`, `x_* ∈ [0,1)` and
`0 < d < d_cond(q,x_*)`: `d t(x_*)² < 1`, and for some `r > 0` the first moment
`E_{G(n,d/n)} |Ẑ_G(t)|` is bounded uniformly in `n ≥ d` and `t ∈ L_r([t(x_*), 0])`. -/
theorem rs_first_moment_tube_unconditional {q : ℕ} (hq : 3 ≤ q) {xs : ℝ} (hxs0 : 0 ≤ xs)
    (hxs1 : xs < 1) {d : ℝ} (hd : 0 < d) (hdc : d < dCond q xs) :
    d * tRe q xs ^ 2 < 1 ∧ ∃ r > 0, ∃ B : ℝ, ∀ n : ℕ, d ≤ n →
      ∀ t ∈ tube (-tRe q xs) r, erExp n (d / n) (fun G => ‖(zhat G q).eval t‖) ≤ B :=
  rs_first_moment_tube hq (ckpz_prop36 (by omega)) hxs0 hxs1 hd hdc

/-- **Proposition C.2 (`prop:rs-first-moment`), the paper's `z`-plane form `eq:rs-gn-moment`.**
`d t(x_*)² < 1`, and there is an open neighbourhood `W ⊂ ℂ \ {-(q-1)}` of `[x_*,1]` with
`sup_{n ≥ d} sup_{z ∈ W} E_{G(n,d/n)} |Ẑ_G(t(z))| < ∞`. -/
theorem rs_first_moment_zplane_unconditional {q : ℕ} (hq : 3 ≤ q) {xs : ℝ} (hxs0 : 0 ≤ xs)
    (hxs1 : xs < 1) {d : ℝ} (hd : 0 < d) (hdc : d < dCond q xs) :
    d * tRe q xs ^ 2 < 1 ∧
      ∃ W : Set ℂ, IsOpen W ∧ (∀ x ∈ Set.Icc xs 1, (x : ℂ) ∈ W) ∧
        (∀ z ∈ W, z + q - 1 ≠ 0) ∧
        ∃ B : ℝ, ∀ n : ℕ, d ≤ n → ∀ z ∈ W,
          erExp n (d / n) (fun G => ‖(zhat G q).eval (tOf q z)‖) ≤ B :=
  rs_first_moment_zplane hq (ckpz_prop36 (by omega)) hxs0 hxs1 hd hdc

/-- **Theorem C.1 (`thm:rs-extension`), zero-freeness part.** Fix an integer `q ≥ 3`,
`x_* ∈ [0,1)` and `0 < d < d_cond(q,x_*)`.  There is `ρ > 0` such that, with probability tending
to one over `G_n ∼ G(n,d/n)`, `Z_{G_n}(q,z) ≠ 0` whenever `dist(z,[x_*,1]) ≤ ρ`. -/
theorem potts_zero_free_up_to_condensation {q : ℕ} (hq : 3 ≤ q) {xs : ℝ} (hx0 : 0 ≤ xs)
    (hx1 : xs < 1) {d : ℝ} (hd : 0 < d) (hdc : d < dCond q xs) :
    ∃ ρ > 0, Tendsto (fun n : ℕ => erProb n (d / n)
        {G | ∀ z : ℂ, (∃ x : ℝ, x ∈ Set.Icc xs 1 ∧ ‖z - x‖ ≤ ρ) → pottsZ G q z ≠ 0})
      atTop (𝓝 1) :=
  potts_zero_free_condensation hq (ckpz_prop36 (by omega)) hx0 hx1 hd hdc

end

end ERZeroFreeness
