# P064: claim-to-evidence correspondence

Source-reading review dated 2026-09-24. No Lean was executed for this review.

This is an agent-assisted reading of four sources: `Registry/P064/Challenge.lean`, the
research proof source `proofs/ThreeSitePhosphorylation/AllSiteAttractingFamily.lean` and
its imported definitions, the research integration handoff and receipt, and the companion
manuscript source `papers/P064/manuscript/main.tex`. It is not an independent human
mathematical review. None of the following has been run on the Lean 4.35.0-rc2 target:
the Challenge statement compilation, the Solution build, the Comparator comparison or
the kernel checks.

## Setting

The Challenge restates the literal model of the sequential distributive n-site cycle,
using the same names and definitions as the proof modules.

- `PhosphorylationSharpness.State n` holds the concentrations `S : Fin (n+1) → ℝ`, `E`,
  `F`, `C D : Fin n → ℝ`.
- `Rates n` holds the six per-site rate families `a b c alpha beta gamma`.
- `Rates.Positive` and `State.Positive` require every component to be strictly positive.
- `field k x` is the mass-action vector field of the reactions
  `S_i + E ⇌ C_i → S_(i+1) + E` and `S_(i+1) + F ⇌ D_i → S_i + F`, written through
  `kinaseNet` and `phosphataseNet`.
- `Equilibrium` says that every component of `field` vanishes.
- `totalE`, `totalF` and `totalS` are the three conserved totals.

These definitions are textually identical to `proofs/PhosphorylationSharpness/Source.lean`,
apart from docstrings. They are the same definitions used by entry P080.

From `ScaledAffineFamily`, the Challenge uses:

- `affineRates offset slope r`, the componentwise rate family `offset + r·slope`;
- `ComponentwiseAffine k`, which says `k r = affineRates offset slope r` for some fixed
  `offset` and `slope`.

From `AllSiteAttractingFamily`, it uses:

- `Species n = Fin (n+1) ⊕ (Fin 2 ⊕ (Fin n ⊕ Fin n))`;
- `speciesVec` and `ofSpecies`, which translate between states and full species vectors;
- `speciesField k v = speciesVec (field k (ofSpecies v))`, the literal field on
  `Species n → ℝ`;
- `SameTotals y x`, which says the three totals of `y` equal those of `x`. This is the
  compatibility class, since the class is exactly the set of states with the same three
  totals.

## Selected declaration

### `ThreeSitePhosphorylation.AllSiteAttractingFamily.all_site_attracting_hopf`

**Formal content.** For every `n : ℕ` with `3 ≤ n` there exist `k : ℝ → Rates n` and
`x : State n` such that:

- `ComponentwiseAffine k` and `x.Positive`;
- `Equilibrium (k r) x` for every `r`, so the equilibrium does not depend on the parameter;
- `(k r).Positive` for all `r` in a neighbourhood of `0`.

Further, there exist `w > 0`, `par per : ℝ → ℝ` and `γ : ℝ → ℝ → Species n → ℝ` with:

- `par → 0` and `per → 2π/w` as the amplitude `a → 0`;
- for every `ε > 0`, eventually as `a → 0`, `dist (γ a t) (speciesVec x) < ε` for all `t`.
  This is uniform shrinking to the equilibrium.

Eventually for `a → 0⁺` (that is, on `𝓝[>] 0`), all of the following hold:

- `(k (par a)).Positive`, `par a < 0` and `0 < per a`;
- `γ a` is `per a`-periodic;
- `HasDerivAt (γ a) (speciesField (k (par a)) (γ a t)) t` for every `t`, so `γ a` is an
  entire solution of the literal field;
- `γ a` is nonconstant, and every species is strictly positive for all `t`;
- `SameTotals (ofSpecies (γ a t)) x` for all `t`;
- **relative orbital asymptotic stability.** For every `ε > 0` there is an open
  `O ⊆ Species n → ℝ` containing `Set.range (γ a)`. For every `v ∈ O` with
  `SameTotals (ofSpecies v) x` there is `V` with `V 0 = v`, and `V` is a solution on
  `[0, ∞)`. It is a right-derivative solution: `HasDerivWithinAt … (Set.Ici 0)`. For all
  `t ≥ 0`, `V` keeps the totals of `x`, stays strictly positive and stays within `ε` of a
  point of the orbit. Also `infDist (V t) (range (γ a)) → 0` as `t → ∞`. Every other
  forward solution `W` from `v` on `[0, ∞)` agrees with `V` for `t ≥ 0`.

The statement has no hypothesis other than `3 ≤ n`. The attraction is relative to the
compatibility class: the conclusion is claimed only for initial states with the totals
of `x`.

**Informal claim supported.** For every `n ≥ 3`, the mass-action sequential distributive
n-site cycle has positive rate constants and totals at which a family of positive
nonconstant periodic orbits bifurcates from a positive equilibrium. The bifurcation is on
one side of the critical parameter only (supercritical), the period tends to `2π/w`, and
each orbit is orbitally asymptotically stable within its compatibility class.

**Manuscript correspondence.** The theorem gives the orbit conclusion of Corollary
`cor:alln` ("Attracting oscillations for every n ≥ 3"). It is existential in the rates and
the totals, as the corollary is. Its proof path matches the manuscript's: first the
three-site witness A (Theorem `thm:main`, via `AllSiteHopfInvariant.base_hopf_invariant`),
then iterated site addition (`hopf_iterate`), then a Hopf/attraction argument on the
compatibility chart (`hopf_attracting_family`). The critical parameter is translated to
`0`. The onset side `par < 0` corresponds to the manuscript's `r < r_A`. The Lean indices
`C_0..C_(n-1)` correspond to the manuscript's `C_1..C_n`.

The formal statement exposes the bifurcating orbit family and its stability. It does not
restate the linearization data: the simple pair `±iω`, the stable complement, the
transversal crossing and `l_1 < 0`. The receipt shows that the proof establishes those
data internally (`HopfInvariant`), but they are not part of the compared type.

**Evidence.** Historical strict receipt only:
`all_site_attracting_family.verify.json` in the research workspace. It records
`verified=true`, exit 0, warnings as errors, Lean 4.30.0, lake manifest `a8df0b60…`, and
requested declarations `hopf_attracting_family` and `all_site_attracting_hopf`. The
reported axioms are `propext`, `Classical.choice` and `Quot.sound`. The target source hash
is `355bdf10…1333c`. All 142 modules in the receipt's closure (141 dependencies plus the
target) are byte-identical in this repository; see
`preparation/P064-ALL-SITE-IMPORT.json`. The receipt's `dependency_materialization`
block reports `proof_admissible: false` and `node_status_effect: none`. The top-level
`verified` field is true. The first field appears to be the research workflow's
authority flag, not a compilation failure, but this has not been confirmed.

No target-toolchain evidence exists. Nothing has been compiled on Lean 4.35.0-rc2 with
Mathlib `065356127b`: not the Challenge statement, not the Solution, and no Comparator or
kernel check.

## Literature correspondence

The primary source is N. Vassena, *Sequential and distributive dual futile cycle: Hopf
bifurcation can occur under parameter-rich kinetics but cannot occur under mass action
kinetics*, preprint arXiv:2608.27081v2 (2026). The manuscript bibliography gives no DOI.
The title, author and locators were independently checked against the arXiv source on
2026-09-25. Theorem 5.8 excludes nonzero purely imaginary eigenvalues and hence Hopf
bifurcation for `n = 2` under mass action. The concluding discussion states that whether
the sequential distributive `n`-site cycles with `n ≥ 3` admit Hopf bifurcation under
parameter-rich or mass-action kinetics remains open.

The entry settles the affirmative mass-action direction for every `n ≥ 3`. For some
positive rate constants, periodic orbits bifurcate from a positive equilibrium, and they
are attracting within the compatibility class. The entry does not formalize the
"if and only if" threshold (Theorem `thm:threshold`), which also uses the one-site
Hurwitz lemma and Vassena's `n = 2` theorem. It also leaves open whether `N_2` has
periodic orbits that do not arise from a Hopf bifurcation.

## Evidence boundary

The following are not formalized in the selected declaration:

- The manuscript's site-addition Theorem `thm:alln`. That theorem starts from an
  arbitrary nondegenerate Hurwitz-complement Hopf parent with `n ≥ 1` and fixed added-site
  rates `(2ε/(S_n* E*), 1, 1)` and `(1/F*, 1, 1)`. The formal all-n construction instead
  picks a separating scale and a sufficiently small positive load at each step. It proves
  existence for some constructed affine family, not inheritance with these fixed unit
  rates.
- The `n = 1` and `n = 2` exclusions and the threshold equivalence (Lemma `lem:onesite`,
  Vassena's Theorem 5.8, Theorem `thm:threshold`).
- The explicit witness A data of Theorem `thm:main`: Table 1 rates, the class
  `(119/25, 1379/50, 1106/25)`, the enclosures of `r_A`, `ω_A`, `Re λ'` and `l_1`, and the
  global stability counts for `r > r_A` and `0 < r < r_A`. The existential all-n statement
  at `n = 3` does not identify the family.
- Quantitative constants, parametric robustness (Proposition `prop:robust`), the static
  and clamp theorems, reductions, the finite-amplitude orbit certificates, and the
  thermodynamic realization.
- The `2n−1` steady-state sharpness theorem. That is entry P080.

No conventional analytic premise appears as a hypothesis. The Hopf and attraction
arguments are proved in the imported development, and the statement's only hypothesis
is `3 ≤ n`.

The manuscript describes its formal coverage more weakly than the imported development.
It says the only Lean result is the subcritical-witness existence theorem and that "we do
not claim a formal proof of attraction". Its description of the site-addition step is
stronger than the formal result. See `preparation/P064-MANUSCRIPT-NOTE.md`. The
manuscript and PDF were not edited.

Research proofs are Lean 4.30.0 receipts. Porting to the 4.35.0-rc2 target is unverified.
Challenge/Solution definitional identity has been checked by source text only (see
`entries/P064/README.md`).
