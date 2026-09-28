module

public import Mathlib

@[expose] public section

/-!
# Attracting Hopf oscillations in sequential distributive multisite phosphorylation

The n-site sequential distributive phosphorylation cycle has species
S_0..S_n (substrate with i phosphorylated sites), the free kinase E and phosphatase F,
kinase complexes C_0..C_(n-1) and phosphatase complexes D_0..D_(n-1). Site i carries the
mass-action reactions

  S_i + E ⇌ C_i → S_(i+1) + E   (rates a_i, b_i, c_i)
  S_(i+1) + F ⇌ D_i → S_i + F   (rates alpha_i, beta_i, gamma_i).

Its three conserved totals are the kinase, phosphatase and substrate totals.
The compatibility class of a state `x` is the set of states that have the same three totals.

**Claim.** For every `n ≥ 3` there is a rate family `k : ℝ → Rates n` that is affine
in the parameter, componentwise. There is also a positive state `x` that is an equilibrium
of `k r` for every `r`, and the rates are positive for `r` near `0`. Further, there is a
frequency `w > 0`, a parameter branch `par`, a period branch `per` and a family `γ a` of
full-species trajectories with these properties:

* `par a → 0` and `per a → 2π/w` as `a → 0`, and `γ a` converges uniformly to `x`;
* for every sufficiently small amplitude `a > 0`: the rates `k (par a)` are positive,
  and `par a < 0`, which is the supercritical side. Also `γ a` is a nonconstant,
  `per a`-periodic solution of the literal mass-action field. It is strictly positive in
  every species, and its totals equal those of `x`.
* each such orbit is orbitally asymptotically stable *relative to its compatibility
  class*. For every `ε > 0` there is an open neighbourhood `O` of the whole orbit such that
  every state `v ∈ O` with the totals of `x` has a unique global forward solution. That
  solution keeps the totals, stays positive, stays within `ε` of the orbit and converges
  to the orbit in distance.

Scope. The statement is existential in the rate family, for each `n`. It does not assert
inheritance from an arbitrary Hurwitz parent with fixed unit added-site rates. It says
nothing about the `n = 1, 2` exclusions, the `2n-1` equilibrium count (entry P080) or
quantitative constants.

The definitions below are reproduced verbatim, with the same names and namespaces, from
the proof modules `proofs/PhosphorylationSharpness/Source.lean`,
`proofs/ThreeSitePhosphorylation/ScaledAffineFamily.lean` and
`proofs/ThreeSitePhosphorylation/AllSiteAttractingFamily.lean`. Only docstrings differ.
The Challenge imports all of `Mathlib`, as every proof module does, so that notation and
instance resolution (topology, metric, derivative) elaborate in the same environment.
It contains no proof-development import.
-/

namespace PhosphorylationSharpness
noncomputable section
open scoped BigOperators

/-- Concentrations of the n+1 substrate forms, two free enzymes, and n complexes
for each enzyme. All concentrations are real; positivity is imposed explicitly. -/
structure State (n : ℕ) where
  S : Fin (n+1) → ℝ
  E : ℝ
  F : ℝ
  C : Fin n → ℝ
  D : Fin n → ℝ

/-- Binding, dissociation, and catalytic rates for kinase (a,b,c) and
phosphatase (alpha,beta,gamma), separately for each site. -/
structure Rates (n : ℕ) where
  a : Fin n → ℝ
  b : Fin n → ℝ
  c : Fin n → ℝ
  alpha : Fin n → ℝ
  beta : Fin n → ℝ
  gamma : Fin n → ℝ

/-- Every reaction rate constant is strictly positive. -/
def Rates.Positive {n : ℕ} (k : Rates n) : Prop :=
  ∀ i, 0 < k.a i ∧ 0 < k.b i ∧ 0 < k.c i ∧
    0 < k.alpha i ∧ 0 < k.beta i ∧ 0 < k.gamma i

/-- Every free species and enzyme-complex concentration is strictly positive. -/
def State.Positive {n : ℕ} (x : State n) : Prop :=
  (∀ i, 0 < x.S i) ∧ 0 < x.E ∧ 0 < x.F ∧ (∀ i, 0 < x.C i) ∧ (∀ i, 0 < x.D i)

/-- Net kinase binding flux, excluding the catalytic reaction. -/
def kinaseNet {n : ℕ} (k : Rates n) (x : State n) (i : Fin n) : ℝ :=
  k.a i*x.S i.castSucc*x.E-k.b i*x.C i

/-- Net phosphatase binding flux, excluding the catalytic reaction. -/
def phosphataseNet {n : ℕ} (k : Rates n) (x : State n) (i : Fin n) : ℝ :=
  k.alpha i*x.S i.succ*x.F-k.beta i*x.D i

/-- Literal mass-action vector field for the sequential distributive cycle. -/
def field {n : ℕ} (k : Rates n) (x : State n) : State n where
  S j := ∑ i : Fin n, (
    (if i.castSucc = j then -kinaseNet k x i+k.gamma i*x.D i else 0) +
    (if i.succ = j then k.c i*x.C i-phosphataseNet k x i else 0))
  E := ∑ i, (-kinaseNet k x i+k.c i*x.C i)
  F := ∑ i, (-phosphataseNet k x i+k.gamma i*x.D i)
  C i := kinaseNet k x i-k.c i*x.C i
  D i := phosphataseNet k x i-k.gamma i*x.D i

/-- Each component of the mass-action vector field vanishes. -/
def Equilibrium {n : ℕ} (k : Rates n) (x : State n) : Prop :=
  (∀ i, (field k x).S i=0) ∧ (field k x).E=0 ∧ (field k x).F=0 ∧
    (∀ i, (field k x).C i=0) ∧ (∀ i, (field k x).D i=0)

/-- Total free and bound kinase. -/
def totalE {n : ℕ} (x : State n) : ℝ := x.E+∑ i, x.C i
/-- Total free and bound phosphatase. -/
def totalF {n : ℕ} (x : State n) : ℝ := x.F+∑ i, x.D i
/-- Total free and enzyme-bound substrate. -/
def totalS {n : ℕ} (x : State n) : ℝ := (∑ i, x.S i)+(∑ i, x.C i)+(∑ i, x.D i)

end
end PhosphorylationSharpness

namespace ThreeSitePhosphorylation.ScaledAffineFamily
noncomputable section
open PhosphorylationSharpness

/-- The rate family `offset + r • slope`, written componentwise. -/
def affineRates {n : ℕ} (offset slope : Rates n) (r : ℝ) : Rates n where
  a i := offset.a i+r*slope.a i
  b i := offset.b i+r*slope.b i
  c i := offset.c i+r*slope.c i
  alpha i := offset.alpha i+r*slope.alpha i
  beta i := offset.beta i+r*slope.beta i
  gamma i := offset.gamma i+r*slope.gamma i

/-- Every rate constant of the family is an affine function of the parameter. -/
def ComponentwiseAffine {n : ℕ} (k : ℝ → Rates n) : Prop :=
  ∃ offset slope : Rates n, ∀ r, k r=affineRates offset slope r

end
end ThreeSitePhosphorylation.ScaledAffineFamily

namespace ThreeSitePhosphorylation.AllSiteAttractingFamily
noncomputable section
open Filter
open scoped Topology
open ScaledAffineFamily

/-- Literal species index: `S_0..S_n`, then `E,F`, then `C_0..C_{n-1}`, `D_0..D_{n-1}`. -/
abbrev Species (n : ℕ) := Fin (n+1) ⊕ (Fin 2 ⊕ (Fin n ⊕ Fin n))

/-- A structured state as a full species vector. -/
def speciesVec {n : ℕ} (x : PhosphorylationSharpness.State n) : Species n → ℝ :=
  Sum.elim x.S (Sum.elim ![x.E,x.F] (Sum.elim x.C x.D))

/-- A full species vector as a structured state. -/
def ofSpecies {n : ℕ} (v : Species n → ℝ) : PhosphorylationSharpness.State n where
  S i := v (Sum.inl i)
  E := v (Sum.inr (Sum.inl 0))
  F := v (Sum.inr (Sum.inl 1))
  C i := v (Sum.inr (Sum.inr (Sum.inl i)))
  D i := v (Sum.inr (Sum.inr (Sum.inr i)))

/-- The literal mass-action field on full species vectors. -/
def speciesField {n : ℕ} (k : PhosphorylationSharpness.Rates n) (v : Species n → ℝ) :
    Species n → ℝ :=
  speciesVec (PhosphorylationSharpness.field k (ofSpecies v))

/-- The three conserved totals of a full state agree with those of `x`
(same compatibility class). -/
def SameTotals {n : ℕ} (y x : PhosphorylationSharpness.State n) : Prop :=
  PhosphorylationSharpness.totalE y=PhosphorylationSharpness.totalE x ∧
    PhosphorylationSharpness.totalF y=PhosphorylationSharpness.totalF x ∧
    PhosphorylationSharpness.totalS y=PhosphorylationSharpness.totalS x

/-- **All-site attracting Hopf theorem.** For every `n ≥ 3` there is a
componentwise-affine rate family with a positive parameter-independent equilibrium. It has
a supercritical family of positive nonconstant periodic mass-action orbits (onset side
`par < 0`), and these shrink to the equilibrium with period tending to `2π/w`. Each orbit
is orbitally asymptotically stable relative to its compatibility class. -/
theorem all_site_attracting_hopf (n : ℕ) (hn : 3 ≤ n) :
    ∃ (k : ℝ → PhosphorylationSharpness.Rates n) (x : PhosphorylationSharpness.State n),
      ComponentwiseAffine k ∧ x.Positive ∧
      (∀ r, PhosphorylationSharpness.Equilibrium (k r) x) ∧
      (∀ᶠ r in 𝓝 (0:ℝ), (k r).Positive) ∧
      ∃ w : ℝ, 0<w ∧ ∃ (par per : ℝ → ℝ) (γ : ℝ → ℝ → Species n → ℝ),
      Tendsto par (𝓝 0) (𝓝 0) ∧ Tendsto per (𝓝 0) (𝓝 (2*Real.pi/w)) ∧
      (∀ ε>0, ∀ᶠ a in 𝓝 (0:ℝ), ∀ t, dist (γ a t) (speciesVec x)<ε) ∧
      ∀ᶠ a in 𝓝[>] (0:ℝ),
        (k (par a)).Positive ∧ par a<0 ∧ 0<per a ∧
        Function.Periodic (γ a) (per a) ∧
        (∀ t, HasDerivAt (γ a) (speciesField (k (par a)) (γ a t)) t) ∧
        (∃ t, γ a t ≠ γ a 0) ∧ (∀ t i, 0<γ a t i) ∧
        (∀ t, SameTotals (ofSpecies (γ a t)) x) ∧
        ∀ ε>0, ∃ O : Set (Species n → ℝ), IsOpen O ∧ Set.range (γ a) ⊆ O ∧
          ∀ v∈O, SameTotals (ofSpecies v) x → ∃ V : ℝ → Species n → ℝ,
            V 0=v ∧
            (∀ t, 0 ≤ t → HasDerivWithinAt V (speciesField (k (par a)) (V t)) (Set.Ici 0) t) ∧
            (∀ t, 0 ≤ t → SameTotals (ofSpecies (V t)) x) ∧
            (∀ t, 0 ≤ t → ∀ i, 0<V t i) ∧
            (∀ t, 0 ≤ t → ∃ y∈Set.range (γ a), dist (V t) y<ε) ∧
            Tendsto (fun t => Metric.infDist (V t) (Set.range (γ a))) atTop (𝓝 0) ∧
            (∀ W : ℝ → Species n → ℝ, W 0=v →
              (∀ t, 0 ≤ t → HasDerivWithinAt W (speciesField (k (par a)) (W t)) (Set.Ici 0) t) →
              ∀ t, 0 ≤ t → W t=V t) := by
  sorry

end
end ThreeSitePhosphorylation.AllSiteAttractingFamily
