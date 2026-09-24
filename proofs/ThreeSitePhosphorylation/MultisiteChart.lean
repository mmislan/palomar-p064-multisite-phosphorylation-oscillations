import proofs.PhosphorylationSharpness.Source

namespace ThreeSitePhosphorylation.MultisiteChart
noncomputable section
open PhosphorylationSharpness
open scoped BigOperators

/-- Coordinates are S1,...,Sn, then the kinase and phosphatase complexes. -/
abbrev ReducedState (n : ℕ) := (Fin n → ℝ) × ((Fin n → ℝ) × (Fin n → ℝ))

def chart {n : ℕ} (Et Ft St : ℝ) (y : ReducedState n) : PhosphorylationSharpness.State n where
  S := Fin.cons (St-(∑ i, y.1 i)-(∑ i, y.2.1 i)-(∑ i, y.2.2 i)) y.1
  E := Et-∑ i, y.2.1 i
  F := Ft-∑ i, y.2.2 i
  C := y.2.1
  D := y.2.2

def project {n : ℕ} (x : PhosphorylationSharpness.State n) : ReducedState n :=
  ((fun i => x.S i.succ),(x.C,x.D))

theorem state_ext {n : ℕ} (x y : PhosphorylationSharpness.State n)
    (hs : x.S=y.S) (he : x.E=y.E) (hf : x.F=y.F) (hc : x.C=y.C) (hd : x.D=y.D) : x=y := by
  cases x
  cases y
  simp_all

/-- Each reaction conserves the three inventories, uniformly in the number
of sites. The substrate sum is exchanged with the reaction sum. -/
theorem conservation {n : ℕ} (k : PhosphorylationSharpness.Rates n)
    (x : PhosphorylationSharpness.State n) :
    totalE (field k x)=0 ∧ totalF (field k x)=0 ∧ totalS (field k x)=0 := by
  have hs : (∑ j, (field k x).S j)=
      ∑ i, ((-kinaseNet k x i+k.gamma i*x.D i)+(k.c i*x.C i-phosphataseNet k x i)) := by
    dsimp only [field]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp [Finset.sum_add_distrib]
  refine ⟨?_,?_,?_⟩
  · dsimp only [totalE,field]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    ring
  · dsimp only [totalF,field]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    ring
  · unfold totalS
    rw [hs]
    dsimp only [field]
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    ring

theorem chart_totals {n : ℕ} (Et Ft St : ℝ) (y : ReducedState n) :
    totalE (chart Et Ft St y)=Et ∧ totalF (chart Et Ft St y)=Ft ∧
      totalS (chart Et Ft St y)=St := by
  simp only [totalE,totalF,totalS,chart,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
  constructor
  · ring
  constructor <;> ring

theorem project_chart {n : ℕ} (Et Ft St : ℝ) (y : ReducedState n) :
    project (chart Et Ft St y)=y := by
  rcases y with ⟨s,c,d⟩
  simp [project,chart]

/-- Every full state is recovered from its inventories and reduced coordinates. -/
theorem chart_project {n : ℕ} (x : PhosphorylationSharpness.State n) :
    chart (totalE x) (totalF x) (totalS x) (project x)=x := by
  apply state_ext
  · funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [chart,project,Fin.cons_zero,totalS,Fin.sum_univ_succ]
      ring
    · simp [chart,project]
  · simp [chart,project,totalE]
  · simp [chart,project,totalF]
  · rfl
  · rfl

theorem chart_project_of_totals {n : ℕ} (Et Ft St : ℝ)
    (x : PhosphorylationSharpness.State n)
    (he : totalE x=Et) (hf : totalF x=Ft) (hs : totalS x=St) :
    chart Et Ft St (project x)=x := by
  simpa only [he,hf,hs] using chart_project x

/-- The linear tangent reconstruction has zero inventory in all three totals. -/
def tangent {n : ℕ} (v : ReducedState n) : PhosphorylationSharpness.State n := chart 0 0 0 v

def reducedField {n : ℕ} (Et Ft St : ℝ) (k : PhosphorylationSharpness.Rates n)
    (y : ReducedState n) : ReducedState n := project (field k (chart Et Ft St y))

theorem tangent_totals {n : ℕ} (v : ReducedState n) :
    totalE (tangent v)=0 ∧ totalF (tangent v)=0 ∧ totalS (tangent v)=0 :=
  chart_totals 0 0 0 v

theorem project_tangent {n : ℕ} (v : ReducedState n) : project (tangent v)=v :=
  project_chart 0 0 0 v

/-- The literal full mass-action field is exactly the tangent reconstruction
of the reduced field. In particular the omitted S0 equation follows from
conservation, rather than an additional dynamical hypothesis. -/
theorem reduced_field_tangent {n : ℕ} (Et Ft St : ℝ)
    (k : PhosphorylationSharpness.Rates n) (y : ReducedState n) :
    tangent (reducedField Et Ft St k y)=field k (chart Et Ft St y) := by
  have hc := conservation k (chart Et Ft St y)
  exact chart_project_of_totals 0 0 0 _ hc.1 hc.2.1 hc.2.2

theorem reduced_field_components {n : ℕ} (Et Ft St : ℝ)
    (k : PhosphorylationSharpness.Rates n) (y : ReducedState n) (i : Fin n) :
    (reducedField Et Ft St k y).1 i=(field k (chart Et Ft St y)).S i.succ ∧
    (reducedField Et Ft St k y).2.1 i=(field k (chart Et Ft St y)).C i ∧
    (reducedField Et Ft St k y).2.2 i=(field k (chart Et Ft St y)).D i := by
  exact ⟨rfl,rfl,rfl⟩

end
end ThreeSitePhosphorylation.MultisiteChart
