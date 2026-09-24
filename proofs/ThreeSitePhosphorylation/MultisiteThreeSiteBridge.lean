import proofs.ThreeSitePhosphorylation.AttractingSource
import proofs.ThreeSitePhosphorylation.MultisiteChart

/-! Literal coordinate equivalence for the three-site base of the all-site
construction. No topology or norm is placed on the structured full state. -/
namespace ThreeSitePhosphorylation.MultisiteThreeSiteBridge
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

def repack (x : State) : PhosphorylationSharpness.State 3 where
  S := ![x 0,x 1,x 2,x 3]
  E := x 4
  F := x 5
  C := ![x 6,x 7,x 8]
  D := ![x 9,x 10,x 11]

def unpack (x : PhosphorylationSharpness.State 3) : State :=
  ![x.S 0,x.S 1,x.S 2,x.S 3,x.E,x.F,x.C 0,x.C 1,x.C 2,x.D 0,x.D 1,x.D 2]

def repackRates (k : Rates) : PhosphorylationSharpness.Rates 3 where
  a := ![k 0,k 3,k 6]
  b := ![k 1,k 4,k 7]
  c := ![k 2,k 5,k 8]
  alpha := ![k 9,k 12,k 15]
  beta := ![k 10,k 13,k 16]
  gamma := ![k 11,k 14,k 17]

theorem unpack_repack (x : State) : unpack (repack x)=x := by
  funext i
  fin_cases i <;> rfl

theorem repack_unpack (x : PhosphorylationSharpness.State 3) : repack (unpack x)=x := by
  apply MultisiteChart.state_ext
  · funext i; fin_cases i <;> rfl
  · rfl
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem repack_field (k : Rates) (x : State) :
    repack (field k x)=PhosphorylationSharpness.field (repackRates k) (repack x) := by
  apply MultisiteChart.state_ext
  · funext i
    fin_cases i <;>
      simp [repack,repackRates,field,balance,flux,PhosphorylationSharpness.field,
        PhosphorylationSharpness.kinaseNet,PhosphorylationSharpness.phosphataseNet,
        Fin.sum_univ_succ] <;> ring
  · simp [repack,repackRates,field,balance,flux,PhosphorylationSharpness.field,
      PhosphorylationSharpness.kinaseNet,Fin.sum_univ_succ]
    ring
  · simp [repack,repackRates,field,balance,flux,PhosphorylationSharpness.field,
      PhosphorylationSharpness.phosphataseNet,Fin.sum_univ_succ]
    ring
  · funext i
    fin_cases i <;>
      simp [repack,repackRates,field,balance,flux,PhosphorylationSharpness.field,
        PhosphorylationSharpness.kinaseNet]
  · funext i
    fin_cases i <;>
      simp [repack,repackRates,field,balance,flux,PhosphorylationSharpness.field,
        PhosphorylationSharpness.phosphataseNet]

theorem repack_totals (x : State) :
    PhosphorylationSharpness.totalE (repack x)=totalE x ∧
    PhosphorylationSharpness.totalF (repack x)=totalF x ∧
    PhosphorylationSharpness.totalS (repack x)=totalS x := by
  simp [PhosphorylationSharpness.totalE,PhosphorylationSharpness.totalF,
    PhosphorylationSharpness.totalS,totalE,totalF,totalS,repack,Fin.sum_univ_succ]
  constructor
  · ring
  constructor <;> ring

theorem repack_positive (x : State) (hx : ∀ i,0<x i) : (repack x).Positive := by
  refine ⟨?_,hx 4,hx 5,?_,?_⟩
  · intro i; fin_cases i <;> exact hx _
  · intro i; fin_cases i <;> exact hx _
  · intro i; fin_cases i <;> exact hx _

theorem unpack_positive (x : PhosphorylationSharpness.State 3) (hx : x.Positive) :
    ∀ i,0<unpack x i := by
  intro i
  fin_cases i <;> dsimp [unpack]
  all_goals first | exact hx.1 _ | exact hx.2.1 | exact hx.2.2.1 |
    exact hx.2.2.2.1 _ | exact hx.2.2.2.2 _

theorem repack_rates_positive (k : Rates) (hk : ∀ i,0<k i) : (repackRates k).Positive := by
  intro i
  fin_cases i <;> refine ⟨hk _,hk _,hk _,hk _,hk _,hk _⟩

def toMultisite (y : ReducedState) : MultisiteChart.ReducedState 3 :=
  MultisiteChart.project (repack (AttractingWitness.affineChart y))

def fromMultisite (v : MultisiteChart.ReducedState 3) : ReducedState :=
  project (unpack (MultisiteChart.chart (totalE AttractingWitness.state)
    (totalF AttractingWitness.state) (totalS AttractingWitness.state) v)) -
    project AttractingWitness.state

theorem chart_toMultisite (y : ReducedState) :
    MultisiteChart.chart (totalE AttractingWitness.state) (totalF AttractingWitness.state)
      (totalS AttractingWitness.state) (toMultisite y)=repack (AttractingWitness.affineChart y) := by
  have h := repack_totals (AttractingWitness.affineChart y)
  have g := AttractingWitness.affineChart_totals y
  exact MultisiteChart.chart_project_of_totals _ _ _ _
    (h.1.trans g.1) (h.2.1.trans g.2.1) (h.2.2.trans g.2.2)

theorem from_toMultisite (y : ReducedState) : fromMultisite (toMultisite y)=y := by
  unfold fromMultisite
  rw [chart_toMultisite,unpack_repack,AttractingWitness.affineChart_project]

theorem affineChart_fromMultisite (v : MultisiteChart.ReducedState 3) :
    AttractingWitness.affineChart (fromMultisite v)=
      unpack (MultisiteChart.chart (totalE AttractingWitness.state)
        (totalF AttractingWitness.state) (totalS AttractingWitness.state) v) := by
  let x := MultisiteChart.chart (totalE AttractingWitness.state)
    (totalF AttractingWitness.state) (totalS AttractingWitness.state) v
  have h := repack_totals (unpack x)
  rw [repack_unpack] at h
  have g := MultisiteChart.chart_totals (totalE AttractingWitness.state)
    (totalF AttractingWitness.state) (totalS AttractingWitness.state) v
  exact AttractingWitness.affineChart_covers_class (unpack x)
    (h.1.symm.trans g.1) (h.2.1.symm.trans g.2.1) (h.2.2.symm.trans g.2.2)

theorem to_fromMultisite (v : MultisiteChart.ReducedState 3) : toMultisite (fromMultisite v)=v := by
  unfold toMultisite
  rw [affineChart_fromMultisite,repack_unpack,MultisiteChart.project_chart]

end
end ThreeSitePhosphorylation.MultisiteThreeSiteBridge
