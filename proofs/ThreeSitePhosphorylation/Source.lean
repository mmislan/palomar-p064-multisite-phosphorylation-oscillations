import Mathlib

/-! Literal eighteen-reaction sequential distributive phosphorylation source.
Species order: S0,S1,S2,S3,E,F,C1,C2,C3,D1,D2,D3.
Reaction order: binding, reverse, conversion, for K1,K2,K3,F1,F2,F3.
This module does not assert the analytic Hopf implication. -/
namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 1000000

abbrev State := Fin 12 → ℝ
abbrev Rates := Fin 18 → ℝ

def flux (k : Rates) (x : State) : Fin 18 → ℝ :=
  ![k 0*x 0*x 4, k 1*x 6, k 2*x 6,
    k 3*x 1*x 4, k 4*x 7, k 5*x 7,
    k 6*x 2*x 4, k 7*x 8, k 8*x 8,
    k 9*x 1*x 5, k 10*x 9, k 11*x 9,
    k 12*x 2*x 5, k 13*x 10, k 14*x 10,
    k 15*x 3*x 5, k 16*x 11, k 17*x 11]

def balance (v : Fin 18 → ℝ) : State :=
  ![-v 0+v 1+v 11,
    v 2-v 3+v 4-v 9+v 10+v 14,
    v 5-v 6+v 7-v 12+v 13+v 17,
    v 8-v 15+v 16,
    -v 0+v 1+v 2-v 3+v 4+v 5-v 6+v 7+v 8,
    -v 9+v 10+v 11-v 12+v 13+v 14-v 15+v 16+v 17,
    v 0-v 1-v 2,v 3-v 4-v 5,v 6-v 7-v 8,
    v 9-v 10-v 11,v 12-v 13-v 14,v 15-v 16-v 17]

def field (k : Rates) (x : State) : State := balance (flux k x)
def totalE (x : State) : ℝ := x 4+x 6+x 7+x 8
def totalF (x : State) : ℝ := x 5+x 9+x 10+x 11
def totalS (x : State) : ℝ := x 0+x 1+x 2+x 3+x 6+x 7+x 8+x 9+x 10+x 11

theorem conservation (k : Rates) (x : State) :
    totalE (field k x) = 0 ∧ totalF (field k x) = 0 ∧ totalS (field k x) = 0 := by
  simp [totalE,totalF,totalS,field,balance]
  constructor
  · ring
  constructor <;> ring

def witnessState : State :=
  ![30,13,19/100,9/100,33/10,1,13/25,7/250,39/50,93/10,3/20,5/2]

def witnessRates (r : ℝ) : Rates :=
  ![101/99000,1/520,5/26,101/550,39/14,1950/7,
    1010/627,1/78,50/39,(1+r)/130,r/93,1/93,
    3939/95,13/25,52,101/9,1/250,2/5]

theorem witness_state_positive : ∀ i, 0 < witnessState i := by
  intro i; fin_cases i <;> norm_num [witnessState]

theorem witness_rates_positive (r : ℝ) (hr : 0 < r) : ∀ i, 0 < witnessRates r i := by
  intro i; fin_cases i <;> simp [witnessRates] <;> positivity

theorem witness_flux (r : ℝ) : flux (witnessRates r) witnessState =
    ![101/1000,1/1000,1/10,3939/500,39/500,39/5,101/100,1/100,1,
      (1+r)/10,r/10,1/10,3939/500,39/500,39/5,101/100,1/100,1] := by
  funext i
  fin_cases i
  · change (101/99000 : ℝ)*(30)*(33/10) = 101/1000
    ring
  · change (1/520 : ℝ)*(13/25) = 1/1000
    ring
  · change (5/26 : ℝ)*(13/25) = 1/10
    ring
  · change (101/550 : ℝ)*(13)*(33/10) = 3939/500
    ring
  · change (39/14 : ℝ)*(7/250) = 39/500
    ring
  · change (1950/7 : ℝ)*(7/250) = 39/5
    ring
  · change (1010/627 : ℝ)*(19/100)*(33/10) = 101/100
    ring
  · change (1/78 : ℝ)*(39/50) = 1/100
    ring
  · change (50/39 : ℝ)*(39/50) = 1
    ring
  · change ((1+r)/130 : ℝ)*(13)*(1) = (1+r)/10
    ring
  · change (r/93 : ℝ)*(93/10) = r/10
    ring
  · change (1/93 : ℝ)*(93/10) = 1/10
    ring
  · change (3939/95 : ℝ)*(19/100)*(1) = 3939/500
    ring
  · change (13/25 : ℝ)*(3/20) = 39/500
    ring
  · change (52 : ℝ)*(3/20) = 39/5
    ring
  · change (101/9 : ℝ)*(9/100)*(1) = 101/100
    ring
  · change (1/250 : ℝ)*(5/2) = 1/100
    ring
  · change (2/5 : ℝ)*(5/2) = 1
    ring

theorem witness_equilibrium (r : ℝ) : field (witnessRates r) witnessState = 0 := by
  unfold field
  rw [witness_flux]
  funext i
  fin_cases i
  · change -(101/1000:ℝ)+1/1000+1/10 = 0
    ring
  · change (1/10:ℝ)-3939/500+39/500-(1+r)/10+r/10+39/5 = 0
    ring
  · change (39/5:ℝ)-101/100+1/100-3939/500+39/500+1 = 0
    ring
  · change (1:ℝ)-101/100+1/100 = 0
    ring
  · change -(101/1000:ℝ)+1/1000+1/10-3939/500+39/500+39/5-101/100+1/100+1 = 0
    ring
  · change -((1+r)/10)+r/10+(1/10:ℝ)-3939/500+39/500+39/5-101/100+1/100+1 = 0
    ring
  · change (101/1000:ℝ)-1/1000-1/10 = 0
    ring
  · change (3939/500:ℝ)-39/500-39/5 = 0
    ring
  · change (101/100:ℝ)-1/100-1 = 0
    ring
  · change (1+r)/10-r/10-(1/10:ℝ) = 0
    ring
  · change (3939/500:ℝ)-39/500-39/5 = 0
    ring
  · change (101/100:ℝ)-1/100-1 = 0
    ring

theorem witness_totals :
    totalE witnessState = 1157/250 ∧ totalF witnessState = 259/20 ∧
    totalS witnessState = 28279/500 := by
  change (33/10:ℝ)+13/25+7/250+39/50 = 1157/250 ∧
    (1:ℝ)+93/10+3/20+5/2 = 259/20 ∧
    (30:ℝ)+13+19/100+9/100+13/25+7/250+39/50+93/10+3/20+5/2 = 28279/500
  norm_num

/-- An affine chart in displacement coordinates (u1,u2,u3,C1,C2,C3,D1,D2,D3). -/
def chart (y : Fin 9 → ℝ) : State :=
  fun i => witnessState i +
    ![-y 0-y 3, y 0-y 1-y 4-y 6, y 1-y 2-y 5-y 7, y 2-y 8,
      -y 3-y 4-y 5,-y 6-y 7-y 8,y 3,y 4,y 5,y 6,y 7,y 8] i

def project (x : State) : Fin 9 → ℝ :=
  ![x 1+x 2+x 3+x 7+x 8+x 9+x 10+x 11,
    x 2+x 3+x 8+x 10+x 11,x 3+x 11,x 6,x 7,x 8,x 9,x 10,x 11]

theorem chart_totals (y : Fin 9 → ℝ) :
    totalE (chart y) = totalE witnessState ∧
    totalF (chart y) = totalF witnessState ∧
    totalS (chart y) = totalS witnessState := by
  simp [totalE,totalF,totalS,chart]
  constructor
  · ring
  constructor <;> ring

theorem chart_project (y : Fin 9 → ℝ) :
    project (chart y) - project witnessState = y := by
  funext i; fin_cases i <;> simp [project,chart] <;> ring

theorem chart_covers_class (x : State)
    (he : totalE x = totalE witnessState)
    (hf : totalF x = totalF witnessState)
    (hs : totalS x = totalS witnessState) :
    chart (project x - project witnessState) = x := by
  simp only [totalE,totalF,totalS] at he hf hs
  funext i; fin_cases i <;> simp [chart,project] <;> linarith

def reducedField (r : ℝ) (y : Fin 9 → ℝ) : Fin 9 → ℝ :=
  project (field (witnessRates r) (chart y))

theorem reduced_equilibrium (r : ℝ) : reducedField r 0 = 0 := by
  have h : chart 0 = witnessState := by ext i; fin_cases i <;> simp [chart]
  simp [reducedField,h,witness_equilibrium,project]

theorem field_smooth : ContDiff ℝ ⊤ (fun p : ℝ × (Fin 9 → ℝ) => reducedField p.1 p.2) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [reducedField,project,field,balance,flux,witnessRates,chart,witnessState] <;> fun_prop

end
end ThreeSitePhosphorylation
