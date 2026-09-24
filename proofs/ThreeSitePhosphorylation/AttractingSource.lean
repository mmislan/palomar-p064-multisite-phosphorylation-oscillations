import proofs.ThreeSitePhosphorylation.Jacobian

/-! The distinct witness A of P064, using the same literal eighteen reactions.
These are source and derivative lemmas, not a theorem of orbital attraction.
The older `three_site_hopf_capacity` concerns a different witness. -/
namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section
set_option maxHeartbeats 1500000

def state : State :=
  ![2,12,1/5,2/5,23/10,2/5,23/50,3/10,17/10,23,9/50,4]

def rates (r : ℝ) : Rates :=
  ![101/4600,1/460,5/23,404/1725,16/75,64/3,
    303/115,3/425,12/17,(1+r)/48,r/230,1/230,
    404/5,16/45,320/9,303/40,3/1000,3/10]

theorem state_positive : ∀ i, 0 < state i := by
  intro i; fin_cases i <;> norm_num [state]

theorem rates_positive (r : ℝ) (hr : 0 < r) : ∀ i, 0 < rates r i := by
  intro i; fin_cases i <;> simp [rates] <;> positivity

theorem equilibrium_flux (r : ℝ) : flux (rates r) state =
    ![101/1000,1/1000,1/10,808/125,8/125,32/5,303/250,3/250,6/5,
      (1+r)/10,r/10,1/10,808/125,8/125,32/5,303/250,3/250,6/5] := by
  ext i
  fin_cases i <;> simp [flux,rates,state] <;> ring

theorem equilibrium (r : ℝ) : field (rates r) state = 0 := by
  unfold field
  rw [equilibrium_flux]
  ext i
  fin_cases i <;> simp [balance] <;> ring

theorem totals : totalE state = 119/25 ∧ totalF state = 1379/50 ∧
    totalS state = 1106/25 := by
  change (23/10:ℝ)+23/50+3/10+17/10 = 119/25 ∧
    (2/5:ℝ)+23+9/50+4 = 1379/50 ∧
    (2:ℝ)+12+1/5+2/5+23/50+3/10+17/10+23+9/50+4 = 1106/25
  norm_num

/-- The existing linear species chart, recentered at witness A. -/
def affineChart (y : ReducedState) : State :=
  fun i => state i + speciesVariation i y

theorem affineChart_zero : affineChart 0 = state := by
  ext i
  simp [affineChart]

theorem affineChart_totals (y : ReducedState) :
    totalE (affineChart y) = totalE state ∧
    totalF (affineChart y) = totalF state ∧
    totalS (affineChart y) = totalS state := by
  simp [totalE,totalF,totalS,affineChart,speciesVariation,coordinate]
  constructor
  · ring
  constructor <;> ring

theorem affineChart_project (y : ReducedState) :
    project (affineChart y) - project state = y := by
  ext i
  fin_cases i <;> simp [project,affineChart,speciesVariation,coordinate] <;> ring

theorem affineChart_covers_class (x : State)
    (he : totalE x = totalE state) (hf : totalF x = totalF state)
    (hs : totalS x = totalS state) :
    affineChart (project x - project state) = x := by
  simp only [totalE,totalF,totalS] at he hf hs
  ext i
  fin_cases i <;> simp [affineChart,project,speciesVariation,coordinate] <;> linarith

def reduced (r : ℝ) (y : ReducedState) : ReducedState :=
  project (field (rates r) (affineChart y))

theorem reduced_equilibrium (r : ℝ) : reduced r 0 = 0 := by
  simp [reduced,affineChart_zero,equilibrium,project]

def binding (r : ℝ) : Fin 6 → ℝ :=
  ![101/4600,404/1725,303/115,(1+r)/48,404/5,303/40]

def exitRate (r : ℝ) : Fin 6 → ℝ :=
  ![101/460,1616/75,303/425,(1+r)/230,1616/45,303/1000]

def complexRow (r : ℝ) (j : Fin 6) : ReducedState →L[ℝ] ℝ :=
  (binding r j * state (enzymeSpecies j)) • speciesVariation (inputSpecies j) +
  (binding r j * state (inputSpecies j)) • speciesVariation (enzymeSpecies j) -
  exitRate r j • coordinate (boundCoordinate j)

def linearRows (r : ℝ) : Fin 9 → ReducedState →L[ℝ] ℝ :=
  ![(5/23:ℝ) • coordinate 3-(1/230:ℝ) • coordinate 6,
    (64/3:ℝ) • coordinate 4-(320/9:ℝ) • coordinate 7,
    (12/17:ℝ) • coordinate 5-(3/10:ℝ) • coordinate 8,
    complexRow r 0,complexRow r 1,complexRow r 2,
    complexRow r 3,complexRow r 4,complexRow r 5]

def linearPart (r : ℝ) : ReducedState →L[ℝ] ReducedState :=
  ContinuousLinearMap.pi (linearRows r)

def quadraticRow (r : ℝ) (j : Fin 6) (y : ReducedState) : ℝ :=
  binding r j * speciesVariation (inputSpecies j) y * speciesVariation (enzymeSpecies j) y

def quadraticPart (r : ℝ) (y : ReducedState) : ReducedState :=
  ![0,0,0,quadraticRow r 0 y,quadraticRow r 1 y,quadraticRow r 2 y,
    quadraticRow r 3 y,quadraticRow r 4 y,quadraticRow r 5 y]

theorem taylor_exact (r : ℝ) (y : ReducedState) :
    reduced r y = linearPart r y + quadraticPart r y := by
  ext i
  fin_cases i <;>
    simp [reduced,project,field,balance,flux,rates,affineChart,state,
      linearPart,linearRows,complexRow,quadraticPart,quadraticRow,
      speciesVariation,coordinate,inputSpecies,enzymeSpecies,boundCoordinate,binding,exitRate] <;> ring

theorem quadraticRow_derivative_zero (r : ℝ) (j : Fin 6) :
    HasFDerivAt (𝕜 := ℝ) (quadraticRow r j) 0 (0 : ReducedState) := by
  have hs := (speciesVariation (inputSpecies j)).hasFDerivAt (x := (0 : ReducedState))
  have he := (speciesVariation (enzymeSpecies j)).hasFDerivAt (x := (0 : ReducedState))
  have h := (hs.const_mul (binding r j)).mul he
  simpa [quadraticRow] using h

theorem quadraticPart_derivative_zero (r : ℝ) :
    HasFDerivAt (𝕜 := ℝ) (quadraticPart r) 0 (0 : ReducedState) := by
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i <;> simp [quadraticPart]
  all_goals first | fun_prop | exact quadraticRow_derivative_zero r _

theorem source_jacobian (r : ℝ) :
    HasFDerivAt (reduced r) (linearPart r) (0 : ReducedState) := by
  have h := (linearPart r).hasFDerivAt.add (quadraticPart_derivative_zero r)
  have he : (⇑(linearPart r) + quadraticPart r) = reduced r := by
    funext y
    exact (taylor_exact r y).symm
  simpa only [add_zero,he] using h

theorem smooth : ContDiff ℝ ⊤ (fun p : ℝ × ReducedState => reduced p.1 p.2) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;>
    simp [reduced,project,field,balance,flux,rates,affineChart,state,
      speciesVariation,coordinate] <;> fun_prop

end
end ThreeSitePhosphorylation.AttractingWitness
