import proofs.ThreeSitePhosphorylation.Source

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 1500000

abbrev ReducedState := Fin 9 → ℝ
def coordinate (i : Fin 9) : ReducedState →L[ℝ] ℝ := ContinuousLinearMap.proj i
def speciesVariation : Fin 12 → ReducedState →L[ℝ] ℝ :=
  ![-coordinate 0-coordinate 3,
    coordinate 0-coordinate 1-coordinate 4-coordinate 6,
    coordinate 1-coordinate 2-coordinate 5-coordinate 7,coordinate 2-coordinate 8,
    -coordinate 3-coordinate 4-coordinate 5,-coordinate 6-coordinate 7-coordinate 8,
    coordinate 3,coordinate 4,coordinate 5,coordinate 6,coordinate 7,coordinate 8]

def inputSpecies : Fin 6 → Fin 12 := ![0,1,2,1,2,3]
def enzymeSpecies : Fin 6 → Fin 12 := ![4,4,4,5,5,5]
def boundCoordinate : Fin 6 → Fin 9 := ![3,4,5,6,7,8]
def bindingRates (r : ℝ) : Fin 6 → ℝ :=
  ![101/99000,101/550,1010/627,(1+r)/130,3939/95,101/9]
def exitRates (r : ℝ) : Fin 6 → ℝ :=
  ![101/520,3939/14,101/78,(1+r)/93,1313/25,101/250]

def complexLinear (r : ℝ) (j : Fin 6) : ReducedState →L[ℝ] ℝ :=
  (bindingRates r j*witnessState (enzymeSpecies j)) • speciesVariation (inputSpecies j) +
  (bindingRates r j*witnessState (inputSpecies j)) • speciesVariation (enzymeSpecies j) -
  exitRates r j • coordinate (boundCoordinate j)

def jacobianRows (r : ℝ) : Fin 9 → ReducedState →L[ℝ] ℝ :=
  ![(5/26:ℝ) • coordinate 3-(1/93:ℝ) • coordinate 6,
    (1950/7:ℝ) • coordinate 4-(52:ℝ) • coordinate 7,
    (50/39:ℝ) • coordinate 5-(2/5:ℝ) • coordinate 8,
    complexLinear r 0,complexLinear r 1,complexLinear r 2,
    complexLinear r 3,complexLinear r 4,complexLinear r 5]

def jacobianOperator (r : ℝ) : ReducedState →L[ℝ] ReducedState :=
  ContinuousLinearMap.pi (jacobianRows r)

def complexQuadratic (r : ℝ) (j : Fin 6) (y : ReducedState) : ℝ :=
  bindingRates r j * speciesVariation (inputSpecies j) y * speciesVariation (enzymeSpecies j) y

def quadraticField (r : ℝ) (y : ReducedState) : ReducedState :=
  ![0,0,0,complexQuadratic r 0 y,complexQuadratic r 1 y,complexQuadratic r 2 y,
    complexQuadratic r 3 y,complexQuadratic r 4 y,complexQuadratic r 5 y]

theorem source_taylor_exact (r : ℝ) (y : ReducedState) :
    reducedField r y = jacobianOperator r y + quadraticField r y := by
  ext i
  fin_cases i <;>
    simp [reducedField,project,field,balance,flux,witnessRates,chart,witnessState,
      jacobianOperator,jacobianRows,complexLinear,quadraticField,complexQuadratic,
      speciesVariation,coordinate,inputSpecies,enzymeSpecies,boundCoordinate,bindingRates,exitRates] <;> ring

theorem complexQuadratic_derivative_zero (r : ℝ) (j : Fin 6) :
    HasFDerivAt (𝕜 := ℝ) (complexQuadratic r j) 0 (0 : ReducedState) := by
  have hs := (speciesVariation (inputSpecies j)).hasFDerivAt (x := (0 : ReducedState))
  have he := (speciesVariation (enzymeSpecies j)).hasFDerivAt (x := (0 : ReducedState))
  have h := (hs.const_mul (bindingRates r j)).mul he
  simpa [complexQuadratic] using h

theorem quadratic_derivative_zero (r : ℝ) :
    HasFDerivAt (𝕜 := ℝ) (quadraticField r) 0 (0 : ReducedState) := by
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i <;> simp [quadraticField]
  all_goals first | fun_prop | exact complexQuadratic_derivative_zero r _

theorem source_jacobian (r : ℝ) :
    HasFDerivAt (reducedField r) (jacobianOperator r) (0 : ReducedState) := by
  have h := (jacobianOperator r).hasFDerivAt.add (quadratic_derivative_zero r)
  have he : (⇑(jacobianOperator r) + quadraticField r) = reducedField r := by
    funext y
    exact (source_taylor_exact r y).symm
  simpa only [add_zero,he] using h

end
end ThreeSitePhosphorylation
