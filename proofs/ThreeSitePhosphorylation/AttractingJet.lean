import proofs.ThreeSitePhosphorylation.AttractingSource

namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section
set_option maxHeartbeats 600000

/-- The actual second-order coefficient of the reduced mass-action source. -/
def hessianRow (r : ℝ) (j : Fin 6) (x : ReducedState) : ReducedState →L[ℝ] ℝ :=
  (binding r j * speciesVariation (inputSpecies j) x) • speciesVariation (enzymeSpecies j) +
  (binding r j * speciesVariation (enzymeSpecies j) x) • speciesVariation (inputSpecies j)

def hessian (r : ℝ) (x : ReducedState) : ReducedState →L[ℝ] ReducedState :=
  ContinuousLinearMap.pi ![0,0,0,hessianRow r 0 x,hessianRow r 1 x,
    hessianRow r 2 x,hessianRow r 3 x,hessianRow r 4 x,hessianRow r 5 x]

theorem quadraticPart_derivative (r : ℝ) (x : ReducedState) :
    HasFDerivAt (quadraticPart r) (hessian r x) x := by
  have hj (j : Fin 6) : HasFDerivAt (quadraticRow r j) (hessianRow r j x) x := by
    have hs := (speciesVariation (inputSpecies j)).hasFDerivAt (x := x)
    have he := (speciesVariation (enzymeSpecies j)).hasFDerivAt (x := x)
    convert (hs.const_mul (binding r j)).mul he using 1
    ext y
    simp [hessianRow]
    ring
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i <;> simp [quadraticPart,hessian]
  all_goals fun_prop

theorem reduced_derivative (r : ℝ) (x : ReducedState) :
    HasFDerivAt (reduced r) (linearPart r + hessian r x) x := by
  have h := (linearPart r).hasFDerivAt.add (quadraticPart_derivative r x)
  have he : (⇑(linearPart r) + quadraticPart r) = reduced r := by
    funext y
    exact (taylor_exact r y).symm
  rwa [he] at h

theorem reduced_fderiv (r : ℝ) (x : ReducedState) :
    fderiv ℝ (reduced r) x = linearPart r + hessian r x :=
  (reduced_derivative r x).fderiv

theorem hessian_symmetric (r : ℝ) (x y : ReducedState) :
    hessian r x y = hessian r y x := by
  ext i
  fin_cases i <;> simp [hessian,hessianRow] <;> ring

theorem hessian_smul (r a : ℝ) (x : ReducedState) :
    hessian r (a • x) = a • hessian r x := by
  ext y i
  fin_cases i <;> simp [hessian,hessianRow] <;> ring

theorem hessian_diagonal (r : ℝ) (x : ReducedState) :
    hessian r x x = (2 : ℝ) • quadraticPart r x := by
  ext i
  fin_cases i <;> simp [hessian,hessianRow,quadraticPart,quadraticRow] <;> ring

theorem source_second_directional_derivative (r : ℝ) (u v : ReducedState) :
    HasDerivAt (fun t : ℝ => fderiv ℝ (reduced r) (t • u) v)
      (hessian r u v) 0 := by
  simp only [reduced_fderiv,hessian_smul,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply]
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (hessian r u v)).const_add (linearPart r v)

/-- Complexification of the same fixed compatibility-class chart. -/
def complexSpecies (x : Fin 9 → ℂ) : Fin 12 → ℂ :=
  ![-x 0-x 3,x 0-x 1-x 4-x 6,x 1-x 2-x 5-x 7,x 2-x 8,
    -x 3-x 4-x 5,-x 6-x 7-x 8,x 3,x 4,x 5,x 6,x 7,x 8]

def complexHessianRow (r : ℝ) (j : Fin 6) (x y : Fin 9 → ℂ) : ℂ :=
  (binding r j : ℂ) * (complexSpecies x (inputSpecies j) * complexSpecies y (enzymeSpecies j) +
    complexSpecies y (inputSpecies j) * complexSpecies x (enzymeSpecies j))

def complexHessian (r : ℝ) (x y : Fin 9 → ℂ) : Fin 9 → ℂ :=
  ![0,0,0,complexHessianRow r 0 x y,complexHessianRow r 1 x y,
    complexHessianRow r 2 x y,complexHessianRow r 3 x y,
    complexHessianRow r 4 x y,complexHessianRow r 5 x y]

theorem complexSpecies_ofReal (x : ReducedState) (j : Fin 12) :
    complexSpecies (fun i => (x i : ℂ)) j = (speciesVariation j x : ℂ) := by
  fin_cases j <;> simp [complexSpecies,speciesVariation,coordinate]

theorem complexHessian_ofReal (r : ℝ) (x y : ReducedState) :
    complexHessian r (fun i => (x i : ℂ)) (fun i => (y i : ℂ)) =
      fun i => (hessian r x y i : ℂ) := by
  ext i
  fin_cases i <;>
    simp [complexHessian,complexHessianRow,complexSpecies_ofReal,hessian,hessianRow] <;> ring

end
end ThreeSitePhosphorylation.AttractingWitness
