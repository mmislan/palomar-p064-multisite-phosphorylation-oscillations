import proofs.ThreeSitePhosphorylation.AttractingJet

namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section

theorem complexSpecies_add (x y : Fin 9 → ℂ) :
    complexSpecies (x+y) = complexSpecies x + complexSpecies y := by
  ext j
  fin_cases j <;> simp [complexSpecies] <;> ring

theorem complexSpecies_smul (c : ℂ) (x : Fin 9 → ℂ) :
    complexSpecies (c • x) = c • complexSpecies x := by
  ext j
  fin_cases j <;> simp [complexSpecies] <;> ring

theorem complexHessian_symmetric (r : ℝ) (x y : Fin 9 → ℂ) :
    complexHessian r x y = complexHessian r y x := by
  ext i
  fin_cases i <;> simp [complexHessian,complexHessianRow,add_comm]

theorem complexHessian_add_left (r : ℝ) (x y z : Fin 9 → ℂ) :
    complexHessian r (x+y) z = complexHessian r x z + complexHessian r y z := by
  ext i
  fin_cases i <;>
    simp [complexHessian,complexHessianRow,complexSpecies_add] <;> ring

theorem complexHessian_add_right (r : ℝ) (x y z : Fin 9 → ℂ) :
    complexHessian r x (y+z) = complexHessian r x y + complexHessian r x z := by
  rw [complexHessian_symmetric r x (y+z),complexHessian_add_left,
    complexHessian_symmetric r y x,complexHessian_symmetric r z x]

theorem complexHessian_smul_left (r : ℝ) (c : ℂ) (x y : Fin 9 → ℂ) :
    complexHessian r (c • x) y = c • complexHessian r x y := by
  ext i
  fin_cases i <;>
    simp [complexHessian,complexHessianRow,complexSpecies_smul] <;> ring

theorem complexHessian_smul_right (r : ℝ) (c : ℂ) (x y : Fin 9 → ℂ) :
    complexHessian r x (c • y) = c • complexHessian r x y := by
  rw [complexHessian_symmetric r x (c • y),complexHessian_smul_left,
    complexHessian_symmetric r y x]

/-- The literal complexified source Hessian packaged as a bilinear map. -/
def complexHessianBilinear (r : ℝ) :
    (Fin 9 → ℂ) →ₗ[ℂ] (Fin 9 → ℂ) →ₗ[ℂ] (Fin 9 → ℂ) where
  toFun x :=
    { toFun := complexHessian r x
      map_add' := complexHessian_add_right r x
      map_smul' := fun c y => complexHessian_smul_right r c x y }
  map_add' x y := by apply LinearMap.ext; intro z; exact complexHessian_add_left r x y z
  map_smul' c x := by apply LinearMap.ext; intro y; exact complexHessian_smul_left r c x y

@[simp] theorem complexHessianBilinear_apply (r : ℝ) (x y : Fin 9 → ℂ) :
    complexHessianBilinear r x y = complexHessian r x y := rfl

end
end ThreeSitePhosphorylation.AttractingWitness
