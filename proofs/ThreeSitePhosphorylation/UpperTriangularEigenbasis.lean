import Mathlib

/-! Explicit eigenbasis of a coupled upper-triangular block. The Sylvester
equation is solved by finite basis coordinates, not assumed as a hypothesis. -/
namespace ThreeSitePhosphorylation.UpperTriangularEigenbasis
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 500000

variable {E F ι ν : Type*}
  [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
  [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]

def block (A : E →ₗ[ℂ] E) (U : F →ₗ[ℂ] E) (K : F →ₗ[ℂ] F) :
    (E × F) →ₗ[ℂ] (E × F) where
  toFun z := (A z.1+U z.2,K z.2)
  map_add' x y := by simp; abel
  map_smul' a z := by simp [smul_add]

omit [Fintype ι] in
theorem coordinate_eigen (A : E →ₗ[ℂ] E) (b : Module.Basis ι ℂ E)
    (parentEig : ι → ℂ) (hA : ∀ i, A (b i)=parentEig i • b i) (i : ι) (x : E) :
    b.coord i (A x)=parentEig i*b.coord i x := by
  have h : (b.coord i).comp A=parentEig i • b.coord i := by
    apply b.ext
    intro j
    by_cases hij : i=j
    · subst j
      simp [hA,Module.Basis.coord_apply]
    · simp [hA,Module.Basis.coord_apply,hij]
  exact DFunLike.congr_fun h x

/-- Explicit solution of (mu*id-A)x=U(cj) by the parent eigenbasis. -/
def newUpper (U : F →ₗ[ℂ] E) (b : Module.Basis ι ℂ E)
    (c : Module.Basis ν ℂ F) (parentEig : ι → ℂ) (μ : ν → ℂ) (j : ν) : E :=
  ∑ i, (b.coord i (U (c j))/(μ j-parentEig i)) • b i

omit [Fintype ν] [DecidableEq ν] in
theorem newUpper_coordinate (U : F →ₗ[ℂ] E) (b : Module.Basis ι ℂ E)
    (c : Module.Basis ν ℂ F) (parentEig : ι → ℂ) (μ : ν → ℂ) (j : ν) (i : ι) :
    b.coord i (newUpper U b c parentEig μ j)=b.coord i (U (c j))/(μ j-parentEig i) := by
  simp [newUpper,Module.Basis.coord_apply,Finsupp.single_apply]

omit [Fintype ν] [DecidableEq ν] in
theorem newUpper_equation (A : E →ₗ[ℂ] E) (U : F →ₗ[ℂ] E)
    (b : Module.Basis ι ℂ E) (c : Module.Basis ν ℂ F) (parentEig : ι → ℂ) (μ : ν → ℂ)
    (hA : ∀ i, A (b i)=parentEig i • b i) (hsep : ∀ i j, μ j ≠ parentEig i) (j : ν) :
    A (newUpper U b c parentEig μ j)+U (c j)=μ j • newUpper U b c parentEig μ j := by
  apply b.repr.injective
  ext i
  change b.coord i (A (newUpper U b c parentEig μ j)+U (c j))=
    b.coord i (μ j • newUpper U b c parentEig μ j)
  rw [map_add,map_smul,coordinate_eigen A b parentEig hA,newUpper_coordinate]
  simp only [smul_eq_mul]
  field_simp [sub_ne_zero.mpr (hsep i j)]; ring

def sylvesterMap (U : F →ₗ[ℂ] E) (b : Module.Basis ι ℂ E)
    (c : Module.Basis ν ℂ F) (parentEig : ι → ℂ) (μ : ν → ℂ) : F →ₗ[ℂ] E :=
  c.constr ℂ (newUpper U b c parentEig μ)

omit [DecidableEq ι] [Fintype ν] [DecidableEq ν] in
theorem sylvesterMap_basis (U : F →ₗ[ℂ] E) (b : Module.Basis ι ℂ E)
    (c : Module.Basis ν ℂ F) (parentEig : ι → ℂ) (μ : ν → ℂ) (j : ν) :
    sylvesterMap U b c parentEig μ (c j)=newUpper U b c parentEig μ j :=
  c.constr_basis ℂ _ j

omit [Fintype ν] [DecidableEq ν] in
theorem sylvester_equation (A : E →ₗ[ℂ] E) (U : F →ₗ[ℂ] E) (K : F →ₗ[ℂ] F)
    (b : Module.Basis ι ℂ E) (c : Module.Basis ν ℂ F) (parentEig : ι → ℂ) (μ : ν → ℂ)
    (hA : ∀ i, A (b i)=parentEig i • b i) (hK : ∀ j, K (c j)=μ j • c j)
    (hsep : ∀ i j, μ j ≠ parentEig i) :
    A.comp (sylvesterMap U b c parentEig μ)+U=(sylvesterMap U b c parentEig μ).comp K := by
  apply c.ext
  intro j
  change A (sylvesterMap U b c parentEig μ (c j))+U (c j)=sylvesterMap U b c parentEig μ (K (c j))
  rw [hK,map_smul,sylvesterMap_basis]
  exact newUpper_equation A U b c parentEig μ hA hsep j

def shear (L : F →ₗ[ℂ] E) : (E × F) ≃ₗ[ℂ] (E × F) where
  toFun z := (z.1+L z.2,z.2)
  invFun z := (z.1-L z.2,z.2)
  left_inv z := by simp
  right_inv z := by simp
  map_add' x y := by simp; abel
  map_smul' a z := by simp [smul_add]

def coupledBasis (U : F →ₗ[ℂ] E) (b : Module.Basis ι ℂ E)
    (c : Module.Basis ν ℂ F) (parentEig : ι → ℂ) (μ : ν → ℂ) :
    Module.Basis (ι ⊕ ν) ℂ (E × F) :=
  (b.prod c).map (shear (sylvesterMap U b c parentEig μ))

omit [DecidableEq ι] [Fintype ν] [DecidableEq ν] in
theorem coupledBasis_old (U : F →ₗ[ℂ] E) (b : Module.Basis ι ℂ E)
    (c : Module.Basis ν ℂ F) (parentEig : ι → ℂ) (μ : ν → ℂ) (i : ι) :
    coupledBasis U b c parentEig μ (Sum.inl i)=(b i,0) := by
  simp [coupledBasis,Module.Basis.prod_apply,shear]

omit [DecidableEq ι] [Fintype ν] [DecidableEq ν] in
theorem coupledBasis_new (U : F →ₗ[ℂ] E) (b : Module.Basis ι ℂ E)
    (c : Module.Basis ν ℂ F) (parentEig : ι → ℂ) (μ : ν → ℂ) (j : ν) :
    coupledBasis U b c parentEig μ (Sum.inr j)=(newUpper U b c parentEig μ j,c j) := by
  simp [coupledBasis,Module.Basis.prod_apply,shear,sylvesterMap_basis]

omit [Fintype ν] [DecidableEq ν] in
/-- The basis is complete by an explicit invertible shear, and every column
is an eigenvector of the actual coupled block. Neither U=0 nor Sylvester
solvability is supplied as an input. -/
theorem coupledBasis_eigen (A : E →ₗ[ℂ] E) (U : F →ₗ[ℂ] E) (K : F →ₗ[ℂ] F)
    (b : Module.Basis ι ℂ E) (c : Module.Basis ν ℂ F) (parentEig : ι → ℂ) (μ : ν → ℂ)
    (hA : ∀ i, A (b i)=parentEig i • b i) (hK : ∀ j, K (c j)=μ j • c j)
    (hsep : ∀ i j, μ j ≠ parentEig i) (j : ι ⊕ ν) :
    block A U K (coupledBasis U b c parentEig μ j)=
      Sum.elim parentEig μ j • coupledBasis U b c parentEig μ j := by
  cases j with
  | inl i => simp [coupledBasis_old,block,hA]
  | inr j =>
    rw [coupledBasis_new]
    apply Prod.ext
    · exact newUpper_equation A U b c parentEig μ hA hsep j
    · exact hK j

end
end ThreeSitePhosphorylation.UpperTriangularEigenbasis
