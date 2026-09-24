import proofs.ThreeSitePhosphorylation.GenericQuadraticTensor
import proofs.ThreeSitePhosphorylation.GenericComplexification

namespace ThreeSitePhosphorylation.GenericTensorBilinear
noncomputable section
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coefficient tensor defines a bilinear map by literal finite sums. -/
def tensorBilinear {𝕜 : Type*} [CommSemiring 𝕜] (H : ι → ι → ι → 𝕜) :
    (ι → 𝕜) →ₗ[𝕜] (ι → 𝕜) →ₗ[𝕜] (ι → 𝕜) where
  toFun x :=
    { toFun := fun y i => ∑ j, ∑ k, H i j k*x j*y k
      map_add' := by
        intro y z
        ext i
        simp [mul_add,Finset.sum_add_distrib]
      map_smul' := by
        intro c y
        ext i
        simp [Finset.mul_sum,mul_left_comm,mul_comm] }
  map_add' := by
    intro x y
    ext z i
    simp [add_mul,mul_add,Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    ext y i
    simp [Finset.mul_sum,mul_left_comm,mul_comm]

@[simp] theorem tensorBilinear_apply {𝕜 : Type*} [CommSemiring 𝕜]
    (H : ι → ι → ι → 𝕜) (x y : ι → 𝕜) (i : ι) :
    tensorBilinear H x y i=∑ j, ∑ k, H i j k*x j*y k := rfl

def realBilinear (H : GenericQuadraticTensor.Tensor ι) :
    (ι → ℝ) →ₗ[ℝ] (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := tensorBilinear H

def complexBilinear (H : GenericQuadraticTensor.Tensor ι) :
    (ι → ℂ) →ₗ[ℂ] (ι → ℂ) →ₗ[ℂ] (ι → ℂ) :=
  tensorBilinear (fun i j k => (H i j k:ℂ))

/-- The literal polynomial field has exactly the one-half Hessian convention. -/
theorem field_eq_half_bilinear (H : ℝ → GenericQuadraticTensor.Tensor ι)
    (r : ℝ) (x : ι → ℝ) :
    GenericQuadraticTensor.field H r x=(1/2:ℝ) • realBilinear (H r) x x := by
  ext i
  have hf : GenericQuadraticTensor.field H r x i=
      ∑ j, ∑ k, (H r i j k/2)*(x j*x k) := by
    simp [GenericQuadraticTensor.field,GenericPolynomialFlow.field,
      GenericQuadraticTensor.direction,GenericQuadraticTensor.coefficient,
      GenericQuadraticTensor.firstCoordinate,GenericQuadraticTensor.secondCoordinate,
      Fintype.sum_prod_type,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      Pi.single_apply,mul_ite]
  rw [hf]
  change _=(1/2:ℝ)*(∑ j, ∑ k, H r i j k*x j*x k)
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem complexify_realBilinear (H : GenericQuadraticTensor.Tensor ι)
    (x y : ι → ℝ) :
    GenericComplexification.complexify (realBilinear H x y)=
      complexBilinear H (GenericComplexification.complexify x)
        (GenericComplexification.complexify y) := by
  ext i
  simp [realBilinear,complexBilinear,GenericComplexification.complexify_apply]

theorem tensorBilinear_symmetric {𝕜 : Type*} [CommSemiring 𝕜]
    (H : ι → ι → ι → 𝕜) (hH : ∀ i j k, H i j k=H i k j)
    (x y : ι → 𝕜) : tensorBilinear H x y=tensorBilinear H y x := by
  ext i
  simp only [tensorBilinear_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [hH i k j]
  ring

theorem realBilinear_symmetric (H : GenericQuadraticTensor.Tensor ι)
    (hH : ∀ i j k, H i j k=H i k j) (x y : ι → ℝ) :
    realBilinear H x y=realBilinear H y x := tensorBilinear_symmetric H hH x y

theorem complexBilinear_symmetric (H : GenericQuadraticTensor.Tensor ι)
    (hH : ∀ i j k, H i j k=H i k j) (x y : ι → ℂ) :
    complexBilinear H x y=complexBilinear H y x :=
  tensorBilinear_symmetric _ (fun i j k => congrArg (fun a : ℝ => (a:ℂ)) (hH i j k)) x y

end
end ThreeSitePhosphorylation.GenericTensorBilinear
