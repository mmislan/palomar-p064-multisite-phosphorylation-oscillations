import proofs.ThreeSitePhosphorylation.GenericQuadraticTensor
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace ThreeSitePhosphorylation.GenericQuadraticDynamics
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def field (A0 D : Matrix ι ι ℝ) (H : ℝ → GenericQuadraticTensor.Tensor ι)
    (r : ℝ) (x : ι → ℝ) : ι → ℝ :=
  (A0+r • D).mulVec x+GenericQuadraticTensor.field H r x

def rescaledField (A0 D : Matrix ι ι ℝ) (H : ℝ → GenericQuadraticTensor.Tensor ι)
    (a r : ℝ) (x : ι → ℝ) : ι → ℝ :=
  (A0+r • D).mulVec x+a • GenericQuadraticTensor.field H r x

/-- Exact amplitude rescaling for the literal quadratic source. -/
theorem field_scaling (A0 D : Matrix ι ι ℝ) (H : ℝ → GenericQuadraticTensor.Tensor ι)
    (a r : ℝ) (x : ι → ℝ) :
    field A0 D H r (a • x)=a • rescaledField A0 D H a r x := by
  simp only [field,rescaledField,Matrix.mulVec_smul,GenericQuadraticTensor.field_smul,
    smul_add,smul_smul,pow_two]

theorem field_zero (A0 D : Matrix ι ι ℝ) (H : ℝ → GenericQuadraticTensor.Tensor ι)
    (r : ℝ) : field A0 D H r 0=0 := by
  simp [field,GenericQuadraticTensor.field_zero]

theorem scaled_curve_derivative (A0 D : Matrix ι ι ℝ)
    (H : ℝ → GenericQuadraticTensor.Tensor ι) (a r t : ℝ) (u : ℝ → ι → ℝ)
    (hu : HasDerivAt u (rescaledField A0 D H a r (u t)) t) :
    HasDerivAt (fun s => a • u s) (field A0 D H r (a • u t)) t := by
  rw [field_scaling]
  exact hu.const_smul a

end
end ThreeSitePhosphorylation.GenericQuadraticDynamics
