import proofs.ThreeSitePhosphorylation.GenericClosedPaths
import proofs.ThreeSitePhosphorylation.GenericQuadraticTensor

namespace ThreeSitePhosphorylation.GenericQuadraticClosedPaths
noncomputable section
open GenericComplexification GenericPeriodicKernel

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq σ]

/-- Literal finite quadratic tensors supply the smooth field and path lift.
Only actual spectral/crossing data and smooth tensor coefficients remain as
inputs. Curvature, physical periodic extension and attraction are separate. -/
theorem closed_path_family_exists (A0 D : Matrix ι ι ℝ)
    (H : ℝ → GenericQuadraticTensor.Tensor ι)
    (hH : ∀ i j k, ContDiff ℝ ⊤ (fun r => H r i j k))
    (r w : ℝ) (hw : 0<w) (roots : σ → ℝ) (hn : ∀ i, roots i<0)
    (basis : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ))
    (heigen : ∀ i, (complexMatrix (A0+r • D)).mulVec (basis i)=
      spectralValues roots w i • basis i)
    (hcross : (basis.coord (Sum.inr 0)
      ((complexMatrix D).mulVec (basis (Sum.inr 0)))).re<0) :
    Nonempty (GenericClosedPaths.ClosedPathFamily A0 D
      (GenericQuadraticTensor.pathField H) r w (basis (Sum.inr 0))) :=
  GenericClosedPaths.closed_path_family_exists A0 D
    (GenericQuadraticTensor.field H) (GenericQuadraticTensor.pathField H)
    (GenericQuadraticTensor.field_smooth H hH)
    (GenericQuadraticTensor.pathField_smooth H hH)
    (GenericQuadraticTensor.pathField_apply H)
    r w hw roots hn basis heigen hcross

end
end ThreeSitePhosphorylation.GenericQuadraticClosedPaths
