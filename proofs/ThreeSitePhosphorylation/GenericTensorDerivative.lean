import proofs.ThreeSitePhosphorylation.GenericTensorBilinear
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

namespace ThreeSitePhosphorylation.GenericTensorDerivative
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The literal finite coefficient sum, bundled continuously in both arguments. -/
def realContinuousBilinear (H : GenericQuadraticTensor.Tensor ι) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  (GenericTensorBilinear.realBilinear H).toContinuousBilinearMap

@[simp] theorem realContinuousBilinear_apply (H : GenericQuadraticTensor.Tensor ι)
    (x y : ι → ℝ) :
    realContinuousBilinear H x y = GenericTensorBilinear.realBilinear H x y := rfl

/-- Symmetry is an input on the actual tensor, not on a presumed derivative. -/
theorem field_hasFDerivAt (H : ℝ → GenericQuadraticTensor.Tensor ι) (r : ℝ)
    (hH : ∀ i j k, H r i j k = H r i k j) (x : ι → ℝ) :
    HasFDerivAt (GenericQuadraticTensor.field H r)
      (realContinuousBilinear (H r) x) x := by
  let B := realContinuousBilinear (H r)
  have hid := hasFDerivAt_id (𝕜 := ℝ) x
  have hb := (B.hasFDerivAt_of_bilinear hid hid).const_smul (1 / 2 : ℝ)
  have hs (y : ι → ℝ) : B y x = B x y :=
    GenericTensorBilinear.realBilinear_symmetric (H r) hH y x
  have he : (1 / 2 : ℝ) •
      (B.precompR (ι → ℝ) x (ContinuousLinearMap.id ℝ (ι → ℝ)) +
        B.precompL (ι → ℝ) (ContinuousLinearMap.id ℝ (ι → ℝ)) x) = B x := by
    ext y i
    change (1 / 2 : ℝ) * (B x y i + B y x i) = B x y i
    rw [hs y]
    ring
  have hf : GenericQuadraticTensor.field H r =
      (fun y => (1 / 2 : ℝ) • B y y) := by
    funext y
    exact GenericTensorBilinear.field_eq_half_bilinear H r y
  rw [hf]
  simp only [id_eq] at hb
  rw [he] at hb
  exact hb

theorem field_fderiv (H : ℝ → GenericQuadraticTensor.Tensor ι) (r : ℝ)
    (hH : ∀ i j k, H r i j k = H r i k j) (x : ι → ℝ) :
    fderiv ℝ (GenericQuadraticTensor.field H r) x =
      realContinuousBilinear (H r) x :=
  (field_hasFDerivAt H r hH x).fderiv

/-- The derivative of the actual first derivative is the constant tensor map. -/
theorem field_fderiv_hasFDerivAt (H : ℝ → GenericQuadraticTensor.Tensor ι) (r : ℝ)
    (hH : ∀ i j k, H r i j k = H r i k j) (x : ι → ℝ) :
    HasFDerivAt (fun y => fderiv ℝ (GenericQuadraticTensor.field H r) y)
      (realContinuousBilinear (H r)) x := by
  have hf : (fun y => fderiv ℝ (GenericQuadraticTensor.field H r) y) =
      realContinuousBilinear (H r) := by
    funext y
    exact field_fderiv H r hH y
  rw [hf]
  exact (realContinuousBilinear (H r)).hasFDerivAt

theorem field_hessian (H : ℝ → GenericQuadraticTensor.Tensor ι) (r : ℝ)
    (hH : ∀ i j k, H r i j k = H r i k j) (x : ι → ℝ) :
    fderiv ℝ (fun y => fderiv ℝ (GenericQuadraticTensor.field H r) y) x =
      realContinuousBilinear (H r) :=
  (field_fderiv_hasFDerivAt H r hH x).fderiv

end
end ThreeSitePhosphorylation.GenericTensorDerivative
