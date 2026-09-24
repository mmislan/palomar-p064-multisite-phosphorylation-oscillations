import proofs.ThreeSitePhosphorylation.ScaledNormalJacobian

/-! Actual block assembly for the scaled zero-load source Jacobian.
The upper-right coupling is retained as an actual derivative block. -/
namespace ThreeSitePhosphorylation.ScaledJacobianBlock
noncomputable section
open MultisiteChart MultisiteCenteredFace MultisiteNormalDerivative
open ScaledMultisiteSource ScaledMultisiteCenteredFace MultisiteSplit
open ScaledNormalJacobian

def centeredJacobian {n : ℕ} (Et Ft St : ℝ)
    (k : PhosphorylationSharpness.Rates n) (zstar : ReducedState n) :
    ReducedState n →L[ℝ] ReducedState n :=
  fderiv ℝ (centeredField Et Ft St k zstar) 0

def faceCLM (n : ℕ) : ReducedState n →L[ℝ] ReducedState (n+1) :=
  (faceInclusion n).toContinuousLinearMap

/-- Differentiate the literal source restriction to the zero-load face. -/
theorem jacobian_face {n : ℕ} (Et Ft St : ℝ)
    (k : PhosphorylationSharpness.Rates n) (κ α : ℝ) (zstar : ReducedState n) :
    (centeredJacobian Et Ft St (appendScaledRates k κ 0 α)
      (faceInclusion n zstar)).comp (faceCLM n) =
      (faceCLM n).comp (centeredJacobian Et Ft St k zstar) := by
  let F := centeredField Et Ft St k zstar
  let G := centeredField Et Ft St (appendScaledRates k κ 0 α) (faceInclusion n zstar)
  have hF : HasFDerivAt F (centeredJacobian Et Ft St k zstar) 0 :=
    ((centeredField_smooth Et Ft St k zstar).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hG : HasFDerivAt G
      (centeredJacobian Et Ft St (appendScaledRates k κ 0 α) (faceInclusion n zstar))
      (faceCLM n 0) := by
    simpa only [map_zero] using
      ((centeredField_smooth Et Ft St (appendScaledRates k κ 0 α)
        (faceInclusion n zstar)).differentiable (by simp)).differentiableAt.hasFDerivAt (x := 0)
  have hleft := hG.comp 0 (faceCLM n).hasFDerivAt
  have hright := (faceCLM n).hasFDerivAt.comp 0 hF
  have he : G ∘ faceCLM n = faceCLM n ∘ F := by
    funext y
    exact scaled_centeredField_zero_load Et Ft St k κ α zstar y
  rw [he] at hleft
  exact hleft.unique hright

theorem jacobian_face_apply {n : ℕ} (Et Ft St : ℝ)
    (k : PhosphorylationSharpness.Rates n) (κ α : ℝ)
    (zstar x : ReducedState n) :
    centeredJacobian Et Ft St (appendScaledRates k κ 0 α) (faceInclusion n zstar)
      (faceInclusion n x) =
      faceInclusion n (centeredJacobian Et Ft St k zstar x) := by
  exact DFunLike.congr_fun (jacobian_face Et Ft St k κ α zstar) x

/-- This is the actual source coupling, with no vanishing assumption. -/
def upperCoupling {n : ℕ} (Et Ft St : ℝ)
    (k : PhosphorylationSharpness.Rates n) (κ : ℝ) (zstar : ReducedState n) :
    (Fin 3 → ℝ) →L[ℝ] ReducedState n :=
  (oldProjection n).comp
    ((centeredJacobian Et Ft St (appendScaledRates k κ 0 (κ/referenceF Ft zstar))
      (faceInclusion n zstar)).comp (normalInclusion n))

/-- The complete actual Jacobian in split coordinates is upper triangular.
Only the bottom-left block vanishes; U is the actual upper-right block. -/
theorem jacobian_split_apply {n : ℕ} (Et Ft St : ℝ)
    (k : PhosphorylationSharpness.Rates n) (κ : ℝ) (zstar : ReducedState n)
    (hf : referenceF Ft zstar ≠ 0) (x : ReducedState n) (z : Fin 3 → ℝ) :
    (splitContinuous n).symm
      (centeredJacobian Et Ft St (appendScaledRates k κ 0 (κ/referenceF Ft zstar))
        (faceInclusion n zstar) (splitContinuous n (x,z))) =
      (centeredJacobian Et Ft St k zstar x + upperCoupling Et Ft St k κ zstar z,
        κ • normalBlock z) := by
  let J := centeredJacobian Et Ft St
    (appendScaledRates k κ 0 (κ/referenceF Ft zstar)) (faceInclusion n zstar)
  have hsplit : (splitContinuous n) (x,z) = faceInclusion n x + normalInclusion n z :=
    split_decomposition x z
  apply Prod.ext
  · change oldProjection n (J (splitContinuous n (x,z))) = _
    rw [hsplit,map_add]
    have hface : J (faceInclusion n x) =
        faceInclusion n (centeredJacobian Et Ft St k zstar x) :=
      jacobian_face_apply Et Ft St k κ (κ/referenceF Ft zstar) zstar x
    rw [hface,map_add,oldProjection_apply,oldCoordinates_face]
    rfl
  · change normalProjectionCLM n (fderiv ℝ (centeredField Et Ft St
        (appendScaledRates k κ 0 (κ/referenceF Ft zstar)) (faceInclusion n zstar)) 0
        (splitContinuous n (x,z))) = κ • normalBlock z
    rw [scaled_centered_normal_fderiv_apply Et Ft St k κ zstar hf]
    have hn : normalProjectionCLM n (splitContinuous n (x,z)) = z := by
      rw [hsplit,map_add]
      change normalProjection (faceInclusion n x) + normalProjection (normalInclusion n z) = z
      rw [normalProjection_face,normalProjection_normal,zero_add]
    rw [hn]

end
end ThreeSitePhosphorylation.ScaledJacobianBlock
