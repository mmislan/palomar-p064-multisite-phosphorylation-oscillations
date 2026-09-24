import proofs.ThreeSitePhosphorylation.ScaledMultisiteCenteredFace
import proofs.ThreeSitePhosphorylation.MultisiteSmoothField
import proofs.ThreeSitePhosphorylation.MultisiteSplit

/-! The actual bottom block of the fixed-total, zero-load scaled source
Jacobian. Differentiability is derived from the literal chemical field. -/
namespace ThreeSitePhosphorylation.ScaledNormalJacobian
noncomputable section
set_option maxHeartbeats 700000
open MultisiteChart MultisiteCenteredFace MultisiteNormalDerivative
open ScaledMultisiteSource ScaledMultisiteCenteredFace MultisiteSplit

/-- Normal coordinates are ordered C,S,D. -/
def normalBlockLinear : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun z := ![-2*z 0,z 0-z 1+z 2,z 1-2*z 2]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' a z := by
    ext i
    fin_cases i <;> simp <;> ring

def normalBlock : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  normalBlockLinear.toContinuousLinearMap

theorem normalBlock_apply (z : Fin 3 → ℝ) :
    normalBlock z = ![-2*z 0,z 0-z 1+z 2,z 1-2*z 2] := rfl

/-- Smoothness is obtained from mass-action components, with fixed rates
and a fixed translation of the reduced conservation-class chart. -/
theorem centeredField_smooth {n : ℕ} (Et Ft St : ℝ)
    (k : PhosphorylationSharpness.Rates n) (zstar : ReducedState n) :
    ContDiff ℝ ⊤ (centeredField Et Ft St k zstar) := by
  change ContDiff ℝ ⊤ (fun y : ReducedState n => reducedField Et Ft St k (zstar+y))
  have hk : MultisiteSmoothField.RatesSmooth (fun _ : ℝ => k) :=
    ⟨fun _ => contDiff_const,fun _ => contDiff_const,fun _ => contDiff_const,
      fun _ => contDiff_const,fun _ => contDiff_const,fun _ => contDiff_const⟩
  have hj := MultisiteSmoothField.reducedField_fixed_totals_smooth
    (fun _ : ℝ => k) Et Ft St hk
  have ht : ContDiff ℝ ⊤ (fun y : ReducedState n => ((0 : ℝ),zstar+y)) :=
    contDiff_const.prodMk (contDiff_const.add contDiff_id)
  simpa only [Function.comp_def] using hj.comp ht

/-- Every direction is split into its old and new coordinates. The actual
Frechet derivative agrees with the previously derived line derivative;
the fixed-total corrections remain in that line calculation. -/
theorem scaled_centered_normal_fderiv_apply {n : ℕ} (Et Ft St : ℝ)
    (k : PhosphorylationSharpness.Rates n) (κ : ℝ) (zstar : ReducedState n)
    (hf : referenceF Ft zstar ≠ 0) (v : ReducedState (n+1)) :
    normalProjectionCLM n
      (fderiv ℝ (centeredField Et Ft St
        (appendScaledRates k κ 0 (κ/referenceF Ft zstar))
        (faceInclusion n zstar)) 0 v) =
      κ • normalBlock (normalProjectionCLM n v) := by
  let F := centeredField Et Ft St
    (appendScaledRates k κ 0 (κ/referenceF Ft zstar)) (faceInclusion n zstar)
  have hs : ContDiff ℝ ⊤ F := centeredField_smooth Et Ft St _ _
  have hd : HasFDerivAt F (fderiv ℝ F 0) 0 :=
    (hs.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hfield := hd.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hactual := (normalProjectionCLM n).hasFDerivAt.comp_hasDerivAt 0 hfield
  have hexact := scaled_centered_normal_hasDerivAt Et Ft St k κ zstar
    (oldCoordinates v) (normalProjection v 0) (normalProjection v 1)
    (normalProjection v 2) hf
  rw [append_coordinates] at hexact
  have hsame : HasDerivAt (fun t : ℝ => normalProjection (F (t • v)))
      (normalProjectionCLM n (fderiv ℝ F 0 v)) 0 := hactual
  simpa only [F,normalProjectionCLM_apply,normalBlock_apply] using hsame.unique hexact

/-- Bundled bottom-row identity; the upper-right coupling is unrestricted. -/
theorem scaled_centered_normal_fderiv {n : ℕ} (Et Ft St : ℝ)
    (k : PhosphorylationSharpness.Rates n) (κ : ℝ) (zstar : ReducedState n)
    (hf : referenceF Ft zstar ≠ 0) :
    (normalProjectionCLM n).comp
      (fderiv ℝ (centeredField Et Ft St
        (appendScaledRates k κ 0 (κ/referenceF Ft zstar))
        (faceInclusion n zstar)) 0) =
      (κ • normalBlock).comp (normalProjectionCLM n) := by
  apply ContinuousLinearMap.ext
  intro v
  exact scaled_centered_normal_fderiv_apply Et Ft St k κ zstar hf v

end
end ThreeSitePhosphorylation.ScaledNormalJacobian
