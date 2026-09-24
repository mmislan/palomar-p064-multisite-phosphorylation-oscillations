import proofs.ThreeSitePhosphorylation.MultisiteNormalDerivative
import proofs.ThreeSitePhosphorylation.ScaledMultisiteSource

/-! Actual fixed-total centered source identities for the scaled existential
site-addition route. Full Frechet block assembly is a separate obligation. -/
namespace ThreeSitePhosphorylation.ScaledMultisiteCenteredFace
noncomputable section
open MultisiteChart MultisiteSource MultisiteCenteredFace MultisiteNormalDerivative
open ScaledMultisiteSource
set_option maxHeartbeats 500000

theorem scaled_reducedField_zero_load {n : ℕ} (Et Ft St : ℝ)
    (k : PhosphorylationSharpness.Rates n) (κ α : ℝ) (y : ReducedState n) :
    reducedField Et Ft St (appendScaledRates k κ 0 α) (appendReduced y 0 0 0)=
      appendReduced (reducedField Et Ft St k y) 0 0 0 := by
  unfold reducedField
  rw [chart_zero_append,scaled_zero_load_face,project_appendState]

/-- On the actual invariant face the centered parent field is unchanged,
even though every new-site rate has an independent positive scale. -/
theorem scaled_centeredField_zero_load {n : ℕ} (Et Ft St : ℝ)
    (k : PhosphorylationSharpness.Rates n) (κ α : ℝ) (zstar y : ReducedState n) :
    centeredField Et Ft St (appendScaledRates k κ 0 α)
      (faceInclusion n zstar) (faceInclusion n y)=
      faceInclusion n (centeredField Et Ft St k zstar y) := by
  change reducedField Et Ft St (appendScaledRates k κ 0 α)
      (faceInclusion n zstar+faceInclusion n y)=_
  rw [← (faceInclusion n).map_add]
  exact scaled_reducedField_zero_load Et Ft St k κ α (zstar+y)

/-- The free F variation is supplied by fixed-total chart reconstruction,
not assumed independently. All omitted inventory corrections are retained. -/
theorem scaled_centered_normal_expansion {n : ℕ} (Et Ft St : ℝ)
    (k : PhosphorylationSharpness.Rates n) (κ : ℝ) (zstar u : ReducedState n)
    (c s d t : ℝ) (hf : referenceF Ft zstar ≠ 0) :
    normalProjection (centeredField Et Ft St
      (appendScaledRates k κ 0 (κ/referenceF Ft zstar)) (faceInclusion n zstar)
      (t • appendReduced u c s d))=
      t • (κ • (![-2*c,c-s+d,s-2*d] : Fin 3 → ℝ))+
      t^2 • (κ • (![0,-phosphataseVariation u d*s/referenceF Ft zstar,
        phosphataseVariation u d*s/referenceF Ft zstar] : Fin 3 → ℝ)) := by
  have h := scaled_normal_expansion k
    (chart (Et-t*c) (Ft-t*d) (St-t*(c+s+d)) (zstar+t • u))
    κ (referenceF Ft zstar) (phosphataseVariation u d) c s d t hf
    (old_chart_freeF Et Ft St zstar u c s d t)
  dsimp only at h
  change ![(PhosphorylationSharpness.field (appendScaledRates k κ 0 (κ/referenceF Ft zstar))
      (chart Et Ft St (faceInclusion n zstar+t • appendReduced u c s d))).C (Fin.last n),
    (PhosphorylationSharpness.field (appendScaledRates k κ 0 (κ/referenceF Ft zstar))
      (chart Et Ft St (faceInclusion n zstar+t • appendReduced u c s d))).S (Fin.last (n+1)),
    (PhosphorylationSharpness.field (appendScaledRates k κ 0 (κ/referenceF Ft zstar))
      (chart Et Ft St (faceInclusion n zstar+t • appendReduced u c s d))).D (Fin.last n)]=_
  rw [fixed_total_chart_path]
  exact h

theorem scaled_centered_normal_eq_smul {n : ℕ} (Et Ft St : ℝ)
    (k : PhosphorylationSharpness.Rates n) (κ : ℝ) (zstar u : ReducedState n)
    (c s d t : ℝ) (hf : referenceF Ft zstar ≠ 0) :
    normalProjection (centeredField Et Ft St
      (appendScaledRates k κ 0 (κ/referenceF Ft zstar)) (faceInclusion n zstar)
      (t • appendReduced u c s d))=
      κ • normalProjection (centeredField Et Ft St
        (appendRates k 0 (1/referenceF Ft zstar)) (faceInclusion n zstar)
        (t • appendReduced u c s d)) := by
  rw [scaled_centered_normal_expansion Et Ft St k κ zstar u c s d t hf,
    centered_normal_expansion Et Ft St k zstar u c s d t hf]
  ext i
  fin_cases i <;> simp <;> ring

/-- Actual transverse directional derivative is κK, independent of the old
direction. This does not assert the upper-right source block vanishes. -/
theorem scaled_centered_normal_hasDerivAt {n : ℕ} (Et Ft St : ℝ)
    (k : PhosphorylationSharpness.Rates n) (κ : ℝ) (zstar u : ReducedState n)
    (c s d : ℝ) (hf : referenceF Ft zstar ≠ 0) :
    HasDerivAt (fun t : ℝ => normalProjection (centeredField Et Ft St
      (appendScaledRates k κ 0 (κ/referenceF Ft zstar)) (faceInclusion n zstar)
      (t • appendReduced u c s d))) (κ • (![-2*c,c-s+d,s-2*d] : Fin 3 → ℝ)) 0 := by
  have he : (fun t : ℝ => normalProjection (centeredField Et Ft St
      (appendScaledRates k κ 0 (κ/referenceF Ft zstar)) (faceInclusion n zstar)
      (t • appendReduced u c s d)))=
      (fun t => κ • normalProjection (centeredField Et Ft St
        (appendRates k 0 (1/referenceF Ft zstar)) (faceInclusion n zstar)
        (t • appendReduced u c s d))) :=
    funext (fun t => scaled_centered_normal_eq_smul Et Ft St k κ zstar u c s d t hf)
  rw [he]
  exact (centered_normal_hasDerivAt Et Ft St k zstar u c s d hf).const_smul κ

end
end ThreeSitePhosphorylation.ScaledMultisiteCenteredFace
