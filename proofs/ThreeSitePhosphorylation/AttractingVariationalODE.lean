import proofs.ThreeSitePhosphorylation.AttractingVariationalFlow

namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section

def integralVariation (x : ReducedState) (f : SourcePath) (t : ℝ) : ReducedState :=
  x+∫ s in (0:ℝ)..t, pathExtension f s

theorem integralVariation_initial (x : ReducedState) (f : SourcePath) :
    integralVariation x f 0=x := by simp [integralVariation]

theorem integralVariation_eq (x : ReducedState) (f q : SourcePath)
    (he : q=constantPath x+linearPicard (ContinuousLinearMap.id ℝ ReducedState) f)
    (t : UnitTime) : integralVariation x f t=q t := by
  rw [he]
  rfl

theorem integralVariation_derivative (x : ReducedState) (f : SourcePath) (t : ℝ) :
    HasDerivAt (integralVariation x f) (pathExtension f t) t := by
  have hc := pathExtension_continuous f
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (0:ℝ) t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  exact hd.const_add x

def variationField (r T dr dT : ℝ) (u q : SourcePath) : SourcePath :=
  T • pathLinear r q+dT • pathLinear r u+T • (dr • pathDelta u)

theorem variationField_apply (r T dr dT : ℝ) (u q : SourcePath) (t : UnitTime) :
    variationField r T dr dT u q t=
      T • linearPart r (q t)+dT • linearPart r (u t)+
        T • (dr • (linearPart 1-linearPart 0) (u t)) := by
  simp only [variationField,ContinuousMap.add_apply,ContinuousMap.smul_apply,pathLinear_apply]
  rfl

theorem variational_ode (r T dr dT : ℝ) (x : ReducedState) (u q : SourcePath)
    (he : q=constantPath x+linearPicard (ContinuousLinearMap.id ℝ ReducedState)
      (variationField r T dr dT u q)) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    HasDerivAt (integralVariation x (variationField r T dr dT u q))
      (T • linearPart r (integralVariation x (variationField r T dr dT u q) t)+
        dT • linearPart r (u ⟨t,ht⟩)+
          T • (dr • (linearPart 1-linearPart 0) (u ⟨t,ht⟩))) t := by
  have hd := integralVariation_derivative x (variationField r T dr dT u q) t
  rw [pathExtension,Set.projIcc_of_mem _ ht,variationField_apply] at hd
  rw [integralVariation_eq x _ q he ⟨t,ht⟩]
  exact hd

end
end ThreeSitePhosphorylation.AttractingWitness
