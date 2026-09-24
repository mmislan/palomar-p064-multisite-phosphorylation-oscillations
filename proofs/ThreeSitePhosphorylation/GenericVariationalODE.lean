import proofs.ThreeSitePhosphorylation.Volterra

/-! Full-interval variational ODE from an explicit integral equation.
No source-specific differentiation or spectral condition is assumed. -/
namespace ThreeSitePhosphorylation.GenericVariationalODE
noncomputable section
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def constantPath : E →L[ℝ] ContinuousPath E := ContinuousLinearMap.const ℝ UnitTime

def integralVariation (x : E) (f : ContinuousPath E) (t : ℝ) : E :=
  x+∫ s in (0:ℝ)..t, pathExtension f s

omit [CompleteSpace E] in
theorem integralVariation_initial (x : E) (f : ContinuousPath E) :
    integralVariation x f 0=x := by simp [integralVariation]

omit [CompleteSpace E] in
theorem integralVariation_eq (x : E) (f q : ContinuousPath E)
    (he : q=constantPath x+linearPicard (ContinuousLinearMap.id ℝ E) f)
    (t : UnitTime) : integralVariation x f t=q t := by
  rw [he]
  rfl

theorem integralVariation_derivative (x : E) (f : ContinuousPath E) (t : ℝ) :
    HasDerivAt (integralVariation x f) (pathExtension f t) t := by
  have hc := pathExtension_continuous f
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (0:ℝ) t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  exact hd.const_add x

/-- A is the base linear field and D its supplied parameter variation.
Their interpretation as actual source derivatives must be docked separately. -/
def variationField (A D : E →L[ℝ] E) (T dr dT : ℝ)
    (u q : ContinuousPath E) : ContinuousPath E :=
  T • A.compLeftContinuous ℝ UnitTime q+
    dT • A.compLeftContinuous ℝ UnitTime u+
      T • (dr • D.compLeftContinuous ℝ UnitTime u)

omit [CompleteSpace E] in
theorem variationField_apply (A D : E →L[ℝ] E) (T dr dT : ℝ)
    (u q : ContinuousPath E) (t : UnitTime) :
    variationField A D T dr dT u q t=
      T • A (q t)+dT • A (u t)+T • (dr • D (u t)) := rfl

/-- The integral continuation solves the actual variational ODE on the
whole unit interval, including both endpoints. The Volterra equation is
an explicit hypothesis, not inferred from a source model implicitly. -/
theorem variational_ode (A D : E →L[ℝ] E) (T dr dT : ℝ)
    (x : E) (u q : ContinuousPath E)
    (he : q=constantPath x+linearPicard (ContinuousLinearMap.id ℝ E)
      (variationField A D T dr dT u q)) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    HasDerivAt (integralVariation x (variationField A D T dr dT u q))
      (T • A (integralVariation x (variationField A D T dr dT u q) t)+
        dT • A (u ⟨t,ht⟩)+T • (dr • D (u ⟨t,ht⟩))) t := by
  have hd := integralVariation_derivative x (variationField A D T dr dT u q) t
  rw [pathExtension,Set.projIcc_of_mem _ ht,variationField_apply] at hd
  rw [integralVariation_eq x _ q he ⟨t,ht⟩]
  exact hd

end
end ThreeSitePhosphorylation.GenericVariationalODE
