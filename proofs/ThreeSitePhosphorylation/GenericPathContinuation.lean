import proofs.ThreeSitePhosphorylation.GenericAffinePathExistence

namespace ThreeSitePhosphorylation.GenericPathContinuation
noncomputable section
open MeasureTheory
open GenericShootingMap GenericAffinePathResidual GenericAffinePathExistence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def timeField (A0 D : E →L[ℝ] E) (B : ℝ → ContinuousPath E → ContinuousPath E)
    (p : FlowData E) (u : ContinuousPath E) : ContinuousPath E :=
  p.1.2.2 • (pathLinear A0 D p.1.2.1 u+p.1.1 • B p.1.2.1 u)

def pathContinuation (A0 D : E →L[ℝ] E)
    (B : ℝ → ContinuousPath E → ContinuousPath E)
    (p : FlowData E) (u : ContinuousPath E) (t : ℝ) : E :=
  p.2+∫ s in (0:ℝ)..t, pathExtension (timeField A0 D B p u) s

omit [CompleteSpace E] in
theorem pathContinuation_initial (A0 D : E →L[ℝ] E)
    (B : ℝ → ContinuousPath E → ContinuousPath E) (p : FlowData E) (u : ContinuousPath E) :
    pathContinuation A0 D B p u 0=p.2 := by simp [pathContinuation]

omit [CompleteSpace E] in
theorem pathContinuation_eq (A0 D : E →L[ℝ] E)
    (B : ℝ → ContinuousPath E → ContinuousPath E) (p : FlowData E) (u : ContinuousPath E)
    (hu : pathResidual A0 D B (p,u)=0) (t : UnitTime) :
    u t=pathContinuation A0 D B p u t := by
  unfold pathResidual at hu
  rw [← map_smul] at hu
  have hh := sub_eq_iff_eq_add.mp (sub_eq_zero.mp hu)
  rw [add_comm] at hh
  exact congrArg (fun v : ContinuousPath E => v t) hh

theorem pathContinuation_derivative (A0 D : E →L[ℝ] E) (Q : ℝ → E → E)
    (B : ℝ → ContinuousPath E → ContinuousPath E)
    (hpoint : ∀ r u t, B r u t=Q r (u t))
    (p : FlowData E) (u : ContinuousPath E) (t : ℝ) :
    HasDerivAt (pathContinuation A0 D B p u)
      (p.1.2.2 • affineField A0 D Q (p.1.1,p.1.2.1) (pathExtension u t)) t := by
  have hc := pathExtension_continuous (timeField A0 D B p u)
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (0:ℝ) t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he : pathExtension (timeField A0 D B p u) t=
      p.1.2.2 • affineField A0 D Q (p.1.1,p.1.2.1) (pathExtension u t) := by
    change p.1.2.2 • affineLift A0 D B (p.1.1,p.1.2.1) u _=_
    rw [affineLift_apply A0 D Q B hpoint]
    rfl
  simpa only [pathContinuation,he] using hd.const_add p.2

/-- A literal residual solution satisfies the actual ODE, including the
endpoint derivatives of its integral continuation. Periodicity is separate. -/
theorem pathContinuation_solves (A0 D : E →L[ℝ] E) (Q : ℝ → E → E)
    (B : ℝ → ContinuousPath E → ContinuousPath E)
    (hpoint : ∀ r u t, B r u t=Q r (u t))
    (p : FlowData E) (u : ContinuousPath E) (hu : pathResidual A0 D B (p,u)=0)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    HasDerivAt (pathContinuation A0 D B p u)
      (p.1.2.2 • affineField A0 D Q (p.1.1,p.1.2.1)
        (pathContinuation A0 D B p u t)) t := by
  have he : pathExtension u t=pathContinuation A0 D B p u t := by
    rw [pathExtension,Set.projIcc_of_mem _ ht]
    exact pathContinuation_eq A0 D B p u hu ⟨t,ht⟩
  simpa only [he] using pathContinuation_derivative A0 D Q B hpoint p u t

end
end ThreeSitePhosphorylation.GenericPathContinuation
