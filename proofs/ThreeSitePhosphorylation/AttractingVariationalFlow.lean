import proofs.ThreeSitePhosphorylation.AttractingLinearFlow

/-! Actual rescaled ODE paths and their first parameter/period variation for A.
These equations alone do not establish Floquet stability. -/

namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section

def pathContinuation (p : FlowData) (u : SourcePath) (t : ℝ) : ReducedState :=
  p.2+∫ s in (0:ℝ)..t, pathExtension (pathField p.1 u) s

theorem pathContinuation_initial (p : FlowData) (u : SourcePath) :
    pathContinuation p u 0=p.2 := by simp [pathContinuation]

theorem pathContinuation_eq (p : FlowData) (u : SourcePath)
    (hu : pathResidual (p,u)=0) (t : UnitTime) : u t=pathContinuation p u t := by
  change u-constantPath p.2-linearPicard (ContinuousLinearMap.id ℝ ReducedState)
    (pathField p.1 u)=0 at hu
  have hh := sub_eq_iff_eq_add.mp (sub_eq_zero.mp hu)
  rw [add_comm] at hh
  have ht := congrArg (fun v : SourcePath => v t) hh
  exact ht

theorem pathContinuation_derivative (p : FlowData) (u : SourcePath) (t : ℝ) :
    HasDerivAt (pathContinuation p u)
      (p.1.2.2 • rescaledField p.1.1 p.1.2.1 (pathExtension u t)) t := by
  have hc := pathExtension_continuous (pathField p.1 u)
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (0:ℝ) t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he : pathExtension (pathField p.1 u) t =
      p.1.2.2 • rescaledField p.1.1 p.1.2.1 (pathExtension u t) := by
    exact pathField_apply p.1.1 p.1.2.1 p.1.2.2 u _
  simpa only [pathContinuation,he] using hd.const_add p.2

/-- The constructed integral paths satisfy the actual rescaled ODE, including
one-sided endpoint data. This does not impose periodicity on nearby paths. -/
theorem pathContinuation_solves (p : FlowData) (u : SourcePath)
    (hu : pathResidual (p,u)=0) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    HasDerivAt (pathContinuation p u)
      (p.1.2.2 • rescaledField p.1.1 p.1.2.1 (pathContinuation p u t)) t := by
  have he : pathExtension u t=pathContinuation p u t := by
    rw [pathExtension,Set.projIcc_of_mem _ ht]
    exact pathContinuation_eq p u hu ⟨t,ht⟩
  simpa only [he] using pathContinuation_derivative p u t

/-- Scaling the constructed paths gives solutions of the literal reduced source. -/
theorem scaled_pathContinuation_solves (p : FlowData) (u : SourcePath)
    (hu : pathResidual (p,u)=0) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    HasDerivAt (fun s => p.1.1 • pathContinuation p u s)
      (p.1.2.2 • reduced p.1.2.1 (p.1.1 • pathContinuation p u t)) t := by
  have hd := (pathContinuation_solves p u hu t ht).const_smul p.1.1
  rw [smul_comm p.1.1 p.1.2.2,rescaledField_source] at hd
  exact hd

end
end ThreeSitePhosphorylation.AttractingWitness

namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section
open scoped Topology

def pathDelta : SourcePath →L[ℝ] SourcePath :=
  (linearPart 1).compLeftContinuous ℝ UnitTime-
    (linearPart 0).compLeftContinuous ℝ UnitTime

theorem pathLinear_direction (r dr : ℝ) (u : ℝ → SourcePath) (q : SourcePath)
    (hu : HasDerivAt u q 0) :
    HasDerivAt (fun s => pathLinear (r+s*dr) (u s))
      (pathLinear r q+dr • pathDelta (u 0)) 0 := by
  have hr : HasDerivAt (fun s : ℝ => r+s*dr) dr 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const dr).const_add r
  have h0 := ((linearPart 0).compLeftContinuous ℝ UnitTime).hasFDerivAt.comp_hasDerivAt 0 hu
  have hd := pathDelta.hasFDerivAt.comp_hasDerivAt 0 hu
  have hh := h0.add (hr.smul hd)
  convert hh using 1
  simp only [zero_mul,add_zero,pathLinear,pathDelta,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,Function.comp_apply]
  abel

theorem pathField_direction (r T dr dT : ℝ) (u : ℝ → SourcePath) (q : SourcePath)
    (hu : HasDerivAt u q 0) :
    HasDerivAt (fun s => pathField (0,(r+s*dr,T+s*dT)) (u s))
      (T • pathLinear r q+dT • pathLinear r (u 0)+T • (dr • pathDelta (u 0))) 0 := by
  have ht : HasDerivAt (fun s : ℝ => T+s*dT) dT 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const dT).const_add T
  have hh := ht.smul (pathLinear_direction r dr u q hu)
  convert hh using 1
  · ext s
    simp [pathField]
  · simp only [zero_mul,add_zero,smul_add]
    abel

/-- Differentiating the actual integral equation gives the full parameter/period
variational equation on the whole unit interval. -/
theorem variational_path_equation (r T dr dT : ℝ) (x dx : ReducedState)
    (u : ℝ → SourcePath) (q : SourcePath) (hu : HasDerivAt u q 0)
    (he : ∀ᶠ s in 𝓝 (0:ℝ), pathResidual (((0,(r+s*dr,T+s*dT)),x+s • dx),u s)=0) :
    q=constantPath dx+linearPicard (ContinuousLinearMap.id ℝ ReducedState)
      (T • pathLinear r q+dT • pathLinear r (u 0)+T • (dr • pathDelta (u 0))) := by
  have hx : HasDerivAt (fun s : ℝ => x+s • dx) dx 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const dx).const_add x
  have hc := constantPath.hasFDerivAt.comp_hasDerivAt 0 hx
  have hf := (linearPicard (ContinuousLinearMap.id ℝ ReducedState)).hasFDerivAt.comp_hasDerivAt 0
    (pathField_direction r T dr dT u q hu)
  have hh := (hu.sub hc).sub hf
  have hz : HasDerivAt (fun s : ℝ => pathResidual (((0,(r+s*dr,T+s*dT)),x+s • dx),u s)) 0 0 :=
    (hasDerivAt_const (x := (0:ℝ)) (c := (0:SourcePath))).congr_of_eventuallyEq he
  have hd := hh.unique hz
  exact sub_eq_iff_eq_add.mp (sub_eq_zero.mp hd) |>.trans (add_comm _ _)

end
end ThreeSitePhosphorylation.AttractingWitness
