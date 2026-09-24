import proofs.ThreeSitePhosphorylation.GenericClosedPaths

namespace ThreeSitePhosphorylation.GenericReturnTime
noncomputable section
open scoped Topology

variable {ι : Type*} [Fintype ι]

/-- At amplitude zero the literal residual is the invertible Volterra
operator applied to the path, minus its prescribed initial value. -/
theorem pathResidual_zero_amplitude (A0 D : Matrix ι ι ℝ)
    (B : ℝ → ContinuousPath (ι → ℝ) → ContinuousPath (ι → ℝ))
    (r T : ℝ) (x : ι → ℝ) (u : ContinuousPath (ι → ℝ)) :
    GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
      D.mulVecLin.toContinuousLinearMap B (((0,(r,T)),x),u)=
      (1-linearPicard (T • (A0+r • D).mulVecLin.toContinuousLinearMap)) u-
        GenericVariationalODE.constantPath x := by
  simp only [GenericAffinePathResidual.pathResidual,zero_smul,add_zero,
    GenericAffinePathResidual.pathLinear]
  rw [GenericClosedPaths.picard_lift,← GenericShootingInvertibility.matrix_operator_affine]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply]
  abel

theorem zero_amplitude_path_unique (A0 D : Matrix ι ι ℝ)
    (B : ℝ → ContinuousPath (ι → ℝ) → ContinuousPath (ι → ℝ))
    (r T : ℝ) (x : ι → ℝ) (u v : ContinuousPath (ι → ℝ))
    (hu : GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
      D.mulVecLin.toContinuousLinearMap B (((0,(r,T)),x),u)=0)
    (hv : GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
      D.mulVecLin.toContinuousLinearMap B (((0,(r,T)),x),v)=0) : u=v := by
  rw [pathResidual_zero_amplitude] at hu hv
  have hh := (sub_eq_zero.mp hu).trans (sub_eq_zero.mp hv).symm
  obtain ⟨b,hb⟩ := linearPicard_one_sub_isUnit
    (T • (A0+r • D).mulVecLin.toContinuousLinearMap)
  apply (ContinuousLinearEquiv.unitsEquiv ℝ (ContinuousPath (ι → ℝ)) b).injective
  change (b : ContinuousPath (ι → ℝ) →L[ℝ] ContinuousPath (ι → ℝ)) u=
    (b : ContinuousPath (ι → ℝ) →L[ℝ] ContinuousPath (ι → ℝ)) v
  rwa [hb]

theorem critical_reference_solution (A0 D : Matrix ι ι ℝ)
    (B : ℝ → ContinuousPath (ι → ℝ) → ContinuousPath (ι → ℝ))
    (r w T : ℝ) (v : ι → ℂ)
    (he : (GenericComplexification.complexMatrix (A0+r • D)).mulVec v=
      (Complex.I*(w:ℂ)) • v) :
    GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
      D.mulVecLin.toContinuousLinearMap B
      (((0,(r,T)),GenericComplexification.realPart v),
        GenericLinearOrbit.referencePath (GenericComplexification.realPart v)
          (GenericComplexification.imagPart v) w T)=0 := by
  rw [pathResidual_zero_amplitude]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply]
  have hh := GenericCriticalOrbit.critical_reference_integral (A0+r • D) w T v he
  change _=GenericVariationalODE.constantPath (GenericComplexification.realPart v)+_ at hh
  exact sub_eq_zero.mpr (sub_eq_iff_eq_add.mpr hh)

theorem normalized_eigen_real_pairing (A : Matrix ι ι ℝ) (w : ℝ) (hw : w ≠ 0)
    (v : ι → ℂ) (p : (ι → ℂ) →ₗ[ℂ] ℂ)
    (he : (GenericComplexification.complexMatrix A).mulVec v=(Complex.I*(w:ℂ)) • v)
    (hleft : ∀ z, p ((GenericComplexification.complexMatrix A).mulVec z)=(Complex.I*(w:ℂ))*p z)
    (hnorm : p v=1) :
    p (GenericComplexification.complexify (GenericComplexification.realPart v))=(1/2:ℂ) := by
  have hm : p (GenericComplexification.conjugateVector v)=0 := by
    have hh := hleft (GenericComplexification.conjugateVector v)
    rw [GenericComplexification.conjugate_eigen A w v he,map_smul,smul_eq_mul] at hh
    have hz : (-Complex.I*(w:ℂ))-(Complex.I*(w:ℂ)) ≠ 0 := by
      intro hz
      have hi := congrArg Complex.im hz
      simp at hi
      exact hw (by linarith)
    apply (mul_eq_zero.mp (show ((-Complex.I*(w:ℂ))-(Complex.I*(w:ℂ)))*
      p (GenericComplexification.conjugateVector v)=0 by linear_combination hh)).resolve_left hz
  have hh := congrArg p (GenericComplexification.complexify_orbit v 0)
  simpa [map_add,map_smul,hnorm,hm] using hh

/-- The endpoint derivative follows from the residual and exact orbit.
No derivative or smoothness of the supplied path selector is assumed. -/
theorem endpoint_phase_time_derivative (A0 D : Matrix ι ι ℝ)
    (B : ℝ → ContinuousPath (ι → ℝ) → ContinuousPath (ι → ℝ))
    (r w : ℝ) (hw : 0<w) (v : ι → ℂ) (p : (ι → ℂ) →ₗ[ℂ] ℂ)
    (he : (GenericComplexification.complexMatrix (A0+r • D)).mulVec v=(Complex.I*(w:ℂ)) • v)
    (hleft : ∀ z, p ((GenericComplexification.complexMatrix (A0+r • D)).mulVec z)=
      (Complex.I*(w:ℂ))*p z) (hnorm : p v=1)
    (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (hres : ∀ᶠ d in 𝓝 ((0,(r,2*Real.pi/w)),GenericComplexification.realPart v),
      GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
        D.mulVecLin.toContinuousLinearMap B (d,ψ d)=0) :
    HasDerivAt (fun T : ℝ => (p (GenericComplexification.complexify
      (ψ ((0,(r,T)),GenericComplexification.realPart v) ⟨1,by norm_num⟩))).im)
      (w/2) (2*Real.pi/w) := by
  let T0 := 2*Real.pi/w
  let L : (ι → ℝ) →L[ℝ] ℝ := Complex.imCLM.comp (GenericShootingInvertibility.sourceGauge p)
  have hreal := normalized_eigen_real_pairing (A0+r • D) w (ne_of_gt hw) v p he hleft hnorm
  have hend : GenericLinearOrbit.linearOrbit (GenericComplexification.realPart v)
      (GenericComplexification.imagPart v) w T0=GenericComplexification.realPart v := by
    have hh := (GenericLinearOrbit.referencePath_endpoints (GenericComplexification.realPart v)
      (GenericComplexification.imagPart v) w (ne_of_gt hw)).2
    simpa [GenericLinearOrbit.referencePath,T0] using hh
  have hphase : L ((A0+r • D).mulVec (GenericComplexification.realPart v))=w/2 := by
    change (p (GenericComplexification.complexify
      ((A0+r • D).mulVec (GenericComplexification.realPart v)))).im=w/2
    rw [GenericComplexification.complexify_action,hleft,hreal]
    simp [div_eq_mul_inv]
  obtain ⟨ha,hb⟩ := GenericComplexification.source_eigen_real_imag (A0+r • D) w v he
  have hd := L.hasFDerivAt.comp_hasDerivAt T0
    (GenericLinearOrbit.linearOrbit_derivative (A0+r • D).mulVecLin.toContinuousLinearMap
      (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w ha hb T0)
  rw [hend] at hd
  simp only [LinearMap.coe_toContinuousLinearMap',Matrix.mulVecLin_apply,hphase] at hd
  have hc : ContinuousAt (fun T : ℝ =>
      ((0,(r,T)),GenericComplexification.realPart v) : ℝ → GenericShootingMap.FlowData (ι → ℝ)) T0 := by
    fun_prop
  have hev := hc.tendsto.eventually hres
  have heq : (fun T : ℝ => (p (GenericComplexification.complexify
      (ψ ((0,(r,T)),GenericComplexification.realPart v) ⟨1,by norm_num⟩))).im) =ᶠ[𝓝 T0]
      (fun T => L (GenericLinearOrbit.linearOrbit (GenericComplexification.realPart v)
        (GenericComplexification.imagPart v) w T)) := by
    filter_upwards [hev] with T hT
    have hu := zero_amplitude_path_unique A0 D B r T (GenericComplexification.realPart v)
      (ψ ((0,(r,T)),GenericComplexification.realPart v))
      (GenericLinearOrbit.referencePath (GenericComplexification.realPart v)
        (GenericComplexification.imagPart v) w T) hT (critical_reference_solution A0 D B r w T v he)
    rw [hu]
    simp [GenericLinearOrbit.referencePath,L,GenericShootingInvertibility.sourceGauge]
  exact HasDerivAt.congr_of_eventuallyEq hd heq

end
end ThreeSitePhosphorylation.GenericReturnTime
