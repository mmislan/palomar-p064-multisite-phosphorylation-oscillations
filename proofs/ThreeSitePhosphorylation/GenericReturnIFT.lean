import proofs.ThreeSitePhosphorylation.GenericReturnTime

/-! Actual phase-return IFT for a selected smooth residual path operator.
The derivative, base phase equation and base fixed point are derived. -/
namespace ThreeSitePhosphorylation.GenericReturnIFT
noncomputable section
open scoped Topology
open GenericComplexification GenericLinearOrbit GenericReturnTime

abbrev ReturnData (E : Type*) := (ℝ × ℝ) × E

def returnArgument {E : Type*} (d : ReturnData E × ℝ) : GenericShootingMap.FlowData E :=
  ((d.1.1.1,(d.1.1.2,d.2)),d.1.2)

variable {ι : Type*} [Fintype ι]

def endpointPhase (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (p : (ι → ℂ) →ₗ[ℂ] ℂ) (d : ReturnData (ι → ℝ) × ℝ) : ℝ :=
  (p (GenericComplexification.complexify (ψ (returnArgument d) ⟨1,by norm_num⟩))).im

theorem returnArgument_smooth : ContDiff ℝ ⊤ (returnArgument (E := ι → ℝ)) := by
  unfold returnArgument
  fun_prop

theorem endpointPhase_smooth
    (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (p : (ι → ℂ) →ₗ[ℂ] ℂ) (d : ReturnData (ι → ℝ) × ℝ)
    (hψ : ContDiffAt ℝ ⊤ ψ (returnArgument d)) :
    ContDiffAt ℝ ⊤ (endpointPhase ψ p) d := by
  let H : (ι → ℝ) →L[ℝ] ℝ := Complex.imCLM.comp (GenericShootingInvertibility.sourceGauge p)
  have he := (ContinuousMap.evalCLM (R := ℝ) (M := ι → ℝ)
    (⟨1,by norm_num⟩ : UnitTime)).contDiff (n := ⊤)
  exact H.contDiff.contDiffAt.comp d (he.contDiffAt.comp d
    (hψ.comp d returnArgument_smooth.contDiffAt))

def returnPoint (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (τ : ReturnData (ι → ℝ) → ℝ) (d : ReturnData (ι → ℝ)) : ι → ℝ :=
  ψ (returnArgument (d,τ d)) ⟨1,by norm_num⟩

theorem returnPoint_smooth
    (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (τ : ReturnData (ι → ℝ) → ℝ) (d : ReturnData (ι → ℝ))
    (hτ : ContDiffAt ℝ ⊤ τ d)
    (hψ : ContDiffAt ℝ ⊤ ψ (returnArgument (d,τ d))) :
    ContDiffAt ℝ ⊤ (returnPoint ψ τ) d := by
  have ha := returnArgument_smooth.contDiffAt.comp d (contDiffAt_id.prodMk hτ)
  exact (ContinuousMap.evalCLM (R := ℝ) (M := ι → ℝ)
    (⟨1,by norm_num⟩ : UnitTime)).contDiff.contDiffAt.comp d (hψ.comp d ha)

omit [Fintype ι] in
theorem returnPoint_phase
    (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (τ : ReturnData (ι → ℝ) → ℝ) (p : (ι → ℂ) →ₗ[ℂ] ℂ)
    (d : ReturnData (ι → ℝ)) :
    (p (GenericComplexification.complexify (returnPoint ψ τ d))).im=endpointPhase ψ p (d,τ d) := rfl

/-- Time transversality is obtained from the actual residual, not assumed.
The selected ψ is preserved throughout, including local time uniqueness. -/
theorem smooth_poincare_time (A0 D : Matrix ι ι ℝ)
    (B : ℝ → ContinuousPath (ι → ℝ) → ContinuousPath (ι → ℝ))
    (r w : ℝ) (hw : 0<w) (v : ι → ℂ) (p : (ι → ℂ) →ₗ[ℂ] ℂ)
    (he : (GenericComplexification.complexMatrix (A0+r • D)).mulVec v=(Complex.I*(w:ℂ)) • v)
    (hleft : ∀ z, p ((GenericComplexification.complexMatrix (A0+r • D)).mulVec z)=(Complex.I*(w:ℂ))*p z)
    (hnorm : p v=1)
    (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (hψ : ContDiffAt ℝ ⊤ ψ ((0,(r,2*Real.pi/w)),GenericComplexification.realPart v))
    (hres : ∀ᶠ d in 𝓝 ((0,(r,2*Real.pi/w)),GenericComplexification.realPart v),
      GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
        D.mulVecLin.toContinuousLinearMap B (d,ψ d)=0) :
    ∃ τ : ReturnData (ι → ℝ) → ℝ,
      ContDiffAt ℝ ⊤ τ ((0,r),GenericComplexification.realPart v) ∧ τ ((0,r),GenericComplexification.realPart v)=2*Real.pi/w ∧
      (∀ᶠ d in 𝓝 ((0,r),GenericComplexification.realPart v), 0<τ d ∧ endpointPhase ψ p (d,τ d)=0 ∧
        GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
          D.mulVecLin.toContinuousLinearMap B
            (returnArgument (d,τ d),ψ (returnArgument (d,τ d)))=0) ∧
      (∀ᶠ d in 𝓝 (((0,r),GenericComplexification.realPart v),2*Real.pi/w),
        endpointPhase ψ p d=0 ↔ τ d.1=d.2) := by
  let T0 := 2*Real.pi/w
  let d0 : ReturnData (ι → ℝ) := ((0,r),GenericComplexification.realPart v)
  let F := endpointPhase ψ p
  have hs : ContDiffAt ℝ ⊤ F (d0,T0) := endpointPhase_smooth ψ p (d0,T0) hψ
  let A := fderiv ℝ F (d0,T0) ∘L ContinuousLinearMap.inr ℝ (ReturnData (ι → ℝ)) ℝ
  have hline : HasDerivAt (fun T : ℝ => (d0,T)) (0,1) T0 :=
    (hasDerivAt_const T0 d0).prodMk (hasDerivAt_id T0)
  have hc := hs.differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt T0 hline
  have hd := endpoint_phase_time_derivative A0 D B r w hw v p he hleft hnorm ψ hres
  have hA1 : A 1=w/2 := hc.unique hd
  have hact (t : ℝ) : A t=t*(w/2) := by
    calc
      A t = A (t • (1 : ℝ)) := by simp
      _ = t • A 1 := map_smul A t 1
      _ = t*(w/2) := by rw [hA1]; rfl
  have hn : w/2 ≠ 0 := ne_of_gt (by positivity)
  have hi : A.IsInvertible := by
    have hinj : Function.Injective A := by
      intro x y h
      rw [hact,hact] at h
      exact mul_right_cancel₀ hn h
    have hsurj : Function.Surjective A := by
      intro y
      exact ⟨y/(w/2),by rw [hact,div_mul_cancel₀ _ hn]⟩
    obtain ⟨b,hb⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj,hsurj⟩
    exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ ℝ b,hb⟩
  have hzero : F (d0,T0)=0 := by
    have hu := zero_amplitude_path_unique A0 D B r T0 (GenericComplexification.realPart v)
      (ψ ((0,(r,T0)),GenericComplexification.realPart v)) (GenericLinearOrbit.referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w T0)
      hres.self_of_nhds (critical_reference_solution A0 D B r w T0 v he)
    have hend := (GenericLinearOrbit.referencePath_endpoints (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w (ne_of_gt hw)).2
    have hp := normalized_eigen_real_pairing (A0+r • D) w (ne_of_gt hw) v p he hleft hnorm
    change (p (GenericComplexification.complexify (ψ ((0,(r,T0)),GenericComplexification.realPart v) ⟨1,by norm_num⟩))).im=0
    rw [hu,hend,hp]
    norm_num
  let τ := hs.implicitFunction (by simp) hi
  have hτ : ContDiffAt ℝ ⊤ τ d0 := hs.contDiffAt_implicitFunction (by simp) hi
  have hτ0 : τ d0=T0 := hs.implicitFunction_apply_self (by simp) hi
  have hphase : ∀ᶠ d in 𝓝 d0, F (d,τ d)=0 := by
    simpa only [hzero] using hs.eventually_apply_implicitFunction (by simp) hi
  have huniq : ∀ᶠ d in 𝓝 (d0,T0), F d=0 ↔ τ d.1=d.2 := by
    simpa only [hzero] using hs.eventually_apply_eq_iff_implicitFunction (by simp) hi
  have htend : Filter.Tendsto (fun d => returnArgument (d,τ d)) (𝓝 d0)
      (𝓝 ((0,(r,T0)),GenericComplexification.realPart v)) := by
    have hc := returnArgument_smooth.continuous.continuousAt.comp
      (continuousAt_id.prodMk hτ.continuousAt)
    simpa [hτ0,returnArgument,d0] using hc.tendsto
  have hpos : ∀ᶠ d in 𝓝 d0, 0<τ d := by
    have hh : 0<τ d0 := by rw [hτ0]; dsimp [T0]; positivity
    exact hτ.continuousAt.eventually (isOpen_Ioi.mem_nhds hh)
  refine ⟨τ,hτ,hτ0,?_,huniq⟩
  filter_upwards [hpos,hphase,htend.eventually hres] with d hd hp hr
  exact ⟨hd,hp,hr⟩

theorem returnPoint_base (A0 D : Matrix ι ι ℝ)
    (B : ℝ → ContinuousPath (ι → ℝ) → ContinuousPath (ι → ℝ))
    (r w : ℝ) (hw : 0<w) (v : ι → ℂ)
    (he : (GenericComplexification.complexMatrix (A0+r • D)).mulVec v=(Complex.I*(w:ℂ)) • v)
    (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (τ : ReturnData (ι → ℝ) → ℝ)
    (hτ0 : τ ((0,r),GenericComplexification.realPart v)=2*Real.pi/w)
    (hres : GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
      D.mulVecLin.toContinuousLinearMap B
      (((0,(r,2*Real.pi/w)),GenericComplexification.realPart v),ψ ((0,(r,2*Real.pi/w)),GenericComplexification.realPart v))=0) :
    returnPoint ψ τ ((0,r),GenericComplexification.realPart v)=GenericComplexification.realPart v := by
  have hu := zero_amplitude_path_unique A0 D B r (2*Real.pi/w) (GenericComplexification.realPart v)
    (ψ ((0,(r,2*Real.pi/w)),GenericComplexification.realPart v))
    (GenericLinearOrbit.referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w (2*Real.pi/w)) hres
    (critical_reference_solution A0 D B r w (2*Real.pi/w) v he)
  unfold returnPoint
  rw [hτ0]
  change ψ ((0,(r,2*Real.pi/w)),GenericComplexification.realPart v) ⟨1,by norm_num⟩=GenericComplexification.realPart v
  rw [hu]
  exact (GenericLinearOrbit.referencePath_endpoints (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w (ne_of_gt hw)).2

end
end ThreeSitePhosphorylation.GenericReturnIFT
