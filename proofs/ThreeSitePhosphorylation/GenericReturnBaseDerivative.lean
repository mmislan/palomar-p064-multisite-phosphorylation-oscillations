import proofs.ThreeSitePhosphorylation.GenericReturnIFT
import proofs.ThreeSitePhosphorylation.GenericReturnBaseVariation
import proofs.ThreeSitePhosphorylation.GenericAmplitudeVariation

/-! Actual base derivative of the phase-corrected return map. The
homogeneous endpoint formula is derived from the selected path residual. -/
namespace ThreeSitePhosphorylation.GenericReturnBaseDerivative
noncomputable section
open scoped Topology
open GenericComplexification GenericLinearOrbit GenericVariationalODE GenericReturnIFT

/-- Here amplitude is identically zero, unlike the generic amplitude
variation theorem where amplitude is the curve parameter itself. -/
theorem zero_amplitude_variational_curve_equation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A0 D : E →L[ℝ] E) (B : ℝ → ContinuousPath E → ContinuousPath E)
    (R T : ℝ → ℝ) (x : ℝ → E) (u : ℝ → ContinuousPath E)
    (dr dT : ℝ) (dx : E) (q : ContinuousPath E)
    (hr : HasDerivAt R dr 0) (ht : HasDerivAt T dT 0)
    (hx : HasDerivAt x dx 0) (hu : HasDerivAt u q 0)
    (he : ∀ᶠ s in 𝓝 (0:ℝ),
      GenericAffinePathResidual.pathResidual A0 D B (((0,(R s,T s)),x s),u s)=0) :
    q=constantPath dx+linearPicard (ContinuousLinearMap.id ℝ E)
      (variationField (A0+(R 0) • D) D (T 0) dr dT (u 0) q) := by
  have hl := GenericAmplitudeVariation.pathLinear_curve_direction A0 D R u dr q hr hu
  have hfield : HasDerivAt
      (fun s => T s • GenericAffinePathResidual.pathLinear A0 D (R s) (u s))
      (variationField (A0+(R 0) • D) D (T 0) dr dT (u 0) q) 0 := by
    convert ht.smul hl using 1
    simp only [variationField,GenericAffinePathResidual.pathLinear]
    module
  have hc := (constantPath (E := E)).hasFDerivAt.comp_hasDerivAt 0 hx
  have hf := (linearPicard (ContinuousLinearMap.id ℝ E)).hasFDerivAt.comp_hasDerivAt 0 hfield
  have hh : HasDerivAt
      (fun s => GenericAffinePathResidual.pathResidual A0 D B (((0,(R s,T s)),x s),u s))
      (q-constantPath dx-linearPicard (ContinuousLinearMap.id ℝ E)
        (variationField (A0+(R 0) • D) D (T 0) dr dT (u 0) q)) 0 := by
    simpa only [GenericAffinePathResidual.pathResidual,zero_smul,add_zero,
      Function.comp_def,map_smul] using (hu.sub hc).sub hf
  have hz : HasDerivAt
      (fun s => GenericAffinePathResidual.pathResidual A0 D B (((0,(R s,T s)),x s),u s)) 0 0 :=
    (hasDerivAt_const (x := (0:ℝ)) (c := (0:ContinuousPath E))).congr_of_eventuallyEq he
  exact sub_eq_iff_eq_add.mp (sub_eq_zero.mp (hh.unique hz)) |>.trans (add_comm _ _)

variable {ι : Type*} [Fintype ι]

theorem actual_return_state_derivative (A0 D : Matrix ι ι ℝ)
    (B : ℝ → ContinuousPath (ι → ℝ) → ContinuousPath (ι → ℝ))
    (r w : ℝ) (hw : 0<w) (v : ι → ℂ) (p : (ι → ℂ) →ₗ[ℂ] ℂ)
    (he : (GenericComplexification.complexMatrix (A0+r • D)).mulVec v=(Complex.I*(w:ℂ)) • v)
    (hleft : ∀ z, p ((GenericComplexification.complexMatrix (A0+r • D)).mulVec z)=(Complex.I*(w:ℂ))*p z)
    (hnorm : p v=1)
    (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (τ : ReturnData (ι → ℝ) → ℝ)
    (hψ : ContDiffAt ℝ ⊤ ψ ((0,(r,2*Real.pi/w)),GenericComplexification.realPart v))
    (hτ : ContDiffAt ℝ ⊤ τ ((0,r),GenericComplexification.realPart v))
    (hτ0 : τ ((0,r),GenericComplexification.realPart v)=2*Real.pi/w)
    (hres : ∀ᶠ d in 𝓝 ((0,(r,2*Real.pi/w)),GenericComplexification.realPart v),
      GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
        D.mulVecLin.toContinuousLinearMap B (d,ψ d)=0)
    (hphase : ∀ᶠ d in 𝓝 ((0,r),GenericComplexification.realPart v), endpointPhase ψ p (d,τ d)=0)
    (dx : ι → ℝ) (U : ContinuousPath (ι → ℝ))
    (hU : U=constantPath dx+
      linearPicard ((2*Real.pi/w) • (A0+r • D).mulVecLin.toContinuousLinearMap) U) :
    (fderiv ℝ (returnPoint ψ τ) ((0,r),GenericComplexification.realPart v)) ((0,0),dx) =
      U ⟨1,by norm_num⟩-
        ((p (GenericComplexification.complexify (U ⟨1,by norm_num⟩))).im/(w/2)) •
          (A0+r • D).mulVec (GenericComplexification.realPart v) := by
  let x := GenericComplexification.realPart v
  let T := 2*Real.pi/w
  let H : (ι → ℝ) →L[ℝ] ℝ := Complex.imCLM.comp (GenericShootingInvertibility.sourceGauge p)
  let d : ℝ → ReturnData (ι → ℝ) := fun s => ((0,r),x+s • dx)
  let S := fun s : ℝ => τ (d s)
  let e : ℝ → GenericShootingMap.FlowData (ι → ℝ) := fun s => ((0,(r,S s)),x+s • dx)
  let u := fun s : ℝ => ψ (e s)
  have hψ0 : ψ ((0,(r,T)),GenericComplexification.realPart v)=GenericLinearOrbit.referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w T :=
    GenericReturnTime.zero_amplitude_path_unique A0 D B r T (GenericComplexification.realPart v)
      _ _ hres.self_of_nhds (GenericReturnTime.critical_reference_solution A0 D B r w T v he)
  have hx : HasDerivAt (fun s : ℝ => x+s • dx) dx 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const dx).const_add x
  have hd : HasDerivAt d (((0:ℝ),0),dx) 0 :=
    (hasDerivAt_const (0:ℝ) ((0:ℝ),r)).prodMk hx
  let dT := fderiv ℝ τ ((0,r),x) ((0,0),dx)
  have hS : HasDerivAt S dT 0 :=
    (hτ.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd (by simp [d,x])
  have hS0 : S 0=T := by simpa [S,d,x,T] using hτ0
  have hecurve : HasDerivAt e (((0:ℝ),(0,dT)),dx) 0 :=
    ((hasDerivAt_const (0:ℝ) (0:ℝ)).prodMk ((hasDerivAt_const (0:ℝ) r).prodMk hS)).prodMk hx
  let q := fderiv ℝ ψ ((0,(r,T)),x) ((0,(0,dT)),dx)
  have hu : HasDerivAt u q 0 :=
    (hψ.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hecurve
      (by simp [e,hS0,x,T])
  have hev : ∀ᶠ s in 𝓝 (0:ℝ),
      GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
        D.mulVecLin.toContinuousLinearMap B (e s,u s)=0 := by
    have hh : Filter.Tendsto e (𝓝 0) (𝓝 ((0,(r,T)),x)) := by
      simpa only [e,zero_smul,add_zero,hS0] using hecurve.continuousAt.tendsto
    exact hh.eventually hres
  have hq := zero_amplitude_variational_curve_equation
    A0.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap B
    (fun _ => r) S (fun s => x+s • dx) u 0 dT dx q
    (hasDerivAt_const 0 r) hS hx hu hev
  have hq' : q=constantPath dx+linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ))
      (variationField (A0+r • D).mulVecLin.toContinuousLinearMap 0 T 0 dT
        (GenericLinearOrbit.referencePath x (GenericComplexification.imagPart v) w T) q) := by
    simpa [u,e,hS0,hψ0,x,variationField,
      GenericShootingInvertibility.matrix_operator_affine] using hq
  have heval : HasDerivAt (fun s => returnPoint ψ τ (d s)) (q ⟨1,by norm_num⟩) 0 :=
    (ContinuousMap.evalCLM (R := ℝ) (M := ι → ℝ)
      (⟨1,by norm_num⟩ : UnitTime)).hasFDerivAt.comp_hasDerivAt 0 hu
  have hpder : HasDerivAt (fun s => returnPoint ψ τ (d s))
      ((fderiv ℝ (returnPoint ψ τ) ((0,r),x)) ((0,0),dx)) 0 := by
    have hs := returnPoint_smooth ψ τ ((0,r),x) hτ
      (by simpa only [returnArgument,x,hτ0] using hψ)
    exact (hs.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd (by simp [d])
  have hz : H (q ⟨1,by norm_num⟩)=0 := by
    have hh := H.hasFDerivAt.comp_hasDerivAt 0 heval
    have hephase : ∀ᶠ s in 𝓝 (0:ℝ), H (returnPoint ψ τ (d s))=0 := by
      have ht : Filter.Tendsto d (𝓝 0) (𝓝 ((0,r),x)) := by
        simpa [d] using hd.continuousAt.tendsto
      exact ht.eventually hphase
    exact hh.unique (HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const (0:ℝ) (0:ℝ)) hephase)
  have htrans : H ((A0+r • D).mulVec x)=w/2 := by
    change (p (GenericComplexification.complexify ((A0+r • D).mulVec (GenericComplexification.realPart v)))).im=w/2
    rw [GenericComplexification.complexify_action,hleft,
      GenericReturnTime.normalized_eigen_real_pairing (A0+r • D) w (ne_of_gt hw) v p he hleft hnorm]
    simp [div_eq_mul_inv]
  have hnonzero : H ((A0+r • D).mulVecLin.toContinuousLinearMap x) ≠ 0 := by
    change H ((A0+r • D).mulVec x) ≠ 0
    rw [htrans]
    positivity
  have hout := GenericReturnBaseVariation.corrected_variation_endpoint
    (A0+r • D) w (ne_of_gt hw) v he H hnonzero dT dx U q hU hq' hz
  rw [heval.unique hpder] at hout
  simp only [LinearMap.coe_toContinuousLinearMap',Matrix.mulVecLin_apply] at hout
  dsimp only [x] at htrans
  rw [htrans] at hout
  exact hout

end
end ThreeSitePhosphorylation.GenericReturnBaseDerivative
