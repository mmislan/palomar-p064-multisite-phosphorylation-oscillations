import proofs.ThreeSitePhosphorylation.GenericReturnBaseDerivative

namespace ThreeSitePhosphorylation.GenericReturnBaseModes
noncomputable section
open scoped Topology
open GenericVariationalODE

variable {ι : Type*} [Fintype ι]

def realEigenPath (T eig : ℝ) (v : (ι → ℝ)) : (ContinuousPath (ι → ℝ)) :=
  ⟨fun t => Real.exp (T*eig*(t:ℝ)) • v,by fun_prop⟩

theorem realEigenPath_integral (A : Matrix ι ι ℝ) (T eig : ℝ) (v : (ι → ℝ))
    (hv : A.mulVecLin.toContinuousLinearMap v=eig • v) :
    realEigenPath T eig v=constantPath v+linearPicard (T • A.mulVecLin.toContinuousLinearMap) (realEigenPath T eig v) := by
  let g := fun t : ℝ => Real.exp (T*eig*t) • v
  have hd (t : ℝ) : HasDerivAt g ((T • A.mulVecLin.toContinuousLinearMap) (g t)) t := by
    have ht : HasDerivAt (fun s : ℝ => T*eig*s) (T*eig) t := by
      simpa using (hasDerivAt_id t).const_mul (T*eig)
    have hh := ((Real.hasDerivAt_exp (T*eig*t)).comp t ht).smul_const v
    convert hh using 1
    simp only [g,ContinuousLinearMap.smul_apply,map_smul,hv,smul_smul]
  have hc : Continuous (fun t => (T • A.mulVecLin.toContinuousLinearMap) (g t)) := by dsimp [g]; fun_prop
  apply ContinuousMap.ext
  intro t
  apply funext
  intro i
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := (t:ℝ)) (fun s _ => hd s) (hc.intervalIntegrable _ _)
  have hh : (∫ s in (0:ℝ)..(t:ℝ), (T • A.mulVecLin.toContinuousLinearMap) (pathExtension (realEigenPath T eig v) s))=
      ∫ s in (0:ℝ)..(t:ℝ), (T • A.mulVecLin.toContinuousLinearMap) (g s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Set.Icc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le t.2.1] at hs
      exact ⟨hs.1,hs.2.trans t.2.2⟩
    simp [pathExtension,Set.projIcc_of_mem _ hs',realEigenPath,g]
  change (realEigenPath T eig v t) i = (v+
    ∫ s in (0:ℝ)..(t:ℝ), (T • A.mulVecLin.toContinuousLinearMap) (pathExtension (realEigenPath T eig v) s)) i
  rw [hh,hf]
  simp [g,realEigenPath]

omit [Fintype ι] in
theorem realEigenPath_endpoint (T eig : ℝ) (v : (ι → ℝ)) :
    realEigenPath T eig v ⟨1,by norm_num⟩=Real.exp (T*eig) • v := by
  simp [realEigenPath]

theorem radial_reference_integral (A : Matrix ι ι ℝ) (w T : ℝ) (v : ι → ℂ)
    (he : (GenericComplexification.complexMatrix A).mulVec v=(Complex.I*(w:ℂ)) • v) :
    GenericLinearOrbit.referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w T = constantPath (GenericComplexification.realPart v)+
      linearPicard (T • A.mulVecLin.toContinuousLinearMap) (GenericLinearOrbit.referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w T) := by
  obtain ⟨ha,hb⟩ := GenericComplexification.source_eigen_real_imag A w v he
  rw [GenericLinearOrbit.referencePath_integral (A.mulVecLin.toContinuousLinearMap) _ _ w T ha hb]
  change _ = ContinuousMap.const UnitTime (GenericComplexification.realPart v)+(_-ContinuousMap.const UnitTime (GenericComplexification.realPart v))
  abel

theorem phase_reference_integral (A : Matrix ι ι ℝ) (w T : ℝ) (v : ι → ℂ)
    (he : (GenericComplexification.complexMatrix A).mulVec v=(Complex.I*(w:ℂ)) • v) :
    GenericLinearOrbit.referencePath (GenericComplexification.imagPart v) (-GenericComplexification.realPart v) w T = constantPath (GenericComplexification.imagPart v)+
      linearPicard (T • A.mulVecLin.toContinuousLinearMap) (GenericLinearOrbit.referencePath (GenericComplexification.imagPart v) (-GenericComplexification.realPart v) w T) := by
  obtain ⟨ha,hb⟩ := GenericComplexification.source_eigen_real_imag A w v he
  change A.mulVecLin.toContinuousLinearMap (GenericComplexification.realPart v)=
    (-w) • GenericComplexification.imagPart v at ha
  change A.mulVecLin.toContinuousLinearMap (GenericComplexification.imagPart v)=
    w • GenericComplexification.realPart v at hb
  have ha' : A.mulVecLin.toContinuousLinearMap (GenericComplexification.imagPart v)=(-w) • (-GenericComplexification.realPart v) := by rw [hb]; module
  have hb' : A.mulVecLin.toContinuousLinearMap (-GenericComplexification.realPart v)=w • GenericComplexification.imagPart v := by rw [map_neg,ha]; module
  rw [GenericLinearOrbit.referencePath_integral (A.mulVecLin.toContinuousLinearMap) _ _ w T ha' hb']
  change _ = ContinuousMap.const UnitTime (GenericComplexification.imagPart v)+(_-ContinuousMap.const UnitTime (GenericComplexification.imagPart v))
  abel

theorem normalized_eigen_imag_pairing (A : Matrix ι ι ℝ) (w : ℝ) (hw : w ≠ 0)
    (v : ι → ℂ) (p : (ι → ℂ) →ₗ[ℂ] ℂ)
    (he : (GenericComplexification.complexMatrix A).mulVec v=(Complex.I*(w:ℂ)) • v)
    (hleft : ∀ z, p ((GenericComplexification.complexMatrix A).mulVec z)=(Complex.I*(w:ℂ))*p z)
    (hnorm : p v=1) :
    p (GenericComplexification.complexify (GenericComplexification.imagPart v))= -Complex.I/2 := by
  have hh := congrArg (fun z => p (GenericComplexification.complexify z))
    (GenericComplexification.source_eigen_real_imag A w v he).1
  dsimp only at hh
  rw [GenericComplexification.complexify_action,hleft,
    GenericReturnTime.normalized_eigen_real_pairing A w hw v p he hleft hnorm,
    map_smul,LinearMap.map_smul_of_tower] at hh
  simp only [Complex.real_smul,Complex.ofReal_neg] at hh
  have hn : (w:ℂ) ≠ 0 := by exact_mod_cast hw
  apply mul_left_cancel₀ hn
  linear_combination hh

theorem real_stable_pairing_zero (A : Matrix ι ι ℝ) (w : ℝ)
    (p : (ι → ℂ) →ₗ[ℂ] ℂ)
    (hleft : ∀ z, p ((GenericComplexification.complexMatrix A).mulVec z)=(Complex.I*(w:ℂ))*p z)
    (eig : ℝ) (heig : eig<0) (x : ι → ℝ) (hx : A.mulVec x=eig • x) :
    p (GenericComplexification.complexify x)=0 := by
  have hh := congrArg (fun y => p (GenericComplexification.complexify y)) hx
  dsimp only at hh
  rw [GenericComplexification.complexify_action,hleft,map_smul,LinearMap.map_smul_of_tower] at hh
  have hn : (Complex.I*(w:ℂ))-(eig:ℂ) ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp at hr
    linarith
  apply (mul_eq_zero.mp (show ((Complex.I*(w:ℂ))-(eig:ℂ))*
      p (GenericComplexification.complexify x)=0 by
    simp only [Complex.real_smul] at hh
    linear_combination hh)).resolve_left hn

variable (A0 D : Matrix ι ι ℝ)
variable (B : ℝ → ContinuousPath (ι → ℝ) → ContinuousPath (ι → ℝ))
variable (r w : ℝ) (hw : 0<w) (v : ι → ℂ) (p : (ι → ℂ) →ₗ[ℂ] ℂ)
variable (he : (GenericComplexification.complexMatrix (A0+r • D)).mulVec v=(Complex.I*(w:ℂ)) • v)
variable (hleft : ∀ z, p ((GenericComplexification.complexMatrix (A0+r • D)).mulVec z)=
  (Complex.I*(w:ℂ))*p z) (hnorm : p v=1)
variable (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
variable (τ : GenericReturnIFT.ReturnData (ι → ℝ) → ℝ)
variable (hψ : ContDiffAt ℝ ⊤ ψ ((0,(r,2*Real.pi/w)),GenericComplexification.realPart v))
variable (hτ : ContDiffAt ℝ ⊤ τ ((0,r),GenericComplexification.realPart v))
variable (hτ0 : τ ((0,r),GenericComplexification.realPart v)=2*Real.pi/w)
variable (hres : ∀ᶠ d in 𝓝 ((0,(r,2*Real.pi/w)),GenericComplexification.realPart v),
  GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
    D.mulVecLin.toContinuousLinearMap B (d,ψ d)=0)
variable (hphase : ∀ᶠ d in 𝓝 ((0,r),GenericComplexification.realPart v),
  GenericReturnIFT.endpointPhase ψ p (d,τ d)=0)
include hw he hleft hnorm hψ hτ hτ0 hres hphase

/-- Actual return derivative on a real stable source eigenvector. -/
theorem actual_return_stable_mode (eig : ℝ) (heig : eig<0)
    (x : ι → ℝ) (hx : (A0+r • D).mulVec x=eig • x) :
    (fderiv ℝ (GenericReturnIFT.returnPoint ψ τ) ((0,r),GenericComplexification.realPart v))
      ((0,0),x)=Real.exp ((2*Real.pi/w)*eig) • x := by
  have hh := GenericReturnBaseDerivative.actual_return_state_derivative A0 D B r w hw v p
    he hleft hnorm ψ τ hψ hτ hτ0 hres hphase x (realEigenPath (2*Real.pi/w) eig x)
    (realEigenPath_integral (A0+r • D) (2*Real.pi/w) eig x hx)
  rw [realEigenPath_endpoint] at hh
  have hz := real_stable_pairing_zero (A0+r • D) w p hleft eig heig x hx
  simpa [map_smul,LinearMap.map_smul_of_tower,hz] using hh

/-- The radial critical direction has actual return eigenvalue one. -/
theorem actual_return_radial_mode :
    (fderiv ℝ (GenericReturnIFT.returnPoint ψ τ) ((0,r),GenericComplexification.realPart v))
      ((0,0),GenericComplexification.realPart v)=GenericComplexification.realPart v := by
  have hh := GenericReturnBaseDerivative.actual_return_state_derivative A0 D B r w hw v p
    he hleft hnorm ψ τ hψ hτ hτ0 hres hphase (GenericComplexification.realPart v)
    (GenericLinearOrbit.referencePath (GenericComplexification.realPart v)
      (GenericComplexification.imagPart v) w (2*Real.pi/w))
    (radial_reference_integral (A0+r • D) w (2*Real.pi/w) v he)
  rw [(GenericLinearOrbit.referencePath_endpoints (GenericComplexification.realPart v)
    (GenericComplexification.imagPart v) w (ne_of_gt hw)).2,
    GenericReturnTime.normalized_eigen_real_pairing (A0+r • D) w (ne_of_gt hw) v p he hleft hnorm] at hh
  simpa using hh

/-- Phase correction kills the actual phase direction. -/
theorem actual_return_phase_mode :
    (fderiv ℝ (GenericReturnIFT.returnPoint ψ τ) ((0,r),GenericComplexification.realPart v))
      ((0,0),GenericComplexification.imagPart v)=0 := by
  have hh := GenericReturnBaseDerivative.actual_return_state_derivative A0 D B r w hw v p
    he hleft hnorm ψ τ hψ hτ hτ0 hres hphase (GenericComplexification.imagPart v)
    (GenericLinearOrbit.referencePath (GenericComplexification.imagPart v)
      (-GenericComplexification.realPart v) w (2*Real.pi/w))
    (phase_reference_integral (A0+r • D) w (2*Real.pi/w) v he)
  rw [(GenericLinearOrbit.referencePath_endpoints (GenericComplexification.imagPart v)
    (-GenericComplexification.realPart v) w (ne_of_gt hw)).2,
    normalized_eigen_imag_pairing (A0+r • D) w (ne_of_gt hw) v p he hleft hnorm,
    (GenericComplexification.source_eigen_real_imag (A0+r • D) w v he).1] at hh
  have hc : ((-Complex.I/2).im/(w/2))*(-w)=1 := by
    norm_num
    field_simp [ne_of_gt hw]
  rw [smul_smul,hc,one_smul,sub_self] at hh
  exact hh

end
end ThreeSitePhosphorylation.GenericReturnBaseModes


