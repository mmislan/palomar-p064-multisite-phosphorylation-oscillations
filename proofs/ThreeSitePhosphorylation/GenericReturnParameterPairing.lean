import proofs.ThreeSitePhosphorylation.GenericReturnBaseDerivative
import proofs.ThreeSitePhosphorylation.GenericCriticalOrbit
import proofs.ThreeSitePhosphorylation.HarmonicForcing

/-! Actual zero-amplitude parameter pairing of the phase-corrected return
map. The pairing is derived from the selected path residual, including the
return-time dependence; no sign or pairing identity is assumed. -/
namespace ThreeSitePhosphorylation.GenericReturnParameterPairing
noncomputable section
open scoped Topology
open GenericComplexification GenericReturnIFT GenericVariationalODE

variable {ι : Type*} [Fintype ι]

/-- First Fourier coefficient of a forced complex variational solution. -/
theorem harmonic_endpoint_pairing
    (A D : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) (L : (ι → ℂ) →ₗ[ℂ] ℂ)
    (z : ℂ) (v vm : ι → ℂ) (hL : ∀ y, L (A y)=z*L y)
    (hv : L v=1) (hm : L vm=0) (T dT : ℝ)
    (hperiod : (T:ℂ)*z=turnFrequency)
    (u : ℝ → (ι → ℂ)) (hzero : u 0=0)
    (hu : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u
      ((T:ℂ) • A (u t)+(dT:ℂ) • A (GenericResonantKernel.harmonicVector v vm t)+
        (T:ℂ) • D (GenericResonantKernel.harmonicVector v vm t)) t) :
    L (u 1)=((dT:ℂ)*z+(T:ℂ)*L (D v))/2 := by
  let Lc := L.toContinuousLinearMap.restrictScalars ℝ
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      HasDerivAt (fun s => L (u s))
        (turnFrequency*L (u t)+
          Complex.exp (turnFrequency*(t:ℂ))*(((dT:ℂ)*z+(T:ℂ)*L (D v))/2)+
          Complex.exp (-turnFrequency*(t:ℂ))*((T:ℂ)*L (D vm)/2)) t := by
    have hh := Lc.hasFDerivAt.comp_hasDerivAt t (hu t ht)
    convert hh using 1
    change _=L ((T:ℂ) • A (u t)+(dT:ℂ) • A (GenericResonantKernel.harmonicVector v vm t)+
      (T:ℂ) • D (GenericResonantKernel.harmonicVector v vm t))
    simp only [map_add,map_smul,smul_eq_mul,hL,GenericResonantKernel.harmonicVector,hv,hm,
      mul_one,mul_zero,add_zero]
    rw [← hperiod]
    ring
  have hh := scalar_integrating_factor turnFrequency (fun t => L (u t))
    (fun t => Complex.exp (turnFrequency*(t:ℂ))*(((dT:ℂ)*z+(T:ℂ)*L (D v))/2)+
      Complex.exp (-turnFrequency*(t:ℂ))*((T:ℂ)*L (D vm)/2)) 1
    (by simpa only [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1),add_assoc] using hd)
    (by fun_prop)
  rw [weighted_harmonic_integral] at hh
  simpa [turnFrequency_exp,hzero] using hh.symm

theorem conjugate_left_zero (A : Matrix ι ι ℝ) (w : ℝ) (hw : 0<w)
    (v : ι → ℂ) (he : (complexMatrix A).mulVec v=(Complex.I*(w:ℂ)) • v)
    (p : (ι → ℂ) →ₗ[ℂ] ℂ)
    (hleft : ∀ z, p ((complexMatrix A).mulVec z)=(Complex.I*(w:ℂ))*p z) :
    p (conjugateVector v)=0 := by
  have hh := hleft (conjugateVector v)
  rw [conjugate_eigen A w v he,map_smul,smul_eq_mul] at hh
  have hz : Complex.I*(w:ℂ)-(-Complex.I*(w:ℂ)) ≠ 0 := by
    intro hz
    have hi := congrArg Complex.im hz
    simp at hi
    linarith
  exact (mul_eq_zero.mp (show (Complex.I*(w:ℂ)-(-Complex.I*(w:ℂ)))*p (conjugateVector v)=0 by
    linear_combination -hh)).resolve_left hz

/-- The unit parameter variation of the actual integral equation pairs with
the normalized left functional through the crossing number only. -/
theorem variation_parameter_pairing (A D : Matrix ι ι ℝ) (w : ℝ) (hw : 0<w)
    (v : ι → ℂ) (he : (complexMatrix A).mulVec v=(Complex.I*(w:ℂ)) • v)
    (p : (ι → ℂ) →ₗ[ℂ] ℂ)
    (hleft : ∀ z, p ((complexMatrix A).mulVec z)=(Complex.I*(w:ℂ))*p z)
    (hnorm : p v=1) (dT : ℝ) (q : ContinuousPath (ι → ℝ))
    (hq : q=constantPath 0+linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ))
      (variationField A.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap
        (2*Real.pi/w) 1 dT
        (GenericLinearOrbit.referencePath (GenericComplexification.realPart v)
          (GenericComplexification.imagPart v) w (2*Real.pi/w)) q)) :
    2*(p (complexify (q ⟨1,by norm_num⟩))).re=
      (2*Real.pi/w)*(p ((complexMatrix D).mulVec v)).re := by
  let T := 2*Real.pi/w
  let u0 := GenericLinearOrbit.referencePath (GenericComplexification.realPart v)
    (GenericComplexification.imagPart v) w T
  let f := variationField A.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap
    T 1 dT u0 q
  let u : ℝ → (ι → ℂ) := fun t => complexify (integralVariation 0 f t)
  have hzero : u 0=0 := by simp [u,integralVariation_initial]
  have hbase (t : UnitTime) : complexify (u0 t)=
      GenericResonantKernel.harmonicVector v (conjugateVector v) t :=
    GenericCriticalOrbit.referencePath_harmonics v w hw t
  have hu : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u
      ((T:ℂ) • (complexMatrix A).mulVec (u t)+
        (dT:ℂ) • (complexMatrix A).mulVec
          (GenericResonantKernel.harmonicVector v (conjugateVector v) t)+
        (T:ℂ) • (complexMatrix D).mulVec
          (GenericResonantKernel.harmonicVector v (conjugateVector v) t)) t := by
    intro t ht
    have hh := complexify.hasFDerivAt.comp_hasDerivAt t
      (variational_ode A.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap
        T 1 dT 0 u0 q hq t ht)
    simp only [map_add,map_smul,one_smul,LinearMap.coe_toContinuousLinearMap',
      Matrix.mulVecLin_apply,complexify_action,hbase] at hh
    convert hh using 1
  have hm := conjugate_left_zero A w hw v he p hleft
  have ht : (T:ℂ)*(Complex.I*(w:ℂ))=turnFrequency := by
    dsimp [T,turnFrequency]
    push_cast
    field_simp
    exact div_self (by exact_mod_cast ne_of_gt hw)
  have hh := harmonic_endpoint_pairing (complexMatrix A).mulVecLin (complexMatrix D).mulVecLin p
    (Complex.I*(w:ℂ)) v (conjugateVector v) hleft hnorm hm T dT ht u hzero hu
  have hend : u 1=complexify (q ⟨1,by norm_num⟩) :=
    congrArg complexify (integralVariation_eq 0 f q hq ⟨1,by norm_num⟩)
  rw [hend] at hh
  rw [congrArg Complex.re hh]
  simp only [Matrix.mulVecLin_apply,Complex.div_ofNat_re,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im]
  ring

/-- Actual derivative of the phase-corrected return point in the kinetic
parameter at zero amplitude, paired with the normalized left functional. -/
theorem return_parameter_pairing (A0 D : Matrix ι ι ℝ)
    (B : ℝ → ContinuousPath (ι → ℝ) → ContinuousPath (ι → ℝ))
    (r w : ℝ) (hw : 0<w) (v : ι → ℂ) (p : (ι → ℂ) →ₗ[ℂ] ℂ)
    (he : (complexMatrix (A0+r • D)).mulVec v=(Complex.I*(w:ℂ)) • v)
    (hleft : ∀ z, p ((complexMatrix (A0+r • D)).mulVec z)=(Complex.I*(w:ℂ))*p z)
    (hnorm : p v=1)
    (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (τ : ReturnData (ι → ℝ) → ℝ)
    (hψ : ContDiffAt ℝ ⊤ ψ ((0,(r,2*Real.pi/w)),GenericComplexification.realPart v))
    (hτ : ContDiffAt ℝ ⊤ τ ((0,r),GenericComplexification.realPart v))
    (hτ0 : τ ((0,r),GenericComplexification.realPart v)=2*Real.pi/w)
    (hres : ∀ᶠ d in 𝓝 ((0,(r,2*Real.pi/w)),GenericComplexification.realPart v),
      GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
        D.mulVecLin.toContinuousLinearMap B (d,ψ d)=0) :
    2*(p (complexify ((fderiv ℝ (returnPoint ψ τ)
      ((0,r),GenericComplexification.realPart v)) ((0,1),0)))).re=
      (2*Real.pi/w)*(p ((complexMatrix D).mulVec v)).re := by
  let x := GenericComplexification.realPart v
  let T := 2*Real.pi/w
  have hψ0 : ψ ((0,(r,T)),x)=
      GenericLinearOrbit.referencePath x (GenericComplexification.imagPart v) w T :=
    GenericReturnTime.zero_amplitude_path_unique A0 D B r T x _ _ hres.self_of_nhds
      (GenericReturnTime.critical_reference_solution A0 D B r w T v he)
  let d : ℝ → ReturnData (ι → ℝ) := fun s => ((0,r+s),x)
  let S := fun s : ℝ => τ (d s)
  let e : ℝ → GenericShootingMap.FlowData (ι → ℝ) := fun s => ((0,(r+s,S s)),x)
  let u := fun s : ℝ => ψ (e s)
  have hrs : HasDerivAt (fun s : ℝ => r+s) 1 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_add r
  have hd : HasDerivAt d (((0:ℝ),1),(0:ι → ℝ)) 0 :=
    ((hasDerivAt_const 0 (0:ℝ)).prodMk hrs).prodMk (hasDerivAt_const 0 x)
  let dT := fderiv ℝ τ ((0,r),x) ((0,1),0)
  have hS : HasDerivAt S dT 0 :=
    (hτ.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd (by simp [d,x])
  have hS0 : S 0=T := by simpa [S,d,x,T] using hτ0
  have he' : HasDerivAt e (((0:ℝ),(1,dT)),(0:ι → ℝ)) 0 :=
    ((hasDerivAt_const 0 (0:ℝ)).prodMk (hrs.prodMk hS)).prodMk (hasDerivAt_const 0 x)
  let q := fderiv ℝ ψ ((0,(r,T)),x) ((0,(1,dT)),0)
  have hu : HasDerivAt u q 0 :=
    (hψ.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 he'
      (by simp [e,hS0,x,T])
  have hev : ∀ᶠ s in 𝓝 (0:ℝ),
      GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
        D.mulVecLin.toContinuousLinearMap B (e s,u s)=0 := by
    have hh : Filter.Tendsto e (𝓝 0) (𝓝 ((0,(r,T)),x)) := by
      simpa only [e,add_zero,hS0] using he'.continuousAt.tendsto
    exact hh.eventually hres
  have hq := GenericReturnBaseDerivative.zero_amplitude_variational_curve_equation
    A0.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap B
    (fun s => r+s) S (fun _ => x) u 1 dT 0 q hrs hS (hasDerivAt_const 0 x) hu hev
  have hu0 : u 0=GenericLinearOrbit.referencePath x (GenericComplexification.imagPart v) w T := by
    simp only [u,e,add_zero,hS0]
    exact hψ0
  have hq' : q=constantPath 0+linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ))
      (variationField (A0+r • D).mulVecLin.toContinuousLinearMap
        D.mulVecLin.toContinuousLinearMap T 1 dT
        (GenericLinearOrbit.referencePath x (GenericComplexification.imagPart v) w T) q) := by
    simp only [hu0,hS0,add_zero,← GenericShootingInvertibility.matrix_operator_affine] at hq
    exact hq
  have hpder : HasDerivAt (fun s => returnPoint ψ τ (d s))
      ((fderiv ℝ (returnPoint ψ τ) ((0,r),x)) ((0,1),0)) 0 := by
    have hs := returnPoint_smooth ψ τ ((0,r),x) hτ
      (by simpa only [returnArgument,x,hτ0] using hψ)
    exact (hs.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd (by simp [d])
  have heval : HasDerivAt (fun s => returnPoint ψ τ (d s)) (q ⟨1,by norm_num⟩) 0 :=
    (ContinuousMap.evalCLM (R := ℝ) (M := ι → ℝ)
      (⟨1,by norm_num⟩ : UnitTime)).hasFDerivAt.comp_hasDerivAt 0 hu
  rw [← heval.unique hpder]
  exact variation_parameter_pairing (A0+r • D) D w hw v he p hleft hnorm dT q hq'

/-- Negative actual crossing gives negative actual return parameter pairing. -/
theorem return_parameter_pairing_negative (A0 D : Matrix ι ι ℝ)
    (B : ℝ → ContinuousPath (ι → ℝ) → ContinuousPath (ι → ℝ))
    (r w : ℝ) (hw : 0<w) (v : ι → ℂ) (p : (ι → ℂ) →ₗ[ℂ] ℂ)
    (he : (complexMatrix (A0+r • D)).mulVec v=(Complex.I*(w:ℂ)) • v)
    (hleft : ∀ z, p ((complexMatrix (A0+r • D)).mulVec z)=(Complex.I*(w:ℂ))*p z)
    (hnorm : p v=1) (hcross : (p ((complexMatrix D).mulVec v)).re<0)
    (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (τ : ReturnData (ι → ℝ) → ℝ)
    (hψ : ContDiffAt ℝ ⊤ ψ ((0,(r,2*Real.pi/w)),GenericComplexification.realPart v))
    (hτ : ContDiffAt ℝ ⊤ τ ((0,r),GenericComplexification.realPart v))
    (hτ0 : τ ((0,r),GenericComplexification.realPart v)=2*Real.pi/w)
    (hres : ∀ᶠ d in 𝓝 ((0,(r,2*Real.pi/w)),GenericComplexification.realPart v),
      GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
        D.mulVecLin.toContinuousLinearMap B (d,ψ d)=0) :
    2*(p (complexify ((fderiv ℝ (returnPoint ψ τ)
      ((0,r),GenericComplexification.realPart v)) ((0,1),0)))).re<0 := by
  rw [return_parameter_pairing A0 D B r w hw v p he hleft hnorm ψ τ hψ hτ hτ0 hres]
  exact mul_neg_of_pos_of_neg (by positivity) hcross

end
end ThreeSitePhosphorylation.GenericReturnParameterPairing
