import proofs.ThreeSitePhosphorylation.GenericClosedPaths
import proofs.ThreeSitePhosphorylation.GenericAmplitudeVariation
import proofs.ThreeSitePhosphorylation.GenericTensorBilinear

namespace ThreeSitePhosphorylation.GenericClosedBranchFirstVariation
noncomputable section
open scoped Topology
open GenericComplexification GenericLinearOrbit GenericVariationalODE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def amplitudeVariationField (A D : Matrix ι ι ℝ)
    (H : ℝ → GenericQuadraticTensor.Tensor ι) (r T dr dT : ℝ)
    (u q : ContinuousPath (ι → ℝ)) : ContinuousPath (ι → ℝ) :=
  variationField A.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap
    T dr dT u q + T • GenericQuadraticTensor.pathField H r u

/-- The ODE is a consequence of the literal Volterra equation, including
the two endpoints. The tensor is not presumed to be a Hessian. -/
theorem amplitude_variational_ode (A D : Matrix ι ι ℝ)
    (H : ℝ → GenericQuadraticTensor.Tensor ι) (r T dr dT : ℝ)
    (x : ι → ℝ) (u q : ContinuousPath (ι → ℝ))
    (he : q=constantPath x+linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ))
      (amplitudeVariationField A D H r T dr dT u q))
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    HasDerivAt (integralVariation x (amplitudeVariationField A D H r T dr dT u q))
      (T • A.mulVec (integralVariation x (amplitudeVariationField A D H r T dr dT u q) t)+
        dT • A.mulVec (u ⟨t,ht⟩)+T • (dr • D.mulVec (u ⟨t,ht⟩))+
        T • GenericQuadraticTensor.field H r (u ⟨t,ht⟩)) t := by
  have hd := integralVariation_derivative x (amplitudeVariationField A D H r T dr dT u q) t
  rw [pathExtension,Set.projIcc_of_mem _ ht] at hd
  rw [integralVariation_eq x _ q he ⟨t,ht⟩]
  simpa only [amplitudeVariationField,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    variationField_apply,GenericQuadraticTensor.pathField_apply] using hd

/-- Actual quadratic amplitude forcing has no resonant first harmonic. -/
theorem amplitude_periodic_path_parameters (A D : Matrix ι ι ℝ)
    (H : ℝ → GenericQuadraticTensor.Tensor ι) (r w : ℝ) (hw : 0<w)
    (v : ι → ℂ) (hv : (GenericComplexification.complexMatrix A).mulVec v=(Complex.I*(w:ℂ)) • v)
    (p : (ι → ℂ) →ₗ[ℂ] ℂ)
    (hleft : ∀ y, p ((GenericComplexification.complexMatrix A).mulVec y)=(Complex.I*(w:ℂ))*p y)
    (hnorm : p v=1) (hcross : (p ((GenericComplexification.complexMatrix D).mulVec v)).re<0)
    (dr dT : ℝ) (dx : ι → ℝ) (q : ContinuousPath (ι → ℝ))
    (hq : q=constantPath dx+linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ))
      (amplitudeVariationField A D H r (2*Real.pi/w) dr dT
        (GenericLinearOrbit.referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w (2*Real.pi/w)) q))
    (hper : q ⟨1,by norm_num⟩=q ⟨0,by norm_num⟩) : dr=0 ∧ dT=0 := by
  let z : ℂ := Complex.I*(w:ℂ)
  let T : ℝ := 2*Real.pi/w
  let u0 := GenericLinearOrbit.referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w T
  let f := amplitudeVariationField A D H r T dr dT u0 q
  let u : ℝ → (ι → ℂ) := fun t => GenericComplexification.complexify (integralVariation dx f t)
  let B := ((T:ℂ)/2) • GenericTensorBilinear.complexBilinear (H r)
  have hp' : u 1=u 0 := by
    change GenericComplexification.complexify (integralVariation dx f 1)=GenericComplexification.complexify (integralVariation dx f 0)
    rw [integralVariation_eq dx f q hq ⟨1,by norm_num⟩,
      integralVariation_eq dx f q hq ⟨0,by norm_num⟩,hper]
  have hbase (t : UnitTime) : GenericComplexification.complexify (u0 t)=
      GenericResonantKernel.harmonicVector v (GenericComplexification.conjugateVector v) t :=
    GenericCriticalOrbit.referencePath_harmonics v w hw t
  have hquadratic (y : ι → ℝ) : GenericComplexification.complexify (GenericQuadraticTensor.field H r y)=
      (1/2:ℂ) • GenericTensorBilinear.complexBilinear (H r) (GenericComplexification.complexify y) (GenericComplexification.complexify y) := by
    rw [GenericTensorBilinear.field_eq_half_bilinear,map_smul,
      GenericTensorBilinear.complexify_realBilinear]
    ext i
    simp [Complex.real_smul]
  have hu : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u
      ((T:ℂ) • (GenericComplexification.complexMatrix A).mulVec (u t)+
        (dT:ℂ) • (GenericComplexification.complexMatrix A).mulVec
          (GenericResonantKernel.harmonicVector v (GenericComplexification.conjugateVector v) t)+
        ((T:ℂ)*(dr:ℂ)) • (GenericComplexification.complexMatrix D).mulVec
          (GenericResonantKernel.harmonicVector v (GenericComplexification.conjugateVector v) t)+
        B (GenericResonantKernel.harmonicVector v (GenericComplexification.conjugateVector v) t)
          (GenericResonantKernel.harmonicVector v (GenericComplexification.conjugateVector v) t)) t := by
    intro t ht
    have hh := GenericComplexification.complexify.hasFDerivAt.comp_hasDerivAt t
      (amplitude_variational_ode A D H r T dr dT dx u0 q hq t ht)
    simp only [map_add,map_smul,GenericComplexification.complexify_action,hquadratic,hbase] at hh
    convert hh using 1
    ext i
    simp [u,B,smul_smul,Complex.real_smul]
    ring
  have hz : z ≠ -Complex.I*(w:ℂ) := by
    intro h
    have hh := congrArg Complex.im h
    simp [z] at hh
    linarith
  have hm : p (GenericComplexification.conjugateVector v)=0 := by
    have hh := hleft (GenericComplexification.conjugateVector v)
    rw [GenericComplexification.conjugate_eigen A w v hv,map_smul,smul_eq_mul] at hh
    have hh' : (z-(-Complex.I*(w:ℂ)))*p (GenericComplexification.conjugateVector v)=0 := by
      dsimp only [z]
      linear_combination -hh
    exact (mul_eq_zero.mp hh').resolve_left (sub_ne_zero.mpr hz)
  have hT : 0<T := by dsimp [T]; positivity
  have ht : (T:ℂ)*z=turnFrequency := by
    dsimp [T,z,turnFrequency]
    push_cast
    field_simp
    exact div_self (by exact_mod_cast ne_of_gt hw)
  exact GenericResonantKernel.quadratic_resonant_parameter_kernel
    (GenericComplexification.complexMatrix A).mulVecLin (GenericComplexification.complexMatrix D).mulVecLin p B z v (GenericComplexification.conjugateVector v)
    hleft hnorm hm hcross w T dr dT hw hT rfl ht u hp' hu

/-- Differentiate the actual closed family, derive its periodic variational
ODE, and conclude vanishing of the first parameter and period derivatives. -/
theorem closed_branch_parameter_derivatives (A0 D : Matrix ι ι ℝ)
    (H : ℝ → GenericQuadraticTensor.Tensor ι)
    (hH : ∀ i j k, ContDiff ℝ ⊤ (fun r => H r i j k))
    (r w : ℝ) (hw : 0<w) (v : ι → ℂ)
    (hv : (GenericComplexification.complexMatrix (A0+r • D)).mulVec v=(Complex.I*(w:ℂ)) • v)
    (C : GenericClosedPaths.ClosedPathFamily A0 D (GenericQuadraticTensor.pathField H) r w v)
    (hcross : (C.left ((GenericComplexification.complexMatrix D).mulVec v)).re<0) :
    HasDerivAt (fun a => (C.parameters a).2.re) 0 0 ∧
      HasDerivAt (fun a => (C.parameters a).2.im) 0 0 := by
  let d := deriv C.parameters 0
  let q := deriv C.paths 0
  have hd : HasDerivAt C.parameters d 0 :=
    (C.parameters_smooth.differentiableAt (by simp)).hasDerivAt
  have hu : HasDerivAt C.paths q 0 :=
    (C.paths_smooth.differentiableAt (by simp)).hasDerivAt
  have hx : HasDerivAt (fun a => (C.parameters a).1) d.1 0 := hd.fst
  have hr : HasDerivAt (fun a => (C.parameters a).2.re) d.2.re 0 :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hd.snd
  have ht : HasDerivAt (fun a => (C.parameters a).2.im) d.2.im 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hd.snd
  have hq := GenericAmplitudeVariation.amplitude_variational_curve_equation
    A0.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap
    (GenericQuadraticTensor.pathField H)
    (fun a => (C.parameters a).2.re) (fun a => (C.parameters a).2.im)
    (fun a => (C.parameters a).1) C.paths d.2.re d.2.im d.1 q hr ht hx hu
    ((GenericQuadraticTensor.pathField_smooth H hH).differentiable (by simp) _)
    C.residual
  have hq' : q=constantPath d.1+linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ))
      (amplitudeVariationField (A0+r • D) D H r (2*Real.pi/w) d.2.re d.2.im
        (GenericLinearOrbit.referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w (2*Real.pi/w)) q) := by
    simpa [C.parameters_zero,C.paths_zero,amplitudeVariationField,
      GenericShootingInvertibility.matrix_operator_affine] using hq
  have hev := (ContinuousMap.evalCLM (R := ℝ) (M := ι → ℝ)
    (⟨1,by norm_num⟩:UnitTime)).hasFDerivAt.comp_hasDerivAt 0 hu
  have h1 : q ⟨1,by norm_num⟩=d.1 :=
    hev.unique (HasDerivAt.congr_of_eventuallyEq hx C.closed)
  have h0 : q ⟨0,by norm_num⟩=d.1 :=
    (integralVariation_eq d.1 _ q hq' ⟨0,by norm_num⟩).symm.trans
      (integralVariation_initial d.1 _)
  obtain ⟨hdr,hdt⟩ := amplitude_periodic_path_parameters (A0+r • D) D H r w hw v hv
    C.left C.left_eigen C.left_normalized hcross d.2.re d.2.im d.1 q hq' (h1.trans h0.symm)
  exact ⟨by simpa only [hdr] using hr, by simpa only [hdt] using ht⟩

end
end ThreeSitePhosphorylation.GenericClosedBranchFirstVariation
