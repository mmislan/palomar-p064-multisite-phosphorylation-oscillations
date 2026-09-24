import proofs.ThreeSitePhosphorylation.GenericClosedBranchFirstVariation
import proofs.ThreeSitePhosphorylation.GenericTensorSecondVariation

namespace ThreeSitePhosphorylation.GenericClosedBranchVariations
noncomputable section
open scoped Topology
open GenericVariationalODE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A0 D : Matrix ι ι ℝ} {H : ℝ → GenericQuadraticTensor.Tensor ι}
variable {r w : ℝ} {v : ι → ℂ}
variable (C : GenericClosedPaths.ClosedPathFamily A0 D (GenericQuadraticTensor.pathField H) r w v)

def firstVariationForcing : ContinuousPath (ι → ℝ) :=
  (2*Real.pi/w) • GenericAffinePathResidual.pathLinear
    A0.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap r (deriv C.paths 0)+
  (2*Real.pi/w) • GenericQuadraticTensor.pathField H r (C.paths 0)

def firstVariationCurve : ℝ → (ι → ℂ) := fun t =>
  GenericComplexification.complexify
    (integralVariation (deriv C.parameters 0).1 (firstVariationForcing C) t)

def secondVariationForcing : ContinuousPath (ι → ℝ) :=
  (2*Real.pi/w) • GenericAffinePathResidual.pathLinear
    A0.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap r (deriv (deriv C.paths) 0)+
  deriv (deriv (fun a => (C.parameters a).2.im)) 0 • GenericAffinePathResidual.pathLinear
    A0.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap r (C.paths 0)+
  (2*Real.pi/w) • (deriv (deriv (fun a => (C.parameters a).2.re)) 0 •
    D.mulVecLin.toContinuousLinearMap.compLeftContinuous ℝ UnitTime (C.paths 0))+
  (2*(2*Real.pi/w)) • GenericTensorSecondVariation.pathHessian (H r)
    (C.paths 0) (deriv C.paths 0)

def secondVariationCurve : ℝ → (ι → ℂ) := fun t =>
  GenericComplexification.complexify (integralVariation
    (deriv (deriv (fun a => (C.parameters a).1)) 0) (secondVariationForcing C) t)

theorem firstVariationCurve_continuous : Continuous (firstVariationCurve C) := by
  have hd : Differentiable ℝ (integralVariation (deriv C.parameters 0).1 (firstVariationForcing C)) :=
    fun t => (integralVariation_derivative _ _ t).differentiableAt
  exact GenericComplexification.complexify.continuous.comp hd.continuous

theorem secondVariationCurve_continuous : Continuous (secondVariationCurve C) := by
  have hd : Differentiable ℝ (integralVariation
      (deriv (deriv (fun a => (C.parameters a).1)) 0) (secondVariationForcing C)) :=
    fun t => (integralVariation_derivative _ _ t).differentiableAt
  exact GenericComplexification.complexify.continuous.comp hd.continuous

variable (hH : ∀ i j k, ContDiff ℝ ⊤ (fun r => H r i j k))
variable (hw : 0<w)
variable (hv : (GenericComplexification.complexMatrix (A0+r • D)).mulVec v=
  (Complex.I*(w:ℂ)) • v)
variable (hcross : (C.left ((GenericComplexification.complexMatrix D).mulVec v)).re<0)
include hH hw hv hcross

theorem firstVariation_integral :
    deriv C.paths 0=constantPath (deriv C.parameters 0).1+
      linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ)) (firstVariationForcing C) := by
  have hd := (C.parameters_smooth.differentiableAt (by simp)).hasDerivAt
  have hu := (C.paths_smooth.differentiableAt (by simp)).hasDerivAt
  obtain ⟨hr,ht⟩ := GenericClosedBranchFirstVariation.closed_branch_parameter_derivatives
    A0 D H hH r w hw v hv C hcross
  have hq := GenericAmplitudeVariation.amplitude_variational_curve_equation
    A0.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap
    (GenericQuadraticTensor.pathField H)
    (fun a => (C.parameters a).2.re) (fun a => (C.parameters a).2.im)
    (fun a => (C.parameters a).1) C.paths 0 0 (deriv C.parameters 0).1 (deriv C.paths 0)
    hr ht hd.fst hu ((GenericQuadraticTensor.pathField_smooth H hH).differentiable (by simp) _)
    C.residual
  simpa [C.parameters_zero,firstVariationForcing,variationField,
    GenericAffinePathResidual.pathLinear] using hq

theorem firstVariationCurve_periodic_endpoints :
    firstVariationCurve C 1=firstVariationCurve C 0 := by
  have hd := (C.parameters_smooth.differentiableAt (by simp)).hasDerivAt
  have hu := (C.paths_smooth.differentiableAt (by simp)).hasDerivAt
  have hev := (ContinuousMap.evalCLM (R := ℝ) (M := ι → ℝ)
    (⟨1,by norm_num⟩:UnitTime)).hasFDerivAt.comp_hasDerivAt 0 hu
  have h1 : deriv C.paths 0 ⟨1,by norm_num⟩=(deriv C.parameters 0).1 :=
    hev.unique (HasDerivAt.congr_of_eventuallyEq hd.fst C.closed)
  unfold firstVariationCurve
  rw [integralVariation_eq _ _ _ (firstVariation_integral C hH hw hv hcross)
    ⟨1,by norm_num⟩,integralVariation_initial,h1]

theorem firstVariationCurve_ode (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    HasDerivAt (firstVariationCurve C)
      (((2*Real.pi/w:ℝ):ℂ) • (GenericComplexification.complexMatrix (A0+r • D)).mulVec
        (firstVariationCurve C t)+(((2*Real.pi/w:ℝ):ℂ)/2) •
        GenericTensorBilinear.complexBilinear (H r)
          (GenericResonantKernel.harmonicVector v (GenericComplexification.conjugateVector v) t)
          (GenericResonantKernel.harmonicVector v (GenericComplexification.conjugateVector v) t)) t := by
  have hd := integralVariation_derivative (deriv C.parameters 0).1 (firstVariationForcing C) t
  rw [pathExtension,Set.projIcc_of_mem _ ht] at hd
  have hc := GenericComplexification.complexify.hasFDerivAt.comp_hasDerivAt t hd
  have hb : GenericComplexification.complexify (C.paths 0 ⟨t,ht⟩)=
      GenericResonantKernel.harmonicVector v (GenericComplexification.conjugateVector v) t := by
    rw [C.paths_zero]
    exact GenericCriticalOrbit.referencePath_harmonics v w hw ⟨t,ht⟩
  have h1 : GenericComplexification.complexify (deriv C.paths 0 ⟨t,ht⟩)=firstVariationCurve C t := by
    unfold firstVariationCurve
    rw [integralVariation_eq _ _ _ (firstVariation_integral C hH hw hv hcross) ⟨t,ht⟩]
  have hlin (y : ContinuousPath (ι → ℝ)) :
      GenericAffinePathResidual.pathLinear A0.mulVecLin.toContinuousLinearMap
        D.mulVecLin.toContinuousLinearMap r y ⟨t,ht⟩=(A0+r • D).mulVec (y ⟨t,ht⟩) := by
    rw [GenericAffinePathResidual.pathLinear,← GenericShootingInvertibility.matrix_operator_affine]
    rfl
  simp only [firstVariationForcing,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    hlin,GenericQuadraticTensor.pathField_apply,GenericTensorBilinear.field_eq_half_bilinear,
    map_add,map_smul,GenericComplexification.complexify_action,
    GenericTensorBilinear.complexify_realBilinear,hb,h1] at hc
  convert hc using 1
  apply funext
  intro i
  simp [firstVariationCurve,Pi.smul_apply,Complex.real_smul]
  ring

variable (hsym : ∀ i j k, H r i j k=H r i k j)
include hsym

theorem secondVariation_integral :
    deriv (deriv C.paths) 0=constantPath (deriv (deriv (fun a => (C.parameters a).1)) 0)+
      linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ)) (secondVariationForcing C) := by
  obtain ⟨hr,ht⟩ := GenericClosedBranchFirstVariation.closed_branch_parameter_derivatives
    A0 D H hH r w hw v hv C hcross
  have hR := Complex.reCLM.contDiff.contDiffAt.comp 0 C.parameters_smooth.snd
  have hT := Complex.imCLM.contDiff.contDiffAt.comp 0 C.parameters_smooth.snd
  have hsym' : ∀ i j k, H (C.parameters 0).2.re i j k=H (C.parameters 0).2.re i k j := by
    simpa [C.parameters_zero] using hsym
  have hh := GenericTensorSecondVariation.second_variational_curve_equation
    A0.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap H hH
    (fun a => (C.parameters a).2.re) (fun a => (C.parameters a).2.im)
    (fun a => (C.parameters a).1) C.paths hR hT C.parameters_smooth.fst C.paths_smooth
    hr.deriv ht.deriv hsym' C.residual
  simpa [C.parameters_zero,secondVariationForcing] using hh

theorem secondVariationCurve_periodic_endpoints :
    secondVariationCurve C 1=secondVariationCurve C 0 := by
  let ev := ContinuousMap.evalCLM (R := ℝ) (M := ι → ℝ) (⟨1,by norm_num⟩:UnitTime)
  have he : (fun a => ev (C.paths a)) =ᶠ[𝓝 (0:ℝ)] fun a => (C.parameters a).1 := C.closed
  have h1 := he.deriv.deriv_eq
  rw [GenericTensorSecondVariation.second_deriv_clm ev C.paths C.paths_smooth] at h1
  unfold secondVariationCurve
  rw [integralVariation_eq _ _ _ (secondVariation_integral C hH hw hv hcross hsym)
    ⟨1,by norm_num⟩,integralVariation_initial]
  exact congrArg GenericComplexification.complexify h1

theorem secondVariationCurve_ode (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    HasDerivAt (secondVariationCurve C)
      (((2*Real.pi/w:ℝ):ℂ) • (GenericComplexification.complexMatrix (A0+r • D)).mulVec
        (secondVariationCurve C t)+
        ((deriv (deriv (fun a => (C.parameters a).2.im)) 0:ℝ):ℂ) •
          (GenericComplexification.complexMatrix (A0+r • D)).mulVec
            (GenericResonantKernel.harmonicVector v (GenericComplexification.conjugateVector v) t)+
        (((2*Real.pi/w:ℝ):ℂ)*((deriv (deriv (fun a => (C.parameters a).2.re)) 0:ℝ):ℂ)) •
          (GenericComplexification.complexMatrix D).mulVec
            (GenericResonantKernel.harmonicVector v (GenericComplexification.conjugateVector v) t)+
        (2*((2*Real.pi/w:ℝ):ℂ)) • GenericTensorBilinear.complexBilinear (H r)
          (GenericResonantKernel.harmonicVector v (GenericComplexification.conjugateVector v) t)
          (firstVariationCurve C t)) t := by
  have hd := integralVariation_derivative
    (deriv (deriv (fun a => (C.parameters a).1)) 0) (secondVariationForcing C) t
  rw [pathExtension,Set.projIcc_of_mem _ ht] at hd
  have hc := GenericComplexification.complexify.hasFDerivAt.comp_hasDerivAt t hd
  have hb : GenericComplexification.complexify (C.paths 0 ⟨t,ht⟩)=
      GenericResonantKernel.harmonicVector v (GenericComplexification.conjugateVector v) t := by
    rw [C.paths_zero]
    exact GenericCriticalOrbit.referencePath_harmonics v w hw ⟨t,ht⟩
  have h1 : GenericComplexification.complexify (deriv C.paths 0 ⟨t,ht⟩)=firstVariationCurve C t := by
    unfold firstVariationCurve
    rw [integralVariation_eq _ _ _ (firstVariation_integral C hH hw hv hcross) ⟨t,ht⟩]
  have h2 : GenericComplexification.complexify (deriv (deriv C.paths) 0 ⟨t,ht⟩)=
      secondVariationCurve C t := by
    unfold secondVariationCurve
    rw [integralVariation_eq _ _ _ (secondVariation_integral C hH hw hv hcross hsym) ⟨t,ht⟩]
  have hlin (y : ContinuousPath (ι → ℝ)) :
      GenericAffinePathResidual.pathLinear A0.mulVecLin.toContinuousLinearMap
        D.mulVecLin.toContinuousLinearMap r y ⟨t,ht⟩=(A0+r • D).mulVec (y ⟨t,ht⟩) := by
    rw [GenericAffinePathResidual.pathLinear,← GenericShootingInvertibility.matrix_operator_affine]
    rfl
  have hD : D.mulVecLin.toContinuousLinearMap.compLeftContinuous ℝ UnitTime (C.paths 0) ⟨t,ht⟩=
      D.mulVec (C.paths 0 ⟨t,ht⟩) := rfl
  simp only [secondVariationForcing,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    hlin,hD,GenericTensorSecondVariation.pathHessian_apply,
    GenericTensorDerivative.realContinuousBilinear_apply,map_add,map_smul,
    GenericComplexification.complexify_action,GenericTensorBilinear.complexify_realBilinear,
    hb,h1,h2] at hc
  convert hc using 1
  apply funext
  intro i
  simp [secondVariationCurve,Pi.smul_apply,Complex.real_smul,smul_smul]

end
end ThreeSitePhosphorylation.GenericClosedBranchVariations

