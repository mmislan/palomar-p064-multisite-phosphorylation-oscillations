import proofs.ThreeSitePhosphorylation.GenericClosedBranchVariations
import proofs.ThreeSitePhosphorylation.GenericQuadraticFourier

namespace ThreeSitePhosphorylation.GenericClosedBranchCurvature
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem periodic_mixed_resonant_balance
    (A D : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) (L : (ι → ℂ) →ₗ[ℂ] ℂ)
    (B : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (z : ℂ) (v vm : ι → ℂ) (hL : ∀ y, L (A y)=z*L y)
    (hv : L v=1) (hm : L vm=0)
    (T dr dT : ℝ) (hperiod : (T:ℂ)*z=turnFrequency)
    (u1 u2 : ℝ → (ι → ℂ)) (hcont : Continuous u1) (hp : u2 1=u2 0)
    (G : ℂ)
    (hmix : (∫ t in (0:ℝ)..1, Complex.exp (-turnFrequency*(t:ℂ))*
      L (B (GenericResonantKernel.harmonicVector v vm t) (u1 t)))=G/16)
    (hu : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u2
      ((T:ℂ) • A (u2 t)+(dT:ℂ) • A (GenericResonantKernel.harmonicVector v vm t)+
        ((T:ℂ)*(dr:ℂ)) • D (GenericResonantKernel.harmonicVector v vm t)+
        (2*(T:ℂ)) • B (GenericResonantKernel.harmonicVector v vm t) (u1 t)) t) :
    ((dT:ℂ)*z+(T:ℂ)*(dr:ℂ)*L (D v))/2+(T:ℂ)*G/8=0 := by
  let f := fun t => (2*(T:ℂ))*L (B (GenericResonantKernel.harmonicVector v vm t) (u1 t))
  have hf : Continuous f := by
    have hh : Continuous (GenericResonantKernel.harmonicVector v vm) := by unfold GenericResonantKernel.harmonicVector; fun_prop
    have hb := (B.toContinuousBilinearMap.continuous.comp hh).clm_apply hcont
    exact continuous_const.mul (L.toContinuousLinearMap.continuous.comp hb)
  let Lc := L.toContinuousLinearMap.restrictScalars ℝ
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      HasDerivAt (fun s => L (u2 s))
        (turnFrequency*L (u2 t)+
          Complex.exp (turnFrequency*(t:ℂ))*((dT:ℂ)*z+(T:ℂ)*(dr:ℂ)*L (D v))/2+
          Complex.exp (-turnFrequency*(t:ℂ))*((T:ℂ)*(dr:ℂ)*L (D vm))/2+f t) t := by
    have hh := Lc.hasFDerivAt.comp_hasDerivAt t (hu t ht)
    convert hh using 1
    change _=L ((T:ℂ) • A (u2 t)+(dT:ℂ) • A (GenericResonantKernel.harmonicVector v vm t)+
      ((T:ℂ)*(dr:ℂ)) • D (GenericResonantKernel.harmonicVector v vm t)+
      (2*(T:ℂ)) • B (GenericResonantKernel.harmonicVector v vm t) (u1 t))
    simp only [f,map_add,map_smul,smul_eq_mul,hL,GenericResonantKernel.harmonicVector,hv,hm,
      mul_one,mul_zero,add_zero]
    rw [← hperiod]
    ring
  have ho := periodic_harmonic_balance
    (((dT:ℂ)*z+(T:ℂ)*(dr:ℂ)*L (D v))/2)
    (((T:ℂ)*(dr:ℂ)*L (D vm))/2) f (fun t => L (u2 t)) hf
    (congrArg L hp) (by simpa only [mul_div_assoc] using hd)
  have hi : (∫ t in (0:ℝ)..1, Complex.exp (-turnFrequency*(t:ℂ))*f t)=
      (T:ℂ)*G/8 := by
    have he (t : ℝ) : Complex.exp (-turnFrequency*(t:ℂ))*f t=
        (2*(T:ℂ))*(Complex.exp (-turnFrequency*(t:ℂ))*
          L (B (GenericResonantKernel.harmonicVector v vm t) (u1 t))) := by dsimp [f]; ring
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul,hmix]
    ring
  rwa [hi] at ho

variable {A0 D : Matrix ι ι ℝ} {H : ℝ → GenericQuadraticTensor.Tensor ι}
variable {r w : ℝ} {v : ι → ℂ}
variable (C : GenericClosedPaths.ClosedPathFamily A0 D (GenericQuadraticTensor.pathField H) r w v)

def branchCoefficient (h11 h20 : ι → ℂ) : ℂ :=
  -2*C.left (GenericTensorBilinear.complexBilinear (H r) v h11)+
    C.left (GenericTensorBilinear.complexBilinear (H r)
      (GenericComplexification.conjugateVector v) h20)

variable (hH : ∀ i j k, ContDiff ℝ ⊤ (fun s => H s i j k))
variable (hw : 0<w)
variable (hv : (GenericComplexification.complexMatrix (A0+r • D)).mulVec v=
  (Complex.I*(w:ℂ)) • v)
variable (hcross : (C.left ((GenericComplexification.complexMatrix D).mulVec v)).re<0)
variable (hsym : ∀ i j k, H r i j k=H r i k j)
variable (hA : Function.Injective (GenericComplexification.complexMatrix (A0+r • D)).mulVecLin)
variable (hS : Function.Injective ((2*Complex.I*(w:ℂ)) •
  (LinearMap.id : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))-
    (GenericComplexification.complexMatrix (A0+r • D)).mulVecLin))
variable (h11 h20 : ι → ℂ)
variable (h11eq : (GenericComplexification.complexMatrix (A0+r • D)).mulVec h11=
  GenericTensorBilinear.complexBilinear (H r) v (GenericComplexification.conjugateVector v))
variable (h20eq : (2*Complex.I*(w:ℂ)) • h20-
  (GenericComplexification.complexMatrix (A0+r • D)).mulVec h20=
    GenericTensorBilinear.complexBilinear (H r) v v)
include hH hw hv hcross hsym hA hS h11eq h20eq

theorem closed_branch_resolvent_moments :
    GenericMixedFourierMoment.fourierMoment 0 (GenericClosedBranchVariations.firstVariationCurve C)=
      (-1/4:ℂ) • h11 ∧
    GenericMixedFourierMoment.fourierMoment 2 (GenericClosedBranchVariations.firstVariationCurve C)=
      (1/8:ℂ) • h20 := by
  exact GenericQuadraticFourier.quadratic_resolvent_moments
    (GenericComplexification.complexMatrix (A0+r • D)).mulVecLin
    (GenericTensorBilinear.complexBilinear (H r)) w hw v (GenericComplexification.conjugateVector v)
    (GenericTensorBilinear.complexBilinear_symmetric (H r) hsym _ _)
    (GenericClosedBranchVariations.firstVariationCurve C)
    (GenericClosedBranchVariations.firstVariationCurve_periodic_endpoints C hH hw hv hcross)
    (GenericClosedBranchVariations.firstVariationCurve_ode C hH hw hv hcross)
    hA hS h11 h20 h11eq h20eq

theorem closed_branch_resonant_moment :
    (∫ t in (0:ℝ)..1, Complex.exp (-turnFrequency*(t:ℂ))*
      C.left (GenericTensorBilinear.complexBilinear (H r)
        (GenericResonantKernel.harmonicVector v (GenericComplexification.conjugateVector v) t)
        (GenericClosedBranchVariations.firstVariationCurve C t)))=branchCoefficient C h11 h20/16 := by
  obtain ⟨h0,h2⟩ := closed_branch_resolvent_moments C hH hw hv hcross hsym hA hS h11 h20 h11eq h20eq
  exact GenericMixedFourierMoment.mixed_harmonic_resolvent_moment _ C.left _ _ h11 h20 _
    (GenericClosedBranchVariations.firstVariationCurve_continuous C).continuousOn h0 h2

/-- The coefficient balance is deduced from the actual periodic second ODE. -/
theorem closed_branch_second_order_balance :
    (((deriv (deriv (fun a => (C.parameters a).2.im)) 0:ℝ):ℂ)*(Complex.I*(w:ℂ))+
      ((2*Real.pi/w:ℝ):ℂ)*((deriv (deriv (fun a => (C.parameters a).2.re)) 0:ℝ):ℂ)*
        C.left ((GenericComplexification.complexMatrix D).mulVec v))/2+
      ((2*Real.pi/w:ℝ):ℂ)*branchCoefficient C h11 h20/8=0 := by
  let z : ℂ := Complex.I*(w:ℂ)
  let T : ℝ := 2*Real.pi/w
  have hm : C.left (GenericComplexification.conjugateVector v)=0 := by
    have hh := C.left_eigen (GenericComplexification.conjugateVector v)
    rw [GenericComplexification.conjugate_eigen (A0+r • D) w v hv,map_smul,smul_eq_mul] at hh
    have hz : z-(-Complex.I*(w:ℂ)) ≠ 0 := by
      intro hz
      have hi := congrArg Complex.im hz
      simp [z] at hi
      linarith
    apply (mul_eq_zero.mp (show (z-(-Complex.I*(w:ℂ)))*
        C.left (GenericComplexification.conjugateVector v)=0 by
      dsimp only [z]; linear_combination -hh)).resolve_left hz
  have ht : (T:ℂ)*z=turnFrequency := by
    dsimp [T,z,turnFrequency]
    push_cast
    field_simp
    exact div_self (by exact_mod_cast ne_of_gt hw)
  exact periodic_mixed_resonant_balance
    (GenericComplexification.complexMatrix (A0+r • D)).mulVecLin
    (GenericComplexification.complexMatrix D).mulVecLin C.left
    (GenericTensorBilinear.complexBilinear (H r)) z v (GenericComplexification.conjugateVector v)
    C.left_eigen C.left_normalized hm T
    (deriv (deriv (fun a => (C.parameters a).2.re)) 0)
    (deriv (deriv (fun a => (C.parameters a).2.im)) 0) ht
    (GenericClosedBranchVariations.firstVariationCurve C)
    (GenericClosedBranchVariations.secondVariationCurve C)
    (GenericClosedBranchVariations.firstVariationCurve_continuous C)
    (GenericClosedBranchVariations.secondVariationCurve_periodic_endpoints C hH hw hv hcross hsym)
    (branchCoefficient C h11 h20)
    (closed_branch_resonant_moment C hH hw hv hcross hsym hA hS h11 h20 h11eq h20eq)
    (GenericClosedBranchVariations.secondVariationCurve_ode C hH hw hv hcross hsym)

/-- Negative crossing and the actual normalized coefficient sign imply
negative second kinetic-parameter derivative. This is not a stability theorem. -/
theorem closed_branch_parameter_second_derivative_negative
    (hG : (branchCoefficient C h11 h20).re<0) :
    deriv (deriv (fun a => (C.parameters a).2.re)) 0<0 := by
  have hb := congrArg Complex.re
    (closed_branch_second_order_balance C hH hw hv hcross hsym hA hS h11 h20 h11eq h20eq)
  have hT : 0<2*Real.pi/w := by positivity
  simp [Complex.div_re,Complex.mul_re,Complex.mul_im] at hb
  have hratio : 2*Real.pi*w/(w*w)=2*Real.pi/w := by field_simp
  rw [hratio] at hb
  by_contra! hn
  have ha := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hT.le hn) hcross.le
  have hg := mul_neg_of_pos_of_neg hT hG
  nlinarith

end
end ThreeSitePhosphorylation.GenericClosedBranchCurvature


