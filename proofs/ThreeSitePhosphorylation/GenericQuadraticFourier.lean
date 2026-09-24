import proofs.ThreeSitePhosphorylation.GenericMixedFourierMoment

namespace ThreeSitePhosphorylation.GenericQuadraticFourier
noncomputable section
open GenericResonantKernel
open GenericMixedFourierMoment

variable {ι : Type*} [Fintype ι]

theorem periodic_fourier_moment
    (A : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) (u f : ℝ → (ι → ℂ))
    (hf : Continuous f) (hp : u 1 = u 0)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u (A (u t) + f t) t)
    (k : ℤ) :
    (A - ((k : ℂ) * turnFrequency) •
      (LinearMap.id : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))) (GenericMixedFourierMoment.fourierMoment k u) +
      GenericMixedFourierMoment.fourierMoment k f = 0 := by
  let a : ℂ := (k : ℂ) * turnFrequency
  let D : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) := A - a • LinearMap.id
  have huc : ContinuousOn u (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hu t ht).continuousAt.continuousWithinAt
  have hw : Continuous (fourierWeight k) := by unfold fourierWeight; fun_prop
  have hwu : IntervalIntegrable (fun t => fourierWeight k t • u t) MeasureTheory.volume 0 1 :=
    (hw.continuousOn.smul huc).intervalIntegrable_of_Icc (by norm_num)
  have hwf : IntervalIntegrable (fun t => fourierWeight k t • f t) MeasureTheory.volume 0 1 :=
    (hw.smul hf).intervalIntegrable _ _
  have hwd : IntervalIntegrable
      (fun t => D.toContinuousLinearMap (fourierWeight k t • u t)) MeasureTheory.volume 0 1 :=
    (D.toContinuousLinearMap.continuous.comp_continuousOn
      (hw.continuousOn.smul huc)).intervalIntegrable_of_Icc (by norm_num)
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => fourierWeight k s • u s)
        (D.toContinuousLinearMap (fourierWeight k t • u t) + fourierWeight k t • f t) t := by
    have hi : HasDerivAt (fun s : ℝ => -a * (s : ℂ)) (-a) t := by
      simpa only [mul_one] using ((hasDerivAt_id (t : ℂ)).const_mul (-a)).comp_ofReal
    have he := (Complex.hasDerivAt_exp (-a * (t : ℂ))).scomp t hi
    convert he.smul (hu t ht) using 1
    change D (fourierWeight k t • u t) + fourierWeight k t • f t = _
    simp only [D, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      map_smul, fourierWeight, a, Function.comp_apply, smul_eq_mul]
    module
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (by simpa using hd) (hwd.add hwf)
  rw [intervalIntegral.integral_add hwd hwf,
    D.toContinuousLinearMap.intervalIntegral_comp_comm hwu] at hFTC
  simpa [D, a, GenericMixedFourierMoment.fourierMoment, fourierWeight, integer_turn_exp, hp] using hFTC


theorem quadratic_harmonic_expansion
    (B : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (q qm : ι → ℂ) (t : ℝ) :
    B (GenericResonantKernel.harmonicVector q qm t) (GenericResonantKernel.harmonicVector q qm t) =
      Complex.exp (((2 : ℤ) : ℂ)*turnFrequency*(t : ℂ)) • ((1/4 : ℂ) • B q q) +
      Complex.exp (((0 : ℤ) : ℂ)*turnFrequency*(t : ℂ)) •
        ((1/4 : ℂ) • (B q qm+B qm q)) +
      Complex.exp (((-2 : ℤ) : ℂ)*turnFrequency*(t : ℂ)) • ((1/4 : ℂ) • B qm qm) := by
  have hplus : Complex.exp (turnFrequency*(t : ℂ))^2 =
      Complex.exp (2*turnFrequency*(t : ℂ)) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  have hminus : Complex.exp (-turnFrequency*(t : ℂ))^2 =
      Complex.exp (-2*turnFrequency*(t : ℂ)) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  have hcross : Complex.exp (turnFrequency*(t : ℂ))*Complex.exp (-turnFrequency*(t : ℂ))=1 := by
    rw [← Complex.exp_add]
    simp
  simp only [GenericResonantKernel.harmonicVector, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_ofNat, Int.cast_neg,
    Int.cast_zero, zero_mul, Complex.exp_zero, one_mul]
  linear_combination (B q q i/4)*hplus + ((B q qm i+B qm q i)/4)*hcross +
    (B qm qm i/4)*hminus

theorem quadratic_moment_zero
    (B : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (q qm : ι → ℂ) :
    GenericMixedFourierMoment.fourierMoment 0 (fun t => B (GenericResonantKernel.harmonicVector q qm t) (GenericResonantKernel.harmonicVector q qm t)) =
      (1/4 : ℂ) • (B q qm+B qm q) := by
  simp_rw [quadratic_harmonic_expansion]
  rw [GenericMixedFourierMoment.moment_add _ _ _ (by fun_prop) (by fun_prop),
    GenericMixedFourierMoment.moment_add _ _ _ (by fun_prop) (by fun_prop)]
  simp only [GenericMixedFourierMoment.pure_harmonic_moment]
  norm_num

theorem quadratic_moment_two
    (B : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (q qm : ι → ℂ) :
    GenericMixedFourierMoment.fourierMoment 2 (fun t => B (GenericResonantKernel.harmonicVector q qm t) (GenericResonantKernel.harmonicVector q qm t)) =
      (1/4 : ℂ) • B q q := by
  simp_rw [quadratic_harmonic_expansion]
  rw [GenericMixedFourierMoment.moment_add _ _ _ (by fun_prop) (by fun_prop),
    GenericMixedFourierMoment.moment_add _ _ _ (by fun_prop) (by fun_prop)]
  simp only [GenericMixedFourierMoment.pure_harmonic_moment]
  norm_num

/-- The actual periodic ODE with the one-half Hessian convention determines
the mean and second harmonic equations. Only the displayed mixed symmetry
is needed here. -/
theorem quadratic_fourier_equations
    (A : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (B : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (w : ℝ) (hw : 0<w) (q qm : ι → ℂ) (hsym : B qm q=B q qm)
    (u : ℝ → (ι → ℂ)) (hp : u 1=u 0)
    (hu : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u
      (((2*Real.pi/w:ℝ):ℂ) • A (u t)+
        (((2*Real.pi/w:ℝ):ℂ)/2) • B
          (GenericResonantKernel.harmonicVector q qm t)
          (GenericResonantKernel.harmonicVector q qm t)) t) :
    A (GenericMixedFourierMoment.fourierMoment 0 u)=(-1/4:ℂ) • B q qm ∧
      (2*Complex.I*(w:ℂ)) • GenericMixedFourierMoment.fourierMoment 2 u-
        A (GenericMixedFourierMoment.fourierMoment 2 u)=(1/8:ℂ) • B q q := by
  let T : ℂ := ((2*Real.pi/w:ℝ):ℂ)
  let A' := T • A
  let B' := (T/2) • B
  let f := fun t => B' (GenericResonantKernel.harmonicVector q qm t)
    (GenericResonantKernel.harmonicVector q qm t)
  have hf : Continuous f := by
    dsimp only [f]
    simp_rw [quadratic_harmonic_expansion]
    fun_prop
  have hd : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u (A' (u t)+f t) t := hu
  have h0 := periodic_fourier_moment A' u f hf hp hd 0
  have h2 := periodic_fourier_moment A' u f hf hp hd 2
  have hm0 := quadratic_moment_zero B' q qm
  have hm2 := quadratic_moment_two B' q qm
  change GenericMixedFourierMoment.fourierMoment 0 f=_ at hm0
  change GenericMixedFourierMoment.fourierMoment 2 f=_ at hm2
  rw [hm0] at h0
  rw [hm2] at h2
  have hT : T ≠ 0 := by
    dsimp [T]
    exact_mod_cast ne_of_gt (div_pos (mul_pos (by norm_num) Real.pi_pos) hw)
  have hturn : turnFrequency=T*(Complex.I*(w:ℂ)) := by
    have hwc : (w:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hw
    dsimp [T,turnFrequency]
    push_cast
    field_simp [hwc]
  constructor
  · ext i
    have hh := congrFun h0 i
    simp only [A',B',LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,
      Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
      Int.cast_zero,zero_mul,hsym,Pi.zero_apply] at hh
    change _=(-1/4:ℂ)*B q qm i
    apply mul_left_cancel₀ hT
    linear_combination hh
  · ext i
    have hh := congrFun h2 i
    simp only [A',B',LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,
      Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
      Int.cast_ofNat,hturn,Pi.zero_apply] at hh
    change (2*Complex.I*(w:ℂ))*GenericMixedFourierMoment.fourierMoment 2 u i-
      A (GenericMixedFourierMoment.fourierMoment 2 u) i=(1/8:ℂ)*B q q i
    apply mul_left_cancel₀ hT
    linear_combination -hh

/-- Genuine injectivity of the two resolvents identifies the moments uniquely;
the actual ODE, not a prescribed Fourier expansion, supplies their equations. -/
theorem quadratic_resolvent_moments
    (A : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (B : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (w : ℝ) (hw : 0<w) (q qm : ι → ℂ) (hsym : B qm q=B q qm)
    (u : ℝ → (ι → ℂ)) (hp : u 1=u 0)
    (hu : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u
      (((2*Real.pi/w:ℝ):ℂ) • A (u t)+
        (((2*Real.pi/w:ℝ):ℂ)/2) • B
          (GenericResonantKernel.harmonicVector q qm t)
          (GenericResonantKernel.harmonicVector q qm t)) t)
    (hA : Function.Injective A)
    (hS : Function.Injective ((2*Complex.I*(w:ℂ)) •
      (LinearMap.id : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))-A))
    (h11 h20 : ι → ℂ) (h11eq : A h11=B q qm)
    (h20eq : (2*Complex.I*(w:ℂ)) • h20-A h20=B q q) :
    GenericMixedFourierMoment.fourierMoment 0 u=(-1/4:ℂ) • h11 ∧
      GenericMixedFourierMoment.fourierMoment 2 u=(1/8:ℂ) • h20 := by
  obtain ⟨h0,h2⟩ := quadratic_fourier_equations A B w hw q qm hsym u hp hu
  constructor
  · apply hA
    simpa only [map_smul,h11eq] using h0
  · apply hS
    change (2*Complex.I*(w:ℂ)) • GenericMixedFourierMoment.fourierMoment 2 u-
      A (GenericMixedFourierMoment.fourierMoment 2 u)=
      (((2*Complex.I*(w:ℂ)) • (LinearMap.id : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))-A) ((1/8:ℂ) • h20))
    rw [map_smul]
    change _=(1/8:ℂ) • ((2*Complex.I*(w:ℂ)) • h20-A h20)
    rw [h20eq]
    exact h2

end
end ThreeSitePhosphorylation.GenericQuadraticFourier

