import proofs.ThreeSitePhosphorylation.FourierMoment
import proofs.ThreeSitePhosphorylation.GenericResonantKernel

namespace ThreeSitePhosphorylation.GenericMixedFourierMoment
noncomputable section
open GenericResonantKernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedSpace ℝ E]

/-- Vector-valued Fourier moment, without a prescribed coordinate index. -/
def fourierMoment (k : ℤ) (u : ℝ → E) : E :=
  ∫ t in (0:ℝ)..1, fourierWeight k t • u t

theorem fourierMoment_fin {n : ℕ} (k : ℤ) (u : ℝ → (Fin n → ℂ)) :
    fourierMoment k u=ThreeSitePhosphorylation.fourierMoment k u := rfl

theorem pure_harmonic_moment (k m : ℤ) (v : E) :
    fourierMoment k (fun t => Complex.exp (((m : ℂ)*turnFrequency)*(t : ℂ)) • v) =
      if m = k then v else 0 := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  have he (t : ℝ) : fourierWeight k t * Complex.exp (((m : ℂ)*turnFrequency)*(t : ℂ)) =
      Complex.exp ((((m-k : ℤ) : ℂ)*turnFrequency)*(t : ℂ)) := by
    unfold fourierWeight
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold fourierMoment
  simp_rw [smul_smul, he]
  rw [intervalIntegral.integral_smul_const]
  by_cases h : m = k
  · subst m
    simp
  · rw [nonzero_integer_harmonic_integral (m-k) (sub_ne_zero.mpr h)]
    simp [h]

omit [FiniteDimensional ℂ E] in
theorem moment_add (k : ℤ) (u v : ℝ → E)
    (hu : Continuous u) (hv : Continuous v) :
    fourierMoment k (fun t => u t + v t) = fourierMoment k u + fourierMoment k v := by
  have hw : Continuous (fourierWeight k) := by unfold fourierWeight; fun_prop
  unfold fourierMoment
  simp_rw [smul_add]
  apply intervalIntegral.integral_add
  · apply Continuous.intervalIntegrable
    exact hw.smul hu
  · apply Continuous.intervalIntegrable
    exact hw.smul hv


theorem mixed_harmonic_fourier_moment
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E)
    (L : E →ₗ[ℂ] ℂ) (q qm : E)
    (u : ℝ → E) (hu : ContinuousOn u (Set.Icc (0:ℝ) 1)) :
    (∫ t in (0:ℝ)..1, Complex.exp (-turnFrequency*(t:ℂ)) *
      L (B (GenericResonantKernel.harmonicVector q qm t) (u t))) =
      (1/2:ℂ)*L (B q (fourierMoment 0 u))+
        (1/2:ℂ)*L (B qm (fourierMoment 2 u)) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  let A := (L.comp (B q)).toContinuousLinearMap
  let D := (L.comp (B qm)).toContinuousLinearMap
  have hw (k : ℤ) : Continuous (fourierWeight k) := by unfold fourierWeight; fun_prop
  have hi (k : ℤ) : IntervalIntegrable (fun t => fourierWeight k t • u t)
      MeasureTheory.volume 0 1 :=
    ((hw k).continuousOn.smul hu).intervalIntegrable_of_Icc (by norm_num)
  have hA : IntervalIntegrable (fun t => A (fourierWeight 0 t • u t))
      MeasureTheory.volume 0 1 :=
    (A.continuous.comp_continuousOn ((hw 0).continuousOn.smul hu)).intervalIntegrable_of_Icc (by norm_num)
  have hD : IntervalIntegrable (fun t => D (fourierWeight 2 t • u t))
      MeasureTheory.volume 0 1 :=
    (D.continuous.comp_continuousOn ((hw 2).continuousOn.smul hu)).intervalIntegrable_of_Icc (by norm_num)
  have he (t : ℝ) : Complex.exp (-turnFrequency*(t:ℂ))*L (B (GenericResonantKernel.harmonicVector q qm t) (u t)) =
      (1/2:ℂ)*A (fourierWeight 0 t • u t)+(1/2:ℂ)*D (fourierWeight 2 t • u t) := by
    have hplus : Complex.exp (-turnFrequency*(t:ℂ))*Complex.exp (turnFrequency*(t:ℂ))=1 := by
      rw [← Complex.exp_add]
      simp
    have hminus : Complex.exp (-turnFrequency*(t:ℂ))*Complex.exp (-turnFrequency*(t:ℂ))=
        fourierWeight 2 t := by
      rw [← Complex.exp_add]
      unfold fourierWeight
      congr 1
      norm_num
      ring
    simp only [GenericResonantKernel.harmonicVector,map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
      smul_eq_mul]
    change _=(1/2:ℂ)*(fourierWeight 0 t * L (B q (u t)))+
      (1/2:ℂ)*(fourierWeight 2 t * L (B qm (u t)))
    have hw0 : fourierWeight 0 t=1 := by simp [fourierWeight]
    rw [hw0,one_mul]
    calc
      _ = (1/2:ℂ)*(Complex.exp (-turnFrequency*(t:ℂ))*Complex.exp (turnFrequency*(t:ℂ)))*
          L (B q (u t))+
        (1/2:ℂ)*(Complex.exp (-turnFrequency*(t:ℂ))*Complex.exp (-turnFrequency*(t:ℂ)))*
          L (B qm (u t)) := by ring
      _ = _ := by rw [hplus,hminus]; ring
  simp_rw [he]
  rw [intervalIntegral.integral_add (hA.const_mul _) (hD.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    A.intervalIntegral_comp_comm (hi 0),D.intervalIntegral_comp_comm (hi 2)]
  rfl

theorem mixed_harmonic_resolvent_moment
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E)
    (L : E →ₗ[ℂ] ℂ) (q qm h11 h20 : E)
    (u : ℝ → E) (hu : ContinuousOn u (Set.Icc (0:ℝ) 1))
    (h0 : fourierMoment 0 u = (-1/4:ℂ) • h11)
    (h2 : fourierMoment 2 u = (1/8:ℂ) • h20) :
    (∫ t in (0:ℝ)..1, Complex.exp (-turnFrequency*(t:ℂ)) *
      L (B (GenericResonantKernel.harmonicVector q qm t) (u t))) =
      (-2*L (B q h11)+L (B qm h20))/16 := by
  rw [mixed_harmonic_fourier_moment B L q qm u hu,h0,h2]
  simp only [map_smul,smul_eq_mul]
  ring


end
end ThreeSitePhosphorylation.GenericMixedFourierMoment
