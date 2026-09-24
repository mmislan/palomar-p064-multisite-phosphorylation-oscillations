import proofs.ThreeSitePhosphorylation.ScalarODE

namespace ThreeSitePhosphorylation
noncomputable section

def fourierWeight (k : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (-((k : ℂ) * turnFrequency) * (t : ℂ))

def fourierMoment {n : ℕ} (k : ℤ) (u : ℝ → (Fin n → ℂ)) : Fin n → ℂ :=
  ∫ t in (0 : ℝ)..1, fourierWeight k t • u t

theorem integer_turn_exp (k : ℤ) : Complex.exp (-((k : ℂ) * turnFrequency)) = 1 := by
  simpa [turnFrequency, mul_assoc] using Complex.exp_int_mul_two_pi_mul_I (-k)

/-- An actual periodic solution determines its integer Fourier moments by
the shifted source operator. No full harmonic expansion of the solution is assumed. -/
theorem periodic_fourier_moment {n : ℕ}
    (A : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (u f : ℝ → (Fin n → ℂ))
    (hf : Continuous f) (hp : u 1 = u 0)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u (A (u t) + f t) t)
    (k : ℤ) :
    (A - ((k : ℂ) * turnFrequency) •
      (LinearMap.id : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) (fourierMoment k u) +
      fourierMoment k f = 0 := by
  let a : ℂ := (k : ℂ) * turnFrequency
  let D : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := A - a • LinearMap.id
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
  simpa [D, a, fourierMoment, fourierWeight, integer_turn_exp, hp] using hFTC

end
end ThreeSitePhosphorylation
