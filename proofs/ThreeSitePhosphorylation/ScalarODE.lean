import Mathlib

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 200000

theorem scalar_integrating_factor (a : ℂ) (u f : ℝ → ℂ) (T : ℝ)
    (hu : ∀ t ∈ Set.uIcc (0:ℝ) T, HasDerivAt u (a*u t+f t) t)
    (hf : Continuous f) :
    (∫ t in (0:ℝ)..T, Complex.exp (-a*(t:ℂ))*f t) =
      Complex.exp (-a*(T:ℂ))*u T-u 0 := by
  have hd (t : ℝ) (ht : t ∈ Set.uIcc (0:ℝ) T) :
      HasDerivAt (fun s : ℝ => Complex.exp (-a*(s:ℂ))*u s)
        (Complex.exp (-a*(t:ℂ))*f t) t := by
    have hi : HasDerivAt (fun s : ℝ => -a*(s:ℂ)) (-a) t := by
      simpa only [mul_one] using ((hasDerivAt_id (t:ℂ)).const_mul (-a)).comp_ofReal
    have he := (Complex.hasDerivAt_exp (-a*(t:ℂ))).scomp t hi
    convert he.mul (hu t ht) using 1
    simp only [Function.comp_apply, smul_eq_mul]
    ring
  have hc : Continuous (fun t : ℝ => Complex.exp (-a*(t:ℂ))*f t) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)
  simpa using h

theorem scalar_periodic_forcing (a : ℂ) (ha : Complex.exp (-a)=1)
    (u f : ℝ → ℂ) (hu : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u (a*u t+f t) t)
    (hf : Continuous f) (hp : u 1=u 0) :
    (∫ t in (0:ℝ)..1, Complex.exp (-a*(t:ℂ))*f t)=0 := by
  have hh := scalar_integrating_factor a u f 1 (by simpa using hu) hf
  simpa [ha,hp] using hh

theorem scalar_periodic_homogeneous (a : ℂ) (ha : Complex.exp (-a) ≠ 1)
    (u : ℝ → ℂ) (hu : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u (a*u t) t)
    (hp : u 1=u 0) : u 0=0 := by
  have hh := scalar_integrating_factor a u (fun _ => 0) 1
    (by simpa using hu) continuous_const
  simp only [mul_zero,intervalIntegral.integral_zero,Complex.ofReal_one,mul_one,hp] at hh
  have he : (Complex.exp (-a)-1)*u 0=0 := by linear_combination -hh
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr ha)

theorem negative_real_nonresonance (a : ℝ) (ha : a<0) : Complex.exp (-(a:ℂ)) ≠ 1 := by
  rw [← Complex.ofReal_neg,← Complex.ofReal_exp]
  intro h
  have hh : Real.exp (-a)=1 := by exact_mod_cast h
  have hz := Real.exp_injective (hh.trans (Real.exp_zero.symm))
  linarith

def turnFrequency : ℂ := 2*Real.pi*Complex.I

theorem turnFrequency_nonzero : turnFrequency ≠ 0 := by
  unfold turnFrequency
  exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero

theorem turnFrequency_exp : Complex.exp (-turnFrequency)=1 := by
  rw [Complex.exp_neg]
  simp [turnFrequency,Complex.exp_two_pi_mul_I]

theorem second_harmonic_integral :
    (∫ t in (0:ℝ)..1, Complex.exp ((-2*turnFrequency)*(t:ℂ)))=0 := by
  rw [integral_exp_mul_complex (mul_ne_zero (by norm_num) turnFrequency_nonzero)]
  have he : Complex.exp (-2*turnFrequency)=1 := by
    simpa [turnFrequency] using Complex.exp_int_mul_two_pi_mul_I (-2)
  simp only [Complex.ofReal_one,Complex.ofReal_zero,mul_one,mul_zero,Complex.exp_zero]
  rw [he]
  simp

end
end ThreeSitePhosphorylation
