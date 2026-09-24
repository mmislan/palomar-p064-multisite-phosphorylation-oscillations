import proofs.ThreeSitePhosphorylation.ResonantKernel

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 400000

theorem nonzero_integer_harmonic_integral (k : ℤ) (hk : k ≠ 0) :
    (∫ t in (0:ℝ)..1, Complex.exp (((k:ℂ)*turnFrequency)*(t:ℂ)))=0 := by
  have hkn : (k:ℂ) ≠ 0 := by exact_mod_cast hk
  rw [integral_exp_mul_complex (mul_ne_zero hkn turnFrequency_nonzero)]
  have he : Complex.exp ((k:ℂ)*turnFrequency)=1 := by
    simpa [turnFrequency,mul_assoc] using Complex.exp_int_mul_two_pi_mul_I k
  simp [he]

theorem weighted_quadratic_harmonics
    (B : (Fin 9 → ℂ) →ₗ[ℂ] (Fin 9 → ℂ) →ₗ[ℂ] (Fin 9 → ℂ))
    (L : (Fin 9 → ℂ) →ₗ[ℂ] ℂ) (q qm : Fin 9 → ℂ) (t : ℝ) :
    Complex.exp (-turnFrequency*(t:ℂ))*L (B (harmonicVector q qm t) (harmonicVector q qm t)) =
      Complex.exp (turnFrequency*(t:ℂ))*(L (B q q)/4) +
      Complex.exp (-turnFrequency*(t:ℂ))*((L (B q qm)+L (B qm q))/4) +
      Complex.exp ((-3*turnFrequency)*(t:ℂ))*(L (B qm qm)/4) := by
  have hcancel : Complex.exp (-turnFrequency*(t:ℂ))*Complex.exp (turnFrequency*(t:ℂ))=1 := by
    rw [← Complex.exp_add]
    simp
  have htriple : Complex.exp (-turnFrequency*(t:ℂ))^3 =
      Complex.exp ((-3*turnFrequency)*(t:ℂ)) := by
    rw [pow_succ,pow_two,← Complex.exp_add,← Complex.exp_add]
    congr 1
    ring
  simp only [harmonicVector,map_add,map_smul,LinearMap.add_apply,
    LinearMap.smul_apply,smul_eq_mul]
  linear_combination
    (Complex.exp (turnFrequency*(t:ℂ))*L (B q q)/4 +
      Complex.exp (-turnFrequency*(t:ℂ))*(L (B q qm)+L (B qm q))/4)*hcancel +
      (L (B qm qm)/4)*htriple

/-- A quadratic term on a first harmonic has no resonant first harmonic.
This is analytic Fourier cancellation, independent of any source coefficient. -/
theorem quadratic_resonance_zero
    (B : (Fin 9 → ℂ) →ₗ[ℂ] (Fin 9 → ℂ) →ₗ[ℂ] (Fin 9 → ℂ))
    (L : (Fin 9 → ℂ) →ₗ[ℂ] ℂ) (q qm : Fin 9 → ℂ) :
    (∫ t in (0:ℝ)..1, Complex.exp (-turnFrequency*(t:ℂ))*
      L (B (harmonicVector q qm t) (harmonicVector q qm t)))=0 := by
  simp_rw [weighted_quadratic_harmonics]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [intervalIntegral.integral_mul_const]
  have h1 := nonzero_integer_harmonic_integral 1 (by norm_num)
  have hm1 := nonzero_integer_harmonic_integral (-1) (by norm_num)
  have hm3 := nonzero_integer_harmonic_integral (-3) (by norm_num)
  norm_num at h1 hm1 hm3
  simp only [neg_mul,h1,hm1,hm3,zero_mul,add_zero]

end
end ThreeSitePhosphorylation
