import proofs.ThreeSitePhosphorylation.ScalarODE

namespace ThreeSitePhosphorylation
noncomputable section

theorem weighted_harmonic_identity (t : ℝ) (A B : ℂ) :
    Complex.exp (-turnFrequency*(t:ℂ))*
      (Complex.exp (turnFrequency*(t:ℂ))*A+Complex.exp (-turnFrequency*(t:ℂ))*B) =
      A+Complex.exp ((-2*turnFrequency)*(t:ℂ))*B := by
  rw [mul_add,← mul_assoc,← Complex.exp_add,neg_mul,neg_add_cancel,Complex.exp_zero,one_mul,
    ← mul_assoc,← Complex.exp_add]
  congr 2
  ring

theorem weighted_harmonic_integral (A B : ℂ) :
    (∫ t in (0:ℝ)..1, Complex.exp (-turnFrequency*(t:ℂ))*
      (Complex.exp (turnFrequency*(t:ℂ))*A+Complex.exp (-turnFrequency*(t:ℂ))*B))=A := by
  simp_rw [weighted_harmonic_identity]
  rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun t : ℝ => Complex.exp ((-2*turnFrequency)*(t:ℂ))*B)).intervalIntegrable _ _),
    intervalIntegral.integral_mul_const,second_harmonic_integral]
  simp

/-- Periodic solvability kills the resonant Fourier coefficient. -/
theorem periodic_harmonic_obstruction (A B : ℂ) (u : ℝ → ℂ)
    (hu : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u
      (turnFrequency*u t+Complex.exp (turnFrequency*(t:ℂ))*A+
        Complex.exp (-turnFrequency*(t:ℂ))*B) t)
    (hp : u 1=u 0) : A=0 := by
  have hh := scalar_periodic_forcing turnFrequency turnFrequency_exp u
    (fun t => Complex.exp (turnFrequency*(t:ℂ))*A+Complex.exp (-turnFrequency*(t:ℂ))*B)
    (by simpa only [add_assoc] using hu) (by fun_prop) hp
  rwa [weighted_harmonic_integral] at hh

theorem crossing_obstruction_injective (c : ℂ) (hc : c.re<0) (T w : ℝ)
    (hT : 0<T) (hw : 0<w) (dr dT : ℝ)
    (h : (T:ℂ)*(dr:ℂ)*c+(dT:ℂ)*(Complex.I*(w:ℂ))=0) : dr=0 ∧ dT=0 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.zero_re,Complex.add_im,
    Complex.zero_im] at hre him
  have hd : dr=0 := by nlinarith [mul_neg_of_pos_of_neg hT hc]
  refine ⟨hd,?_⟩
  rw [hd] at him
  nlinarith

end
end ThreeSitePhosphorylation
