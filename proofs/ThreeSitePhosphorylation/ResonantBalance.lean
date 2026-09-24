import proofs.ThreeSitePhosphorylation.QuadraticHarmonics

namespace ThreeSitePhosphorylation
noncomputable section

/-- The first Fourier coefficient of an arbitrary continuous forcing balances
the resonant parameter forcing. This also applies to higher branch variations. -/
theorem periodic_harmonic_balance (A B : ℂ) (f u : ℝ → ℂ)
    (hf : Continuous f) (hp : u 1=u 0)
    (hu : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u
      (turnFrequency*u t+Complex.exp (turnFrequency*(t:ℂ))*A+
        Complex.exp (-turnFrequency*(t:ℂ))*B+f t) t) :
    A+(∫ t in (0:ℝ)..1, Complex.exp (-turnFrequency*(t:ℂ))*f t)=0 := by
  have h := scalar_periodic_forcing turnFrequency turnFrequency_exp u
    (fun t => Complex.exp (turnFrequency*(t:ℂ))*A+
      Complex.exp (-turnFrequency*(t:ℂ))*B+f t)
    (by intro t ht; convert hu t ht using 1; ring) (by fun_prop) hp
  have he (t : ℝ) : Complex.exp (-turnFrequency*(t:ℂ))*
      (Complex.exp (turnFrequency*(t:ℂ))*A+Complex.exp (-turnFrequency*(t:ℂ))*B+f t) =
      Complex.exp (-turnFrequency*(t:ℂ))*
        (Complex.exp (turnFrequency*(t:ℂ))*A+Complex.exp (-turnFrequency*(t:ℂ))*B)+
      Complex.exp (-turnFrequency*(t:ℂ))*f t := by ring
  simp_rw [he] at h
  rw [intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),weighted_harmonic_integral] at h
  exact h

theorem periodic_quadratic_harmonic_obstruction (A C : ℂ)
    (B : (Fin 9 → ℂ) →ₗ[ℂ] (Fin 9 → ℂ) →ₗ[ℂ] (Fin 9 → ℂ))
    (L : (Fin 9 → ℂ) →ₗ[ℂ] ℂ) (q qm : Fin 9 → ℂ) (u : ℝ → ℂ)
    (hp : u 1=u 0)
    (hu : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u
      (turnFrequency*u t+Complex.exp (turnFrequency*(t:ℂ))*A+
        Complex.exp (-turnFrequency*(t:ℂ))*C+
        L (B (harmonicVector q qm t) (harmonicVector q qm t))) t) : A=0 := by
  have hcont : Continuous (fun t : ℝ => L (B (harmonicVector q qm t) (harmonicVector q qm t))) := by
    have hb := B.toContinuousBilinearMap.continuous
    have hL := L.toContinuousLinearMap.continuous
    have hh : Continuous (harmonicVector q qm) := by unfold harmonicVector; fun_prop
    exact hL.comp ((hb.comp hh).clm_apply hh)
  have h := periodic_harmonic_balance A C _ u hcont hp hu
  simpa only [quadratic_resonance_zero,add_zero] using h

end
end ThreeSitePhosphorylation
