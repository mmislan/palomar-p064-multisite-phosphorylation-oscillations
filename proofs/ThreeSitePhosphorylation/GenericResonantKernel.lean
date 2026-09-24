import proofs.ThreeSitePhosphorylation.ResonantBalance

/-! Dimension-independent harmonic and quadratic resonant kernel algebra.
The scalar Fourier identities are reused from the existing modules. -/
namespace ThreeSitePhosphorylation.GenericResonantKernel
noncomputable section
set_option maxHeartbeats 400000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

def harmonicVector (v vm : E) (t : ℝ) : E :=
  (Complex.exp (turnFrequency*(t:ℂ))/2) • v+
    (Complex.exp (-turnFrequency*(t:ℂ))/2) • vm

/-- The projected periodic variational equation has no nonzero parameter or
period direction when the critical eigenvalue crosses transversely. -/
theorem resonant_parameter_kernel
    (A D : E →ₗ[ℂ] E) (L : E →ₗ[ℂ] ℂ)
    (z : ℂ) (v vm : E) (hL : ∀ y, L (A y)=z*L y)
    (hv : L v=1) (hm : L vm=0) (hc : (L (D v)).re<0)
    (w T dr dT : ℝ) (hw : 0<w) (hT : 0<T)
    (hz : z=Complex.I*(w:ℂ)) (hperiod : (T:ℂ)*z=turnFrequency)
    (u : ℝ → E) (hp : u 1=u 0)
    (hu : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u
      ((T:ℂ) • A (u t)+(dT:ℂ) • A (harmonicVector v vm t)+
        ((T:ℂ)*(dr:ℂ)) • D (harmonicVector v vm t)) t) : dr=0 ∧ dT=0 := by
  let Lc := L.toContinuousLinearMap.restrictScalars ℝ
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      HasDerivAt (fun s => L (u s))
        (turnFrequency*L (u t)+
          Complex.exp (turnFrequency*(t:ℂ))*((dT:ℂ)*z+(T:ℂ)*(dr:ℂ)*L (D v))/2+
          Complex.exp (-turnFrequency*(t:ℂ))*((T:ℂ)*(dr:ℂ)*L (D vm))/2) t := by
    have hh := Lc.hasFDerivAt.comp_hasDerivAt t (hu t ht)
    convert hh using 1
    change _=L ((T:ℂ) • A (u t)+(dT:ℂ) • A (harmonicVector v vm t)+
      ((T:ℂ)*(dr:ℂ)) • D (harmonicVector v vm t))
    simp only [map_add,map_smul,smul_eq_mul,hL,harmonicVector,hv,hm,mul_one,mul_zero,add_zero]
    rw [← hperiod]
    ring
  have ho := periodic_harmonic_obstruction (((dT:ℂ)*z+(T:ℂ)*(dr:ℂ)*L (D v))/2)
    (((T:ℂ)*(dr:ℂ)*L (D vm))/2) (fun t => L (u t))
    (by simpa only [mul_div_assoc] using hd) (congrArg L hp)
  have hz0 : (T:ℂ)*(dr:ℂ)*L (D v)+(dT:ℂ)*(Complex.I*(w:ℂ))=0 := by
    rw [div_eq_zero_iff] at ho
    have hh := ho.resolve_right (by norm_num)
    rw [hz] at hh
    linear_combination hh
  exact crossing_obstruction_injective _ hc T w hT hw dr dT hz0


omit [FiniteDimensional ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem weighted_quadratic_harmonics
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E)
    (L : E →ₗ[ℂ] ℂ) (q qm : E) (t : ℝ) :
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

omit [FiniteDimensional ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
/-- A quadratic term on a first harmonic has no resonant first harmonic.
This is analytic Fourier cancellation, independent of any source coefficient. -/
theorem quadratic_resonance_zero
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E)
    (L : E →ₗ[ℂ] ℂ) (q qm : E) :
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


omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem periodic_quadratic_harmonic_obstruction (A C : ℂ)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E)
    (L : E →ₗ[ℂ] ℂ) (q qm : E) (u : ℝ → ℂ)
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


/-- Quadratic forcing of the reference harmonic has no resonant first Fourier
coefficient, so it does not change the first parameter and period obstruction. -/
theorem quadratic_resonant_parameter_kernel
    (A D : E →ₗ[ℂ] E) (L : E →ₗ[ℂ] ℂ)
    (B : E →ₗ[ℂ] E →ₗ[ℂ] E)
    (z : ℂ) (v vm : E) (hL : ∀ y, L (A y)=z*L y)
    (hv : L v=1) (hm : L vm=0) (hc : (L (D v)).re<0)
    (w T dr dT : ℝ) (hw : 0<w) (hT : 0<T)
    (hz : z=Complex.I*(w:ℂ)) (hperiod : (T:ℂ)*z=turnFrequency)
    (u : ℝ → E) (hp : u 1=u 0)
    (hu : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u
      ((T:ℂ) • A (u t)+(dT:ℂ) • A (harmonicVector v vm t)+
        ((T:ℂ)*(dr:ℂ)) • D (harmonicVector v vm t)+
        B (harmonicVector v vm t) (harmonicVector v vm t)) t) : dr=0 ∧ dT=0 := by
  let Lc := L.toContinuousLinearMap.restrictScalars ℝ
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      HasDerivAt (fun s => L (u s))
        (turnFrequency*L (u t)+
          Complex.exp (turnFrequency*(t:ℂ))*((dT:ℂ)*z+(T:ℂ)*(dr:ℂ)*L (D v))/2+
          Complex.exp (-turnFrequency*(t:ℂ))*((T:ℂ)*(dr:ℂ)*L (D vm))/2+
          L (B (harmonicVector v vm t) (harmonicVector v vm t))) t := by
    have hh := Lc.hasFDerivAt.comp_hasDerivAt t (hu t ht)
    convert hh using 1
    change _=L ((T:ℂ) • A (u t)+(dT:ℂ) • A (harmonicVector v vm t)+
      ((T:ℂ)*(dr:ℂ)) • D (harmonicVector v vm t)+
      B (harmonicVector v vm t) (harmonicVector v vm t))
    simp only [map_add,map_smul,smul_eq_mul,hL,harmonicVector,hv,hm,mul_one,mul_zero,add_zero]
    rw [← hperiod]
    ring
  have ho := periodic_quadratic_harmonic_obstruction
    (((dT:ℂ)*z+(T:ℂ)*(dr:ℂ)*L (D v))/2)
    (((T:ℂ)*(dr:ℂ)*L (D vm))/2) B L v vm (fun t => L (u t))
    (congrArg L hp) (by simpa only [mul_div_assoc] using hd)
  have hz0 : (T:ℂ)*(dr:ℂ)*L (D v)+(dT:ℂ)*(Complex.I*(w:ℂ))=0 := by
    rw [div_eq_zero_iff] at ho
    have hh := ho.resolve_right (by norm_num)
    rw [hz] at hh
    linear_combination hh
  exact crossing_obstruction_injective _ hc T w hT hw dr dT hz0


end
end ThreeSitePhosphorylation.GenericResonantKernel
