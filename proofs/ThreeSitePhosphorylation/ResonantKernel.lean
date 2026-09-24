import proofs.ThreeSitePhosphorylation.HarmonicForcing

namespace ThreeSitePhosphorylation
noncomputable section

def harmonicVector (v vm : Fin 9 → ℂ) (t : ℝ) : Fin 9 → ℂ :=
  (Complex.exp (turnFrequency*(t:ℂ))/2) • v+
    (Complex.exp (-turnFrequency*(t:ℂ))/2) • vm

/-- The projected periodic variational equation has no nonzero parameter or
period direction when the critical eigenvalue crosses transversely. -/
theorem resonant_parameter_kernel
    (A D : (Fin 9 → ℂ) →ₗ[ℂ] (Fin 9 → ℂ)) (L : (Fin 9 → ℂ) →ₗ[ℂ] ℂ)
    (z : ℂ) (v vm : Fin 9 → ℂ) (hL : ∀ y, L (A y)=z*L y)
    (hv : L v=1) (hm : L vm=0) (hc : (L (D v)).re<0)
    (w T dr dT : ℝ) (hw : 0<w) (hT : 0<T)
    (hz : z=Complex.I*(w:ℂ)) (hperiod : (T:ℂ)*z=turnFrequency)
    (u : ℝ → (Fin 9 → ℂ)) (hp : u 1=u 0)
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

end
end ThreeSitePhosphorylation
