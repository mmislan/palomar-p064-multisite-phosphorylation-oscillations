import proofs.ThreeSitePhosphorylation.AttractingLinearFlow
import proofs.ThreeSitePhosphorylation.AttractingResolvent
import proofs.ThreeSitePhosphorylation.ScalarODE

namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section

def complexify : ReducedState →L[ℝ] (Fin 9 → ℂ) :=
  ContinuousLinearMap.pi (fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))

@[simp] theorem complexify_apply (y : ReducedState) (i : Fin 9) :
    complexify y i=(y i:ℂ) := rfl

theorem complexify_source (r : ℝ) (y : ReducedState) :
    complexify (linearPart r y)=(complexSource r).mulVec (complexify y) := by
  rw [← sourceMatrix_action]
  ext i
  simp [complexSource,Matrix.mulVec,dotProduct]

def conjugateVector (v : Fin 9 → ℂ) : Fin 9 → ℂ := fun i => star (v i)

theorem conjugate_source (r : ℝ) (v : Fin 9 → ℂ) :
    (complexSource r).mulVec (conjugateVector v)=conjugateVector ((complexSource r).mulVec v) := by
  ext i
  simp [conjugateVector,complexSource,Matrix.mulVec,dotProduct]

theorem conjugate_eigen (r w : ℝ) (v : Fin 9 → ℂ)
    (he : (complexSource r).mulVec v=(Complex.I*(w:ℂ)) • v) :
    (complexSource r).mulVec (conjugateVector v)=(-Complex.I*(w:ℂ)) • conjugateVector v := by
  rw [conjugate_source,he]
  ext i
  simp [conjugateVector]

theorem complexify_orbit (v : Fin 9 → ℂ) (θ : ℝ) :
    complexify (Real.cos θ • realPart v-Real.sin θ • imagPart v)=
      (Complex.exp ((θ:ℂ)*Complex.I)/2) • v+
      (Complex.exp (-(θ:ℂ)*Complex.I)/2) • conjugateVector v := by
  rw [Complex.exp_ofReal_mul_I,← Complex.ofReal_neg,Complex.exp_ofReal_mul_I]
  ext i
  apply Complex.ext <;>
    simp [complexify,realPart,imagPart,conjugateVector,Complex.mul_re,Complex.mul_im] <;> ring

theorem normalized_orbit_harmonics (v : Fin 9 → ℂ) (w : ℝ) (hw : w ≠ 0) (t : ℝ) :
    complexify (linearOrbit (realPart v) (imagPart v) w ((2*Real.pi/w)*t))=
      (Complex.exp (turnFrequency*(t:ℂ))/2) • v+
      (Complex.exp (-turnFrequency*(t:ℂ))/2) • conjugateVector v := by
  have ht : w*((2*Real.pi/w)*t)=2*Real.pi*t := by field_simp
  rw [linearOrbit,ht,complexify_orbit]
  congr 3 <;> simp only [turnFrequency,Complex.ofReal_mul,Complex.ofReal_ofNat] <;> ring

end
end ThreeSitePhosphorylation.AttractingWitness

namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section

theorem basis_coord_eigen {ι : Type*} (b : Module.Basis ι ℂ (Fin 9 → ℂ))
    (A : Matrix (Fin 9) (Fin 9) ℂ) (z : ι → ℂ)
    (he : ∀ i, A.mulVec (b i)=z i • b i) (i : ι) (v : Fin 9 → ℂ) :
    b.coord i (A.mulVec v)=z i*b.coord i v :=
  eigenbasis_coordinate A.mulVecLin b z he i v
theorem real_vector_imaginary_eigen_zero (r w : ℝ) (hw : w ≠ 0) (v : Fin 9 → ℂ)
    (hv : imagPart v=0)
    (he : (complexSource r).mulVec v=(Complex.I*(w:ℂ)) • v) : v=0 := by
  have hh := (source_eigen_real_imag r w v he).2
  rw [hv,map_zero] at hh
  have hr : realPart v=0 := (smul_eq_zero.mp hh.symm).resolve_left hw
  ext i
  exact Complex.ext (congrFun hr i) (congrFun hv i)

end
end ThreeSitePhosphorylation.AttractingWitness


namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section

theorem periodic_homogeneous_source_kernel (r w T : ℝ) (hw : 0<w) (hT : 0<T)
    (x : Fin 7 → ℝ) (hn : ∀ i, x i<0)
    (b : Module.Basis SpectralIndex ℂ (Fin 9 → ℂ))
    (he : ∀ i, (complexSource r).mulVec (b i)=spectralValues x w i • b i)
    (u : ℝ → (Fin 9 → ℂ))
    (hu : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt u (T • (complexSource r).mulVec (u t)) t)
    (hp : u 1=u 0) (hc : b.coord (Sum.inr 0) (u 0)=0) (hr : imagPart (u 0)=0) : u 0=0 := by
  have hs (i : Fin 7) : b.coord (Sum.inl i) (u 0)=0 := by
    let L := ((b.coord (Sum.inl i)).toContinuousLinearMap).restrictScalars ℝ
    have hd (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
        HasDerivAt (fun s => b.coord (Sum.inl i) (u s))
          (((T*x i:ℝ):ℂ)*b.coord (Sum.inl i) (u t)) t := by
      have hh := L.hasFDerivAt.comp_hasDerivAt t (hu t ht)
      convert hh using 1
      change _ = b.coord (Sum.inl i) (T • (complexSource r).mulVec (u t))
      change _ = ((b.coord (Sum.inl i)).restrictScalars ℝ) (T • (complexSource r).mulVec (u t))
      rw [map_smul]
      change _ = T • b.coord (Sum.inl i) ((complexSource r).mulVec (u t))
      rw [basis_coord_eigen b _ _ he]
      simp [spectralValues,Complex.ofReal_mul,mul_assoc]
    exact scalar_periodic_homogeneous ((T*x i:ℝ):ℂ)
      (negative_real_nonresonance (T*x i) (mul_neg_of_pos_of_neg hT (hn i)))
      (fun t => b.coord (Sum.inl i) (u t)) hd (congrArg (b.coord (Sum.inl i)) hp)
  have hminus : (complexSource r).mulVec (u 0)=(Complex.I*((-w:ℝ):ℂ)) • u 0 := by
    apply sub_eq_zero.mp
    apply (b.forall_coord_eq_zero_iff).mp
    intro i
    rw [map_sub,map_smul,basis_coord_eigen b _ _ he]
    cases i with
    | inl i => simp [hs]
    | inr j =>
      fin_cases j
      · simp [hc]
      · simp [spectralValues]
  exact real_vector_imaginary_eigen_zero r (-w) (neg_ne_zero.mpr (ne_of_gt hw)) (u 0) hr hminus

end
end ThreeSitePhosphorylation.AttractingWitness

