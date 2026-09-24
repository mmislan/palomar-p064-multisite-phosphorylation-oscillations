import proofs.ThreeSitePhosphorylation.GenericComplexification
import proofs.ThreeSitePhosphorylation.ScalarODE

/-! Periodic homogeneous kernel elimination in arbitrary finite dimension.
Stable modes are removed by their actual scalar ODE, and the remaining
negative-frequency mode by the reality of the initial state. -/
namespace ThreeSitePhosphorylation.GenericPeriodicKernel
noncomputable section
open GenericComplexification
set_option maxHeartbeats 400000

variable {ι σ : Type*} [Fintype ι] [DecidableEq σ]

def spectralValues (roots : σ → ℝ) (w : ℝ) : σ ⊕ Fin 2 → ℂ :=
  Sum.elim (fun i => (roots i:ℂ)) ![Complex.I*(w:ℂ),-Complex.I*(w:ℂ)]

theorem basis_coord_eigen {η : Type*} [DecidableEq η]
    (b : Module.Basis η ℂ (ι → ℂ)) (A : Matrix ι ι ℂ) (eig : η → ℂ)
    (he : ∀ i, A.mulVec (b i)=eig i • b i) (i : η) (v : ι → ℂ) :
    b.coord i (A.mulVec v)=eig i*b.coord i v := by
  have h : (b.coord i).comp A.mulVecLin=eig i • b.coord i := by
    apply b.ext
    intro j
    by_cases hij : i=j
    · subst j
      simp [he,Module.Basis.coord_apply]
    · simp [he,Module.Basis.coord_apply,hij]
  exact DFunLike.congr_fun h v

/-- The only periodic homogeneous solution with zero positive-frequency
coordinate and real initial value has zero initial value. The period scale
T is any positive number; no resonance equality is required for this kernel
statement. The supplied basis must be a genuine eigenbasis of the actual
complexification of the real matrix A. -/
theorem periodic_homogeneous_source_kernel (A : Matrix ι ι ℝ) (w T : ℝ)
    (hw : 0<w) (hT : 0<T) (roots : σ → ℝ) (hn : ∀ i, roots i<0)
    (b : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ))
    (he : ∀ i, (complexMatrix A).mulVec (b i)=spectralValues roots w i • b i)
    (u : ℝ → (ι → ℂ))
    (hu : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt u (T • (complexMatrix A).mulVec (u t)) t)
    (hp : u 1=u 0) (hc : b.coord (Sum.inr 0) (u 0)=0)
    (hr : imagPart (u 0)=0) : u 0=0 := by
  have hs (i : σ) : b.coord (Sum.inl i) (u 0)=0 := by
    let L := ((b.coord (Sum.inl i)).toContinuousLinearMap).restrictScalars ℝ
    have hd (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
        HasDerivAt (fun s => b.coord (Sum.inl i) (u s))
          (((T*roots i:ℝ):ℂ)*b.coord (Sum.inl i) (u t)) t := by
      have hh := L.hasFDerivAt.comp_hasDerivAt t (hu t ht)
      convert hh using 1
      change _=b.coord (Sum.inl i) (T • (complexMatrix A).mulVec (u t))
      change _=((b.coord (Sum.inl i)).restrictScalars ℝ) (T • (complexMatrix A).mulVec (u t))
      rw [map_smul]
      change _=T • b.coord (Sum.inl i) ((complexMatrix A).mulVec (u t))
      rw [basis_coord_eigen b _ _ he]
      simp [spectralValues,Complex.ofReal_mul,mul_assoc]
    exact scalar_periodic_homogeneous ((T*roots i:ℝ):ℂ)
      (negative_real_nonresonance (T*roots i) (mul_neg_of_pos_of_neg hT (hn i)))
      (fun t => b.coord (Sum.inl i) (u t)) hd (congrArg (b.coord (Sum.inl i)) hp)
  have hminus : (complexMatrix A).mulVec (u 0)=(Complex.I*((-w:ℝ):ℂ)) • u 0 := by
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
  exact real_vector_imaginary_eigen_zero A (-w) (neg_ne_zero.mpr (ne_of_gt hw)) (u 0) hr hminus

end
end ThreeSitePhosphorylation.GenericPeriodicKernel
