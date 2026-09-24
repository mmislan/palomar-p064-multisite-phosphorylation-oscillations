import proofs.ThreeSitePhosphorylation.GenericPeriodicKernel
import proofs.ThreeSitePhosphorylation.GenericResonantKernel

/-! Parameter, period and initial-state kernel elimination from the actual
periodic variational ODE. The crossing and source eigenbasis remain inputs. -/
namespace ThreeSitePhosphorylation.GenericPeriodicVariation
noncomputable section
open GenericComplexification GenericPeriodicKernel GenericResonantKernel

variable {ι σ : Type*} [Fintype ι] [DecidableEq σ]

theorem periodic_variation_kernel (A : Matrix ι ι ℝ) (D : Matrix ι ι ℂ)
    (w T : ℝ) (hw : 0<w) (hT : 0<T)
    (hperiod : (T:ℂ)*(Complex.I*(w:ℂ))=turnFrequency)
    (roots : σ → ℝ) (hn : ∀ i, roots i<0)
    (b : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ))
    (he : ∀ i, (complexMatrix A).mulVec (b i)=spectralValues roots w i • b i)
    (hcross : (b.coord (Sum.inr 0) (D.mulVec (b (Sum.inr 0)))).re<0)
    (dr dT : ℝ) (u : ℝ → (ι → ℂ)) (hper : u 1=u 0)
    (hr : imagPart (u 0)=0) (hc : b.coord (Sum.inr 0) (u 0)=0)
    (hu : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u
      ((T:ℂ) • (complexMatrix A).mulVec (u t)+
        (dT:ℂ) • (complexMatrix A).mulVec
          (GenericResonantKernel.harmonicVector (b (Sum.inr 0)) (GenericComplexification.conjugateVector (b (Sum.inr 0))) t)+
        ((T:ℂ)*(dr:ℂ)) • D.mulVec
          (GenericResonantKernel.harmonicVector (b (Sum.inr 0)) (GenericComplexification.conjugateVector (b (Sum.inr 0))) t)) t) :
    dr=0 ∧ dT=0 ∧ u 0=0 := by
  let z : ℂ := Complex.I*(w:ℂ)
  let v := b (Sum.inr (0:Fin 2))
  have hv : (complexMatrix A).mulVec v=z • v := by
    simpa [v,z,spectralValues] using he (Sum.inr (0:Fin 2))
  have hleft (y : ι → ℂ) : b.coord (Sum.inr 0) ((complexMatrix A).mulVec y)=
      z*b.coord (Sum.inr 0) y := by
    simpa [z,spectralValues] using GenericPeriodicKernel.basis_coord_eigen b (complexMatrix A) _ he (Sum.inr 0) y
  have hnorm : b.coord (Sum.inr 0) v=1 := by simp [v,Module.Basis.coord_apply]
  have hz : z ≠ -Complex.I*(w:ℂ) := by
    intro hh
    have hi := congrArg Complex.im hh
    simp [z] at hi
    linarith
  have hm : b.coord (Sum.inr 0) (GenericComplexification.conjugateVector v)=0 := by
    have hh := hleft (GenericComplexification.conjugateVector v)
    rw [GenericComplexification.conjugate_eigen A w v hv,map_smul,smul_eq_mul] at hh
    have hmul : (z-(-Complex.I*(w:ℂ)))*b.coord (Sum.inr 0) (GenericComplexification.conjugateVector v)=0 := by
      linear_combination -hh
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hz)
  obtain ⟨hdr,hdt⟩ := GenericResonantKernel.resonant_parameter_kernel (complexMatrix A).mulVecLin D.mulVecLin
    (b.coord (Sum.inr 0)) z v (GenericComplexification.conjugateVector v) hleft hnorm hm hcross
    w T dr dT hw hT rfl hperiod u hper hu
  have hhom : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt u (T • (complexMatrix A).mulVec (u t)) t := by
    intro t ht
    have hh := hu t ht
    simp only [hdr,hdt,Complex.ofReal_zero,zero_smul,mul_zero,add_zero] at hh
    convert hh using 1
  exact ⟨hdr,hdt,GenericPeriodicKernel.periodic_homogeneous_source_kernel A w T hw hT roots hn b he
    u hhom hper hc hr⟩

end
end ThreeSitePhosphorylation.GenericPeriodicVariation
