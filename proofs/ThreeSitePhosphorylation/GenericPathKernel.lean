import proofs.ThreeSitePhosphorylation.GenericPeriodicVariation
import proofs.ThreeSitePhosphorylation.GenericVariationalODE
import proofs.ThreeSitePhosphorylation.GenericCriticalOrbit

namespace ThreeSitePhosphorylation.GenericPathKernel
noncomputable section
open GenericComplexification GenericPeriodicKernel GenericResonantKernel
open GenericVariationalODE GenericLinearOrbit GenericCriticalOrbit

variable {ι σ : Type*} [Fintype ι] [DecidableEq σ]

/-- The actual integral variational equation has trivial periodic gauged
kernel. Identifying this equation with a nonlinear path derivative is a
separate obligation, not an implicit hypothesis of this theorem. -/
theorem periodic_path_kernel (A D : Matrix ι ι ℝ) (w : ℝ) (hw : 0<w)
    (roots : σ → ℝ) (hn : ∀ i, roots i<0)
    (b : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ))
    (he : ∀ i, (GenericComplexification.complexMatrix A).mulVec (b i)=GenericPeriodicKernel.spectralValues roots w i • b i)
    (hcross : (b.coord (Sum.inr 0) ((GenericComplexification.complexMatrix D).mulVec (b (Sum.inr 0)))).re<0)
    (dr dT : ℝ) (dx : ι → ℝ) (q : ContinuousPath (ι → ℝ))
    (hq : q=GenericVariationalODE.constantPath dx+linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ))
      (GenericVariationalODE.variationField A.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap
        (2*Real.pi/w) dr dT
        (GenericLinearOrbit.referencePath (GenericComplexification.realPart (b (Sum.inr 0))) (GenericComplexification.imagPart (b (Sum.inr 0))) w (2*Real.pi/w)) q))
    (hper : q ⟨1,by norm_num⟩=q ⟨0,by norm_num⟩)
    (hgauge : b.coord (Sum.inr 0) (GenericComplexification.complexify dx)=0) : dr=0 ∧ dT=0 ∧ dx=0 := by
  let v := b (Sum.inr (0:Fin 2))
  let T := 2*Real.pi/w
  let u0 := GenericLinearOrbit.referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w T
  let f := GenericVariationalODE.variationField A.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap
    T dr dT u0 q
  let u : ℝ → (ι → ℂ) := fun t => GenericComplexification.complexify (GenericVariationalODE.integralVariation dx f t)
  have hinit : u 0=GenericComplexification.complexify dx := by simp [u,GenericVariationalODE.integralVariation_initial]
  have hp : u 1=u 0 := by
    change GenericComplexification.complexify (GenericVariationalODE.integralVariation dx f 1)=GenericComplexification.complexify (GenericVariationalODE.integralVariation dx f 0)
    rw [GenericVariationalODE.integralVariation_eq dx f q hq ⟨1,by norm_num⟩,
      GenericVariationalODE.integralVariation_eq dx f q hq ⟨0,by norm_num⟩,hper]
  have hr : GenericComplexification.imagPart (u 0)=0 := by rw [hinit]; ext i; simp [GenericComplexification.imagPart]
  have hc : b.coord (Sum.inr 0) (u 0)=0 := by rwa [hinit]
  have hbase (t : UnitTime) : GenericComplexification.complexify (u0 t)=GenericResonantKernel.harmonicVector v (GenericComplexification.conjugateVector v) t :=
    GenericCriticalOrbit.referencePath_harmonics v w hw t
  have hu : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u
      ((T:ℂ) • (GenericComplexification.complexMatrix A).mulVec (u t)+
        (dT:ℂ) • (GenericComplexification.complexMatrix A).mulVec (GenericResonantKernel.harmonicVector v (GenericComplexification.conjugateVector v) t)+
        ((T:ℂ)*(dr:ℂ)) • (GenericComplexification.complexMatrix D).mulVec (GenericResonantKernel.harmonicVector v (GenericComplexification.conjugateVector v) t)) t := by
    intro t ht
    have hh := GenericComplexification.complexify.hasFDerivAt.comp_hasDerivAt t
      (GenericVariationalODE.variational_ode A.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap
        T dr dT dx u0 q hq t ht)
    simp only [map_add,map_smul,LinearMap.coe_toContinuousLinearMap',
      Matrix.mulVecLin_apply,GenericComplexification.complexify_action,hbase] at hh
    convert hh using 1
    ext i
    simp [u,f,smul_smul,mul_assoc]
  have hT : 0<T := by dsimp [T]; positivity
  have hperiod : (T:ℂ)*(Complex.I*(w:ℂ))=turnFrequency := by
    dsimp [T,turnFrequency]
    push_cast
    field_simp
    exact div_self (by exact_mod_cast ne_of_gt hw)
  obtain ⟨hdr,hdt,hzero⟩ := GenericPeriodicVariation.periodic_variation_kernel A (GenericComplexification.complexMatrix D)
    w T hw hT hperiod roots hn b he hcross dr dT u hp hr hc hu
  refine ⟨hdr,hdt,?_⟩
  rw [hinit] at hzero
  apply GenericCriticalOrbit.complexify_injective
  simpa only [map_zero] using hzero

end
end ThreeSitePhosphorylation.GenericPathKernel
