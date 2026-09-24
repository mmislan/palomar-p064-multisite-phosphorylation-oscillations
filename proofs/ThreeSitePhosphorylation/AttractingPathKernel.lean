import proofs.ThreeSitePhosphorylation.AttractingComplexOrbit
import proofs.ThreeSitePhosphorylation.AttractingVariationalODE
import proofs.ThreeSitePhosphorylation.AttractingPairing
import proofs.ThreeSitePhosphorylation.ResonantKernel

namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section

def sourceDelta : Matrix (Fin 9) (Fin 9) ℂ := complexSource 1-complexSource 0

end
end ThreeSitePhosphorylation.AttractingWitness
namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section

theorem source_periodic_variation_kernel (r w : ℝ) (hw : 0<w)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0)
    (roots : Fin 7 → ℝ) (hn : ∀ i, roots i<0)
    (b : Module.Basis SpectralIndex ℂ (Fin 9 → ℂ))
    (hb : ∀ i, b i=adjugateVector (spectralValues roots w i))
    (he : ∀ i, (complexSource r).mulVec (b i)=spectralValues roots w i • b i)
    (dr dT : ℝ)
    (u : ℝ → (Fin 9 → ℂ)) (hper : u 1=u 0) (hr : imagPart (u 0)=0)
    (hc : b.coord (Sum.inr 0) (u 0)=0)
    (hu : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u
      (((2*Real.pi/w:ℝ):ℂ) • (complexSource r).mulVec (u t)+
        (dT:ℂ) • (complexSource r).mulVec
          (harmonicVector (adjugateVector (Complex.I*(w:ℂ)))
            (conjugateVector (adjugateVector (Complex.I*(w:ℂ)))) t)+
        (((2*Real.pi/w:ℝ):ℂ)*(dr:ℂ)) • sourceDelta.mulVec
          (harmonicVector (adjugateVector (Complex.I*(w:ℂ)))
            (conjugateVector (adjugateVector (Complex.I*(w:ℂ)))) t)) t) :
    dr=0 ∧ dT=0 ∧ u 0=0 := by
  let z : ℂ := Complex.I*(w:ℂ)
  let v := adjugateVector z
  have hz : z ≠ -Complex.I*(w:ℂ) := by
    intro h
    have hh := congrArg Complex.im h
    simp [z] at hh
    linarith
  have hv := (source_root_eigenvector r z hp).2
  have hleft := (source_left_eigenfunctional r w roots b he).2
  have hb0 : b (Sum.inr 0)=v := by simpa [v,z,spectralValues] using hb (Sum.inr 0)
  have hnorm : b.coord (Sum.inr 0) v=1 := by
    rw [← hb0]
    exact (source_left_eigenfunctional r w roots b he).1
  have hm : b.coord (Sum.inr 0) (conjugateVector v)=0 := by
    have hh := hleft (conjugateVector v)
    rw [conjugate_eigen r w v hv,map_smul,smul_eq_mul] at hh
    have hh' : (z-(-Complex.I*(w:ℂ)))*b.coord (Sum.inr 0) (conjugateVector v)=0 := by
      dsimp only [z]
      linear_combination -hh
    exact (mul_eq_zero.mp hh').resolve_left (sub_ne_zero.mpr hz)
  have hcross : (b.coord (Sum.inr 0) (sourceDelta.mulVec v)).re < 0 := by
    have hh := source_parameter_pairing_negative r w (ne_of_gt hw) hp
      (b.coord (Sum.inr 0)) hleft hnorm
    simpa [sourceDelta,sourceOperator_apply,ContinuousLinearMap.sub_apply,
      Matrix.sub_mulVec,v,z] using hh
  have hT : 0<2*Real.pi/w := by positivity
  have ht : ((2*Real.pi/w:ℝ):ℂ)*z=turnFrequency := by
    dsimp [z,turnFrequency]
    push_cast
    field_simp
    exact div_self (by exact_mod_cast ne_of_gt hw)
  obtain ⟨hdr,hdt⟩ := resonant_parameter_kernel (complexSource r).mulVecLin
    sourceDelta.mulVecLin (b.coord (Sum.inr 0)) z v (conjugateVector v)
    hleft hnorm hm hcross w (2*Real.pi/w) dr dT hw hT rfl ht u hper hu
  have hhom : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt u ((2*Real.pi/w) • (complexSource r).mulVec (u t)) t := by
    intro t ht'
    have hh := hu t ht'
    simp only [hdr,hdt,Complex.ofReal_zero,zero_smul,mul_zero,add_zero] at hh
    convert hh using 1
  exact ⟨hdr,hdt,periodic_homogeneous_source_kernel r w (2*Real.pi/w) hw hT roots hn b he
    u hhom hper hc hr⟩

end
end ThreeSitePhosphorylation.AttractingWitness
namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section

theorem complexify_delta (y : ReducedState) :
    complexify ((linearPart 1-linearPart 0) y)=sourceDelta.mulVec (complexify y) := by
  simp only [ContinuousLinearMap.sub_apply,map_sub,complexify_source,sourceDelta,Matrix.sub_mulVec]

theorem periodic_path_kernel (r w : ℝ) (hw : 0<w)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0)
    (roots : Fin 7 → ℝ) (hn : ∀ i, roots i<0)
    (b : Module.Basis SpectralIndex ℂ (Fin 9 → ℂ))
    (hb : ∀ i, b i=adjugateVector (spectralValues roots w i))
    (he : ∀ i, (complexSource r).mulVec (b i)=spectralValues roots w i • b i)
    (dr dT : ℝ) (dx : ReducedState) (q : SourcePath)
    (hq : q=constantPath dx+linearPicard (ContinuousLinearMap.id ℝ ReducedState)
      (variationField r (2*Real.pi/w) dr dT
        (referencePath (realPart (adjugateVector (Complex.I*(w:ℂ))))
          (imagPart (adjugateVector (Complex.I*(w:ℂ)))) w (2*Real.pi/w)) q))
    (hper : q ⟨1,by norm_num⟩=q ⟨0,by norm_num⟩)
    (hgauge : b.coord (Sum.inr 0) (complexify dx)=0) : dr=0 ∧ dT=0 ∧ dx=0 := by
  let v := adjugateVector (Complex.I*(w:ℂ))
  let u0 := referencePath (realPart v) (imagPart v) w (2*Real.pi/w)
  let f := variationField r (2*Real.pi/w) dr dT u0 q
  let u : ℝ → (Fin 9 → ℂ) := fun t => complexify (integralVariation dx f t)
  have hinit : u 0=complexify dx := by simp [u,integralVariation_initial]
  have hp' : u 1=u 0 := by
    change complexify (integralVariation dx f 1)=complexify (integralVariation dx f 0)
    rw [integralVariation_eq dx f q hq ⟨1,by norm_num⟩,
      integralVariation_eq dx f q hq ⟨0,by norm_num⟩,hper]
  have hr : imagPart (u 0)=0 := by rw [hinit]; ext i; simp [imagPart]
  have hc : b.coord (Sum.inr 0) (u 0)=0 := by rwa [hinit]
  have hbase (t : UnitTime) : complexify (u0 t)=harmonicVector v (conjugateVector v) t := by
    exact normalized_orbit_harmonics v w (ne_of_gt hw) t
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :=
    complexify.hasFDerivAt.comp_hasDerivAt t (variational_ode r (2*Real.pi/w) dr dT dx u0 q hq t ht)
  have hu : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt u
      (((2*Real.pi/w:ℝ):ℂ) • (complexSource r).mulVec (u t)+
        (dT:ℂ) • (complexSource r).mulVec (harmonicVector v (conjugateVector v) t)+
        (((2*Real.pi/w:ℝ):ℂ)*(dr:ℂ)) • sourceDelta.mulVec
          (harmonicVector v (conjugateVector v) t)) t := by
    intro t ht
    have hh := hd t ht
    simp only [map_add,map_smul,complexify_source,complexify_delta,hbase] at hh
    convert hh using 1
    ext i
    simp [u,f,smul_smul,mul_assoc]
  obtain ⟨hdr,hdt,hzero⟩ := source_periodic_variation_kernel r w hw hp roots hn b hb he dr dT u hp' hr hc hu
  refine ⟨hdr,hdt,?_⟩
  rw [hinit] at hzero
  ext i
  have hi := congrFun hzero i
  simp only [complexify_apply,Pi.zero_apply] at hi
  exact Complex.ofReal_injective hi

end
end ThreeSitePhosphorylation.AttractingWitness


