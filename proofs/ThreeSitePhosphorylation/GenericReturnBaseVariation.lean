import proofs.ThreeSitePhosphorylation.GenericClosedPaths

namespace ThreeSitePhosphorylation.GenericReturnBaseVariation
noncomputable section
open scoped Topology
open GenericVariationalODE

variable {ι : Type*} [Fintype ι]

def pathLinear (A : Matrix ι ι ℝ) :
    ContinuousPath (ι → ℝ) →L[ℝ] ContinuousPath (ι → ℝ) :=
  A.mulVecLin.toContinuousLinearMap.compLeftContinuous ℝ UnitTime

@[simp] theorem pathLinear_apply (A : Matrix ι ι ℝ)
    (u : ContinuousPath (ι → ℝ)) (t : UnitTime) :
    pathLinear A u t=A.mulVecLin.toContinuousLinearMap (u t) := rfl

theorem linearPicard_pathLinear (A : Matrix ι ι ℝ) (T : ℝ)
    (u : ContinuousPath (ι → ℝ)) :
    linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ)) (T • pathLinear A u)=
      linearPicard (T • A.mulVecLin.toContinuousLinearMap) u := by
  rw [map_smul]
  exact GenericClosedPaths.picard_lift A.mulVecLin.toContinuousLinearMap T u

def periodTimePath (A : Matrix ι ι ℝ) (u : (ContinuousPath (ι → ℝ))) : (ContinuousPath (ι → ℝ)) :=
  ⟨fun t => (t:ℝ) • A.mulVecLin.toContinuousLinearMap (u t),by fun_prop⟩

theorem periodTimePath_integral (A : Matrix ι ι ℝ) (w T : ℝ) (v : ι → ℂ)
    (he : (GenericComplexification.complexMatrix A).mulVec v=(Complex.I*(w:ℂ)) • v) :
    periodTimePath A (GenericLinearOrbit.referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w T) =
      linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ))
        (T • pathLinear A (periodTimePath A (GenericLinearOrbit.referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w T))+
          pathLinear A (GenericLinearOrbit.referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w T)) := by
  let L := A.mulVecLin.toContinuousLinearMap
  let b := fun t : ℝ => GenericLinearOrbit.linearOrbit (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w (T*t)
  let g := fun t : ℝ => t • L (b t)
  obtain ⟨ha,hb⟩ := GenericComplexification.source_eigen_real_imag A w v he
  have hd (t : ℝ) : HasDerivAt g (T • L (g t)+L (b t)) t := by
    have ht : HasDerivAt (fun s : ℝ => T*s) T t := by
      simpa using (hasDerivAt_id t).const_mul T
    have hb' : HasDerivAt b (T • L (b t)) t :=
      (GenericLinearOrbit.linearOrbit_derivative L (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w ha hb (T*t)).scomp t ht
    have hA := L.hasFDerivAt.comp_hasDerivAt t hb'
    have hh := (hasDerivAt_id t).smul hA
    convert hh using 1
    simp only [g,map_smul,smul_smul,one_smul,Function.comp_apply,id_eq]
    module
  have hc : Continuous (fun t => T • L (g t)+L (b t)) := by
    have hbc : Continuous b := (GenericLinearOrbit.linearOrbit_continuous (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w).comp
      (continuous_const.mul continuous_id)
    exact (continuous_const.smul (L.continuous.comp
      (continuous_id.smul (L.continuous.comp hbc)))).add (L.continuous.comp hbc)
  apply ContinuousMap.ext
  intro t
  apply funext
  intro i
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := (t:ℝ)) (fun s _ => hd s) (hc.intervalIntegrable _ _)
  have hh : (∫ s in (0:ℝ)..(t:ℝ), pathExtension
      (T • pathLinear A (periodTimePath A (GenericLinearOrbit.referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w T))+
        pathLinear A (GenericLinearOrbit.referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w T)) s) =
      ∫ s in (0:ℝ)..(t:ℝ), T • L (g s)+L (b s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Set.Icc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le t.2.1] at hs
      exact ⟨hs.1,hs.2.trans t.2.2⟩
    simp [pathExtension,Set.projIcc_of_mem _ hs',pathLinear_apply,periodTimePath,
      GenericLinearOrbit.referencePath,L,g,b]
  change (periodTimePath A (GenericLinearOrbit.referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w T) t) i =
    (∫ s in (0:ℝ)..(t:ℝ), pathExtension
      (T • pathLinear A (periodTimePath A (GenericLinearOrbit.referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w T))+
        pathLinear A (GenericLinearOrbit.referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w T)) s) i
  rw [hh,hf]
  simp [periodTimePath,GenericLinearOrbit.referencePath,g,b,L]

theorem parameter_free_variation_endpoint (A : Matrix ι ι ℝ) (w : ℝ) (hw : w ≠ 0)
    (v : ι → ℂ) (he : (GenericComplexification.complexMatrix A).mulVec v=(Complex.I*(w:ℂ)) • v)
    (dT : ℝ) (dx : (ι → ℝ)) (U q : (ContinuousPath (ι → ℝ)))
    (hU : U=constantPath dx+linearPicard ((2*Real.pi/w) • A.mulVecLin.toContinuousLinearMap) U)
    (hq : q=constantPath dx+linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ))
      (GenericVariationalODE.variationField A.mulVecLin.toContinuousLinearMap 0 (2*Real.pi/w) 0 dT
        (GenericLinearOrbit.referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w (2*Real.pi/w)) q)) :
    q ⟨1,by norm_num⟩=U ⟨1,by norm_num⟩+dT • A.mulVecLin.toContinuousLinearMap (GenericComplexification.realPart v) := by
  let T := 2*Real.pi/w
  let u0 := GenericLinearOrbit.referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w T
  let V := periodTimePath A u0
  have hV : V=linearPicard (T • A.mulVecLin.toContinuousLinearMap) V+
      linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ)) (pathLinear A u0) := by
    have hh := periodTimePath_integral A w T v he
    rw [map_add,linearPicard_pathLinear] at hh
    exact hh
  have hq' : q=constantPath dx+linearPicard (T • A.mulVecLin.toContinuousLinearMap) q+
      dT • linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ)) (pathLinear A u0) := by
    have hh : q=constantPath dx+linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ))
        (T • pathLinear A q+dT • pathLinear A u0) := by
      simpa [GenericVariationalODE.variationField,pathLinear,T,u0] using hq
    rw [map_add,linearPicard_pathLinear] at hh
    simpa only [map_smul,add_assoc] using hh
  have hdiff : (1-linearPicard (T • A.mulVecLin.toContinuousLinearMap)) (q-(U+dT • V))=0 := by
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,map_sub,map_add,map_smul]
    linear_combination (norm := module) hq' - hU - dT • hV
  obtain ⟨b,hb⟩ := linearPicard_one_sub_isUnit (T • A.mulVecLin.toContinuousLinearMap)
  have hz : q-(U+dT • V)=0 := by
    apply (ContinuousLinearEquiv.unitsEquiv ℝ (ContinuousPath (ι → ℝ)) b).injective
    change (b : (ContinuousPath (ι → ℝ)) →L[ℝ] (ContinuousPath (ι → ℝ))) (q-(U+dT • V)) =
      (b : (ContinuousPath (ι → ℝ)) →L[ℝ] (ContinuousPath (ι → ℝ))) 0
    rw [hb,map_zero]
    exact hdiff
  have hh := congrArg (fun f : (ContinuousPath (ι → ℝ)) => f ⟨1,by norm_num⟩) (sub_eq_zero.mp hz)
  have hend := (GenericLinearOrbit.referencePath_endpoints (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w hw).2
  simpa only [ContinuousMap.add_apply,ContinuousMap.smul_apply,V,periodTimePath,
    ContinuousMap.coe_mk,one_smul,u0,T,hend] using hh

theorem corrected_variation_endpoint (A : Matrix ι ι ℝ) (w : ℝ) (hw : w ≠ 0)
    (v : ι → ℂ) (he : (GenericComplexification.complexMatrix A).mulVec v=(Complex.I*(w:ℂ)) • v)
    (H : (ι → ℝ) →L[ℝ] ℝ) (htrans : H (A.mulVecLin.toContinuousLinearMap (GenericComplexification.realPart v)) ≠ 0)
    (dT : ℝ) (dx : (ι → ℝ)) (U q : (ContinuousPath (ι → ℝ)))
    (hU : U=constantPath dx+linearPicard ((2*Real.pi/w) • A.mulVecLin.toContinuousLinearMap) U)
    (hq : q=constantPath dx+linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ))
      (GenericVariationalODE.variationField A.mulVecLin.toContinuousLinearMap 0 (2*Real.pi/w) 0 dT
        (GenericLinearOrbit.referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w (2*Real.pi/w)) q))
    (hphase : H (q ⟨1,by norm_num⟩)=0) :
    q ⟨1,by norm_num⟩=U ⟨1,by norm_num⟩-
      (H (U ⟨1,by norm_num⟩)/H (A.mulVecLin.toContinuousLinearMap (GenericComplexification.realPart v))) • A.mulVecLin.toContinuousLinearMap (GenericComplexification.realPart v) := by
  have heq := parameter_free_variation_endpoint A w hw v he dT dx U q hU hq
  rw [heq,map_add,map_smul,smul_eq_mul] at hphase
  have hd : dT= -(H (U ⟨1,by norm_num⟩)/H (A.mulVecLin.toContinuousLinearMap (GenericComplexification.realPart v))) := by
    apply (eq_neg_iff_add_eq_zero).mpr
    field_simp [htrans]
    linarith [hphase]
  rw [heq,hd,neg_smul]
  simp only [sub_eq_add_neg]


end
end ThreeSitePhosphorylation.GenericReturnBaseVariation
