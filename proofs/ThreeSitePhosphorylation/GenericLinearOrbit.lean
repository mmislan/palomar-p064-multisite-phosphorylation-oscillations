import proofs.ThreeSitePhosphorylation.Volterra

/-! Reference harmonic paths in an arbitrary real Banach space.
The actual action of the supplied operator on the two vectors is explicit. -/
namespace ThreeSitePhosphorylation.GenericLinearOrbit
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def linearOrbit (a b : E) (w t : ℝ) : E :=
  Real.cos (w*t) • a-Real.sin (w*t) • b

theorem linearOrbit_derivative (A : E →L[ℝ] E)
    (a b : E) (w : ℝ) (ha : A a=(-w) • b) (hb : A b=w • a) (t : ℝ) :
    HasDerivAt (linearOrbit a b w) (A (linearOrbit a b w t)) t := by
  have hc := ((Real.hasDerivAt_cos (w*t)).comp t ((hasDerivAt_id t).const_mul w)).smul_const a
  have hs := ((Real.hasDerivAt_sin (w*t)).comp t ((hasDerivAt_id t).const_mul w)).smul_const b
  convert hc.sub hs using 1
  simp only [linearOrbit,map_sub,map_smul,ha,hb,smul_smul]
  module

theorem linearOrbit_continuous (a b : E) (w : ℝ) :
    Continuous (linearOrbit a b w) := by unfold linearOrbit; fun_prop

def referencePath (a b : E) (w T : ℝ) : ContinuousPath E :=
  ⟨fun t => linearOrbit a b w (T*(t:ℝ)),(linearOrbit_continuous a b w).comp (by fun_prop)⟩

theorem referencePath_endpoints (a b : E) (w : ℝ) (hw : w ≠ 0) :
    referencePath a b w (2*Real.pi/w) ⟨0,by norm_num⟩=a ∧
      referencePath a b w (2*Real.pi/w) ⟨1,by norm_num⟩=a := by
  have he : w*(2*Real.pi/w)=2*Real.pi := by field_simp
  simp [referencePath,linearOrbit,he]

theorem referencePath_integral [CompleteSpace E] (A : E →L[ℝ] E)
    (a b : E) (w T : ℝ) (ha : A a=(-w) • b) (hb : A b=w • a) :
    linearPicard (T • A) (referencePath a b w T) =
      referencePath a b w T-ContinuousMap.const UnitTime a := by
  have hd (s : ℝ) : HasDerivAt (fun t => linearOrbit a b w (T*t))
      ((T • A) (linearOrbit a b w (T*s))) s := by
    have ht : HasDerivAt (fun t : ℝ => T*t) T s := by
      simpa using ((hasDerivAt_id s).const_mul T)
    exact (linearOrbit_derivative A a b w ha hb (T*s)).scomp s ht
  ext t
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := (t:ℝ)) (fun s _ => hd s)
    (((T • A).continuous.comp ((linearOrbit_continuous a b w).comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _)
  have he : (∫ s in (0:ℝ)..(t:ℝ), (T • A)
      (pathExtension (referencePath a b w T) s)) =
      ∫ s in (0:ℝ)..(t:ℝ), (T • A) (linearOrbit a b w (T*s)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Set.Icc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le t.2.1] at hs
      exact ⟨hs.1,hs.2.trans t.2.2⟩
    simp [pathExtension,Set.projIcc_of_mem _ hs',referencePath]
  change (∫ s in (0:ℝ)..(t:ℝ), (T • A)
      (pathExtension (referencePath a b w T) s)) = _
  rw [he,hf]
  simp [referencePath,linearOrbit]


end
end ThreeSitePhosphorylation.GenericLinearOrbit
