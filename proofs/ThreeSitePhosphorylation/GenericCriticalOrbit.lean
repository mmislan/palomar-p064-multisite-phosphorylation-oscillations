import proofs.ThreeSitePhosphorylation.GenericComplexification
import proofs.ThreeSitePhosphorylation.GenericLinearOrbit
import proofs.ThreeSitePhosphorylation.GenericResonantKernel

namespace ThreeSitePhosphorylation.GenericCriticalOrbit
noncomputable section
open GenericComplexification GenericLinearOrbit

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem complexify_injective :
    Function.Injective (GenericComplexification.complexify : (ι → ℝ) → (ι → ℂ)) := by
  intro x y h
  funext i
  have hi := congrArg Complex.re (congrFun h i)
  simpa only [complexify_apply,Complex.ofReal_re] using hi

/-- The actual real critical orbit has the normalized first-harmonic
complexification used by the generic resonant kernel. -/
theorem normalized_orbit_harmonics (v : ι → ℂ) (w : ℝ) (hw : w ≠ 0) (t : ℝ) :
    complexify (linearOrbit (GenericComplexification.realPart v) (imagPart v) w ((2*Real.pi/w)*t))=
      GenericResonantKernel.harmonicVector v (conjugateVector v) t := by
  have ht : w*((2*Real.pi/w)*t)=2*Real.pi*t := by field_simp
  rw [linearOrbit,ht,complexify_orbit]
  unfold GenericResonantKernel.harmonicVector
  have he : ((2*Real.pi*t : ℝ) : ℂ)*Complex.I=turnFrequency*(t:ℂ) := by
    simp only [turnFrequency,Complex.ofReal_mul,Complex.ofReal_ofNat]
    ring
  have hn : -((2*Real.pi*t : ℝ) : ℂ)*Complex.I = -turnFrequency*(t:ℂ) := by
    rw [neg_mul,he,neg_mul]
  rw [he,hn]

theorem referencePath_harmonics (v : ι → ℂ) (w : ℝ) (hw : 0<w) (t : UnitTime) :
    complexify (referencePath (GenericComplexification.realPart v) (imagPart v) w (2*Real.pi/w) t)=
      GenericResonantKernel.harmonicVector v (conjugateVector v) (t:ℝ) :=
  normalized_orbit_harmonics v w (ne_of_gt hw) t

/-- A literal critical eigenvector of the complexification of a real matrix
supplies the two real operator actions and hence the actual integral path. -/
theorem critical_reference_integral (A : Matrix ι ι ℝ) (w T : ℝ) (v : ι → ℂ)
    (he : (complexMatrix A).mulVec v=(Complex.I*(w:ℂ)) • v) :
    referencePath (GenericComplexification.realPart v) (imagPart v) w T =
      ContinuousMap.const UnitTime (GenericComplexification.realPart v)+
        linearPicard (T • A.mulVecLin.toContinuousLinearMap)
          (referencePath (GenericComplexification.realPart v) (imagPart v) w T) := by
  obtain ⟨ha,hb⟩ := source_eigen_real_imag A w v he
  have hh := referencePath_integral A.mulVecLin.toContinuousLinearMap
    (GenericComplexification.realPart v) (imagPart v) w T ha hb
  rw [hh]
  abel

/-- At the positive critical frequency, the same integral path has the
required closed endpoints and normalized physical duration. -/
theorem normalized_critical_reference (A : Matrix ι ι ℝ) (w : ℝ) (hw : 0<w)
    (v : ι → ℂ) (he : (complexMatrix A).mulVec v=(Complex.I*(w:ℂ)) • v) :
    let u := referencePath (GenericComplexification.realPart v) (imagPart v) w (2*Real.pi/w)
    u=ContinuousMap.const UnitTime (GenericComplexification.realPart v)+
      linearPicard ((2*Real.pi/w) • A.mulVecLin.toContinuousLinearMap) u ∧
      u ⟨0,by norm_num⟩=GenericComplexification.realPart v ∧ u ⟨1,by norm_num⟩=GenericComplexification.realPart v := by
  exact ⟨critical_reference_integral A w (2*Real.pi/w) v he,
    referencePath_endpoints (GenericComplexification.realPart v) (imagPart v) w (ne_of_gt hw)⟩

end
end ThreeSitePhosphorylation.GenericCriticalOrbit
