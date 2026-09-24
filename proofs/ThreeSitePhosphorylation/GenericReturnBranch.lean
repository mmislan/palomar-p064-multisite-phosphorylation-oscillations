import proofs.ThreeSitePhosphorylation.GenericClosedPaths
import proofs.ThreeSitePhosphorylation.GenericReturnIFT
import proofs.ThreeSitePhosphorylation.GenericAffinePathUniqueness

namespace ThreeSitePhosphorylation.GenericReturnBranch
noncomputable section
open scoped Topology
open GenericClosedPaths GenericReturnIFT GenericShootingMap GenericLinearOrbit
open GenericComplexification GenericShootingInvertibility GenericVariationalODE
variable {ι : Type*} [Fintype ι]
variable (A0 D : Matrix ι ι ℝ)
variable (B : ℝ → ContinuousPath (ι → ℝ) → ContinuousPath (ι → ℝ))
variable (v : ι → ℂ)
variable (Q : ℝ → (ι → ℝ) → (ι → ℝ))
variable (hQ : ContDiff ℝ ⊤ (fun p : ℝ × (ι → ℝ) => Q p.1 p.2))
variable (hB : ContDiff ℝ ⊤ (fun p : ℝ × ContinuousPath (ι → ℝ) => B p.1 p.2))
variable (hpoint : ∀ r u t, B r u t=Q r (u t))

theorem closed_family_solution_operator (r w : ℝ) (C : ClosedPathFamily A0 D B r w v)
    (ψ : FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (huniq : ∀ᶠ d in 𝓝 (((0,(r,2*Real.pi/w)),GenericComplexification.realPart v),
        referencePath (GenericComplexification.realPart v)
          (GenericComplexification.imagPart v) w (2*Real.pi/w)),
      GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap B d=0 ↔ ψ d.1=d.2) :
    ∀ᶠ a in 𝓝 (0:ℝ), ψ (shootingArgument (a,C.parameters a))=C.paths a := by
  have hc := (shootingArgument_smooth.continuous.continuousAt.comp
    (continuousAt_id.prodMk C.parameters_smooth.continuousAt)).prodMk C.paths_smooth.continuousAt
  have ht : Filter.Tendsto (fun a => (shootingArgument (a,C.parameters a),C.paths a)) (𝓝 (0:ℝ))
      (𝓝 (((0,(r,2*Real.pi/w)),GenericComplexification.realPart v),
        referencePath (GenericComplexification.realPart v)
          (GenericComplexification.imagPart v) w (2*Real.pi/w))) := by
    simpa [shootingArgument,C.parameters_zero,C.paths_zero] using hc.tendsto
  filter_upwards [ht.eventually huniq,C.residual] with a ha hr
  exact ha.mp hr

theorem closed_family_return_time (r w : ℝ) (hw : 0 < w)
    (he : (complexMatrix (A0+r • D)).mulVec v=(Complex.I*(w:ℂ)) • v) (C : ClosedPathFamily A0 D B r w v)
    (ψ : FlowData (ι → ℝ) → ContinuousPath (ι → ℝ)) (τ : ReturnData (ι → ℝ) → ℝ)
    (hpath : ∀ᶠ a in 𝓝 (0:ℝ), ψ (shootingArgument (a,C.parameters a))=C.paths a)
    (huniq : ∀ᶠ d in 𝓝 (((0,r),GenericComplexification.realPart v),2*Real.pi/w),
      endpointPhase ψ C.left d=0 ↔ τ d.1=d.2) :
    ∀ᶠ a in 𝓝 (0:ℝ),
      τ ((a,(C.parameters a).2.re),(C.parameters a).1)=(C.parameters a).2.im ∧
      returnPoint ψ τ ((a,(C.parameters a).2.re),(C.parameters a).1)=(C.parameters a).1 := by
  have hc : ContinuousAt (fun a : ℝ =>
      (((a,(C.parameters a).2.re),(C.parameters a).1),(C.parameters a).2.im)) 0 := by
    have hC := C.parameters_smooth.continuousAt
    have hr := Complex.reCLM.continuous.continuousAt.comp hC.snd
    have hi := Complex.imCLM.continuous.continuousAt.comp hC.snd
    exact ((continuousAt_id.prodMk hr).prodMk hC.fst).prodMk hi
  have ht : Filter.Tendsto (fun a : ℝ =>
      (((a,(C.parameters a).2.re),(C.parameters a).1),(C.parameters a).2.im)) (𝓝 0)
      (𝓝 (((0,r),GenericComplexification.realPart v),2*Real.pi/w)) := by
    simpa [C.parameters_zero] using hc.tendsto
  have hbase := GenericReturnTime.normalized_eigen_real_pairing (A0+r • D) w (ne_of_gt hw)
    v C.left he
    C.left_eigen C.left_normalized
  filter_upwards [ht.eventually huniq,hpath,C.normalized,C.closed] with a ha hpatha hnorm hclosed
  have hphase : endpointPhase ψ C.left
      (((a,(C.parameters a).2.re),(C.parameters a).1),(C.parameters a).2.im)=0 := by
    change (sourceGauge C.left (ψ (shootingArgument (a,C.parameters a)) ⟨1,by norm_num⟩)).im=0
    rw [hpatha,hclosed]
    have hn : sourceGauge C.left (C.parameters a).1 =
        sourceGauge C.left (GenericComplexification.realPart v) := by
      exact sub_eq_zero.mp (by simpa only [map_sub] using hnorm)
    rw [hn]
    change (C.left (complexify (GenericComplexification.realPart v))).im=0
    rw [hbase]
    norm_num
  have htime := ha.mp hphase
  refine ⟨htime,?_⟩
  unfold returnPoint
  rw [htime]
  change ψ (shootingArgument (a,C.parameters a)) ⟨1,by norm_num⟩=(C.parameters a).1
  rw [hpatha,hclosed]

include hQ hB hpoint in
theorem closed_family_return_map_exists (r w : ℝ) (hw : 0 < w)
    (he : (complexMatrix (A0+r • D)).mulVec v=(Complex.I*(w:ℂ)) • v) (C : ClosedPathFamily A0 D B r w v) :
    ∃ (ψ : FlowData (ι → ℝ) → ContinuousPath (ι → ℝ)) (τ : ReturnData (ι → ℝ) → ℝ),
      ContDiffAt ℝ ⊤ ψ ((0,(r,2*Real.pi/w)),GenericComplexification.realPart v) ∧
      ContDiffAt ℝ ⊤ τ ((0,r),GenericComplexification.realPart v) ∧
      ContDiffAt ℝ ⊤ (returnPoint ψ τ) ((0,r),GenericComplexification.realPart v) ∧
      τ ((0,r),GenericComplexification.realPart v)=2*Real.pi/w ∧
      (∀ᶠ a in 𝓝 (0:ℝ),
        τ ((a,(C.parameters a).2.re),(C.parameters a).1)=(C.parameters a).2.im ∧
        returnPoint ψ τ ((a,(C.parameters a).2.re),(C.parameters a).1)=(C.parameters a).1) ∧
      (∀ᶠ d in 𝓝 (((0,(r,2*Real.pi/w)),GenericComplexification.realPart v),
        referencePath (GenericComplexification.realPart v)
          (GenericComplexification.imagPart v) w (2*Real.pi/w)),
        GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap B d=0 ↔ ψ d.1=d.2) ∧
      (∀ᶠ d in 𝓝 (((0,r),GenericComplexification.realPart v),2*Real.pi/w),
        endpointPhase ψ C.left d=0 ↔ τ d.1=d.2) := by
  let T := 2*Real.pi/w
  obtain ⟨ψ,hψ,hψ0,hres,hunique⟩ := GenericAffinePathUniqueness.smooth_full_interval_paths_unique
    A0.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap Q B hQ hB hpoint
    ((0,(r,T)),GenericComplexification.realPart v)
    (referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w T) (GenericReturnTime.critical_reference_solution A0 D B r w T v he)
  obtain ⟨τ,hτ,hτ0,hreturn,hτunique⟩ := smooth_poincare_time A0 D B r w hw v C.left he
    C.left_eigen C.left_normalized ψ hψ hres
  have hpath := closed_family_solution_operator A0 D B v r w C ψ hunique
  have hfixed := closed_family_return_time A0 D B v r w hw he C ψ τ hpath hτunique
  have hs : ContDiffAt ℝ ⊤ (returnPoint ψ τ) ((0,r),GenericComplexification.realPart v) := by
    apply returnPoint_smooth ψ τ _ hτ
    simpa only [hτ0,returnArgument] using hψ
  exact ⟨ψ,τ,hψ,hτ,hs,hτ0,hfixed,hunique,hτunique⟩

end
end ThreeSitePhosphorylation.GenericReturnBranch
