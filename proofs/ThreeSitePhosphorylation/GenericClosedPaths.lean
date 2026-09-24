import proofs.ThreeSitePhosphorylation.GenericAffinePathExistence
import proofs.ThreeSitePhosphorylation.GenericCriticalOrbit
import proofs.ThreeSitePhosphorylation.GenericShootingInvertibility

namespace ThreeSitePhosphorylation.GenericClosedPaths
noncomputable section
open scoped Topology
open GenericShootingMap GenericComplexification GenericLinearOrbit
open GenericPeriodicKernel GenericShootingInvertibility
set_option maxHeartbeats 500000

variable {ι σ : Type*} [Fintype ι] [DecidableEq σ]

theorem picard_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) (T : ℝ) (u : ContinuousPath E) :
    T • linearPicard (ContinuousLinearMap.id ℝ E) (A.compLeftContinuous ℝ UnitTime u)=
      linearPicard (T • A) u := by
  rw [← map_smul]
  ext t
  change (∫ s in (0:ℝ)..(t:ℝ), pathExtension (T • A.compLeftContinuous ℝ UnitTime u) s)=
    ∫ s in (0:ℝ)..(t:ℝ), (T • A) (pathExtension u s)
  apply intervalIntegral.integral_congr
  intro s _
  rfl

structure ClosedPathFamily (A0 D : Matrix ι ι ℝ)
    (B : ℝ → ContinuousPath (ι → ℝ) → ContinuousPath (ι → ℝ))
    (r w : ℝ) (v : ι → ℂ) where
  left : (ι → ℂ) →ₗ[ℂ] ℂ
  left_eigen : ∀ y, left ((GenericComplexification.complexMatrix (A0+r • D)).mulVec y)=
    (Complex.I*(w:ℂ))*left y
  left_normalized : left v=1
  parameters : ℝ → GenericShootingMap.ShootingState (ι → ℝ)
  paths : ℝ → ContinuousPath (ι → ℝ)
  parameters_smooth : ContDiffAt ℝ ⊤ parameters 0
  paths_smooth : ContDiffAt ℝ ⊤ paths 0
  parameters_zero : parameters 0=(GenericComplexification.realPart v,(r:ℂ)+Complex.I*((2*Real.pi/w:ℝ):ℂ))
  paths_zero : paths 0=GenericLinearOrbit.referencePath (GenericComplexification.realPart v) (GenericComplexification.imagPart v) w (2*Real.pi/w)
  residual : ∀ᶠ a in 𝓝 (0:ℝ), GenericAffinePathResidual.pathResidual
    A0.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap B
      (GenericShootingMap.shootingArgument (a,parameters a),paths a)=0
  closed : ∀ᶠ a in 𝓝 (0:ℝ), paths a ⟨1,by norm_num⟩=(parameters a).1
  normalized : ∀ᶠ a in 𝓝 (0:ℝ), GenericShootingInvertibility.sourceGauge left ((parameters a).1-GenericComplexification.realPart v)=0

/-- The two actual path/shooting implicit-function constructions produce a
normalized closed family. This does not yet assert nonlinear attraction. -/
theorem closed_path_family_exists (A0 D : Matrix ι ι ℝ)
    (Q : ℝ → (ι → ℝ) → (ι → ℝ))
    (B : ℝ → ContinuousPath (ι → ℝ) → ContinuousPath (ι → ℝ))
    (hQ : ContDiff ℝ ⊤ (fun p : ℝ × (ι → ℝ) => Q p.1 p.2))
    (hB : ContDiff ℝ ⊤ (fun p : ℝ × ContinuousPath (ι → ℝ) => B p.1 p.2))
    (hpoint : ∀ r u t, B r u t=Q r (u t))
    (r w : ℝ) (hw : 0<w) (roots : σ → ℝ) (hn : ∀ i, roots i<0)
    (basis : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ))
    (heigen : ∀ i, (GenericComplexification.complexMatrix (A0+r • D)).mulVec (basis i)=
      GenericPeriodicKernel.spectralValues roots w i • basis i)
    (hcross : (basis.coord (Sum.inr 0)
      ((GenericComplexification.complexMatrix D).mulVec (basis (Sum.inr 0)))).re<0) :
    Nonempty (ClosedPathFamily A0 D B r w (basis (Sum.inr 0))) := by
  let v := basis (Sum.inr (0:Fin 2))
  let x := GenericComplexification.realPart v
  let T := 2*Real.pi/w
  let s0 : GenericShootingMap.ShootingState (ι → ℝ) := (x,(r:ℂ)+Complex.I*(T:ℂ))
  let u0 := GenericLinearOrbit.referencePath x (GenericComplexification.imagPart v) w T
  have hev : (GenericComplexification.complexMatrix (A0+r • D)).mulVec v=(Complex.I*(w:ℂ)) • v := by
    simpa [v,GenericPeriodicKernel.spectralValues] using heigen (Sum.inr 0)
  have hint := GenericCriticalOrbit.critical_reference_integral (A0+r • D) w T v hev
  have hzeroPath : GenericAffinePathResidual.pathResidual
      A0.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap B
        (((0,(r,T)),x),u0)=0 := by
    simp only [GenericAffinePathResidual.pathResidual,zero_smul,add_zero,
      GenericAffinePathResidual.pathLinear]
    rw [picard_lift,← GenericShootingInvertibility.matrix_operator_affine]
    change u0-GenericVariationalODE.constantPath x-
      linearPicard (T • (A0+r • D).mulVecLin.toContinuousLinearMap) u0=0
    have hint' : u0=GenericVariationalODE.constantPath x+
        linearPicard (T • (A0+r • D).mulVecLin.toContinuousLinearMap) u0 := hint
    exact sub_eq_zero.mpr (sub_eq_iff_eq_add.mpr (hint'.trans (add_comm _ _)))
  obtain ⟨ψ,hψ,hψ0,hres⟩ := GenericAffinePathExistence.smooth_full_interval_paths
    A0.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap Q B
    hQ hB hpoint ((0,(r,T)),x) u0 hzeroPath
  have hi := GenericShootingInvertibility.shooting_partial_invertible A0 D B r w hw roots hn basis heigen hcross ψ hψ hψ0 hres
  have hs := GenericShootingMap.shootingMap_smooth ψ (GenericShootingInvertibility.sourceGauge (basis.coord (Sum.inr 0))) x (0,s0)
    (by simpa [GenericShootingMap.shootingArgument,s0] using hψ)
  have hzero : GenericShootingMap.shootingMap ψ (GenericShootingInvertibility.sourceGauge (basis.coord (Sum.inr 0))) x (0,s0)=0 := by
    apply GenericShootingMap.shootingMap_zero
    rw [hψ0]
    exact (GenericLinearOrbit.referencePath_endpoints x (GenericComplexification.imagPart v) w (ne_of_gt hw)).2
  let b := hs.implicitFunction (by simp) hi
  have hb : ContDiffAt ℝ ⊤ b 0 := hs.contDiffAt_implicitFunction (by simp) hi
  have hb0 : b 0=s0 := hs.implicitFunction_apply_self (by simp) hi
  have hclosed : ∀ᶠ a in 𝓝 (0:ℝ),
      GenericShootingMap.shootingMap ψ (GenericShootingInvertibility.sourceGauge (basis.coord (Sum.inr 0))) x (a,b a)=0 := by
    simpa only [hzero] using hs.eventually_apply_implicitFunction (by simp) hi
  have harg : ContDiffAt ℝ ⊤ (fun a => GenericShootingMap.shootingArgument (a,b a)) 0 :=
    GenericShootingMap.shootingArgument_smooth.contDiffAt.comp 0 (contDiffAt_id.prodMk hb)
  have harg0 : GenericShootingMap.shootingArgument (0,b 0)=((0,(r,T)),x) := by
    rw [hb0]
    simp [GenericShootingMap.shootingArgument,s0]
  have hpath : ContDiffAt ℝ ⊤ (fun a => ψ (GenericShootingMap.shootingArgument (a,b a))) 0 := by
    apply ContDiffAt.comp 0 _ harg
    rwa [harg0]
  refine ⟨{
    left := basis.coord (Sum.inr 0)
    left_eigen := ?_
    left_normalized := by simp [Module.Basis.coord_apply]
    parameters := b
    paths := fun a => ψ (GenericShootingMap.shootingArgument (a,b a))
    parameters_smooth := hb
    paths_smooth := hpath
    parameters_zero := hb0
    paths_zero := by rw [harg0,hψ0]
    residual := ?_
    closed := ?_
    normalized := ?_ }⟩
  · intro y
    simpa [GenericPeriodicKernel.spectralValues] using GenericPeriodicKernel.basis_coord_eigen basis _ _ heigen (Sum.inr 0) y
  · have ht := harg.continuousAt.tendsto
    rw [harg0] at ht
    exact ht.eventually hres
  · filter_upwards [hclosed] with a ha
    exact sub_eq_zero.mp (congrArg Prod.fst ha)
  · filter_upwards [hclosed] with a ha
    exact congrArg Prod.snd ha

end
end ThreeSitePhosphorylation.GenericClosedPaths
