import proofs.ThreeSitePhosphorylation.GenericReturnDerivative
import proofs.ThreeSitePhosphorylation.GenericReturnParameterPairing
import proofs.ThreeSitePhosphorylation.GenericReturnBranch

/-! The actual local solution and return-time maps of a closed quadratic
branch, retaining smoothness, residual, phase, both uniqueness statements,
base values, branch fixed points and actual scaling. Every field is supplied
by the path and return-time implicit-function constructions. -/
namespace ThreeSitePhosphorylation.GenericReturnContracts
noncomputable section
open scoped Topology
open GenericReturnIFT GenericReturnScaling GenericClosedPaths

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A0 D : Matrix ι ι ℝ} {K : ℝ → GenericQuadraticTensor.Tensor ι}
variable {r w : ℝ} {v : ι → ℂ}

structure ReturnFlow (C : ClosedPathFamily A0 D (GenericQuadraticTensor.pathField K) r w v) where
  ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ)
  τ : ReturnData (ι → ℝ) → ℝ
  ψ_smooth : ContDiffAt ℝ ⊤ ψ ((0,(r,2*Real.pi/w)),GenericComplexification.realPart v)
  τ_smooth : ContDiffAt ℝ ⊤ τ ((0,r),GenericComplexification.realPart v)
  point_smooth : ContDiffAt ℝ ⊤ (returnPoint ψ τ) ((0,r),GenericComplexification.realPart v)
  ψ_zero : ψ ((0,(r,2*Real.pi/w)),GenericComplexification.realPart v)=
    GenericLinearOrbit.referencePath (GenericComplexification.realPart v)
      (GenericComplexification.imagPart v) w (2*Real.pi/w)
  τ_zero : τ ((0,r),GenericComplexification.realPart v)=2*Real.pi/w
  residual : ∀ᶠ d in 𝓝 ((0,(r,2*Real.pi/w)),GenericComplexification.realPart v),
    GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
      D.mulVecLin.toContinuousLinearMap (GenericQuadraticTensor.pathField K) (d,ψ d)=0
  path_unique : ∀ᶠ d in 𝓝 (((0,(r,2*Real.pi/w)),GenericComplexification.realPart v),
      GenericLinearOrbit.referencePath (GenericComplexification.realPart v)
        (GenericComplexification.imagPart v) w (2*Real.pi/w)),
    GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
      D.mulVecLin.toContinuousLinearMap (GenericQuadraticTensor.pathField K) d=0 ↔ ψ d.1=d.2
  phase : ∀ᶠ d in 𝓝 ((0,r),GenericComplexification.realPart v),
    endpointPhase ψ C.left (d,τ d)=0
  time_unique : ∀ᶠ d in 𝓝 (((0,r),GenericComplexification.realPart v),2*Real.pi/w),
    endpointPhase ψ C.left d=0 ↔ τ d.1=d.2
  branch_closed : ∀ᶠ a in 𝓝 (0:ℝ),
    τ ((a,(C.parameters a).2.re),(C.parameters a).1)=(C.parameters a).2.im ∧
    returnPoint ψ τ ((a,(C.parameters a).2.re),(C.parameters a).1)=(C.parameters a).1

theorem returnFlow_exists (hK : ∀ i j k, ContDiff ℝ ⊤ (fun s => K s i j k)) (hw : 0<w)
    (he : (GenericComplexification.complexMatrix (A0+r • D)).mulVec v=(Complex.I*(w:ℂ)) • v)
    (C : ClosedPathFamily A0 D (GenericQuadraticTensor.pathField K) r w v) :
    Nonempty (ReturnFlow C) := by
  obtain ⟨ψ,τ,hψ,hτ,hs,hτ0,hfixed,huniq,htime⟩ :=
    GenericReturnBranch.closed_family_return_map_exists A0 D (GenericQuadraticTensor.pathField K) v
      (GenericQuadraticTensor.field K) (GenericQuadraticTensor.field_smooth K hK)
      (GenericQuadraticTensor.pathField_smooth K hK) (GenericQuadraticTensor.pathField_apply K)
      r w hw he C
  let T := 2*Real.pi/w
  let x := GenericComplexification.realPart v
  let u := GenericLinearOrbit.referencePath x (GenericComplexification.imagPart v) w T
  have hu : GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
      D.mulVecLin.toContinuousLinearMap (GenericQuadraticTensor.pathField K) (((0,(r,T)),x),u)=0 :=
    GenericReturnTime.critical_reference_solution A0 D _ r w T v he
  have hψ0 : ψ ((0,(r,T)),x)=u := huniq.self_of_nhds.mp hu
  have hres : ∀ᶠ d in 𝓝 ((0,(r,T)),x),
      GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
        D.mulVecLin.toContinuousLinearMap (GenericQuadraticTensor.pathField K) (d,ψ d)=0 := by
    have ht : Filter.Tendsto (fun d : GenericShootingMap.FlowData (ι → ℝ) => (d,ψ d))
        (𝓝 ((0,(r,T)),x)) (𝓝 (((0,(r,T)),x),u)) := by
      have hψ' : ContinuousAt ψ ((0,(r,T)),x) := hψ.continuousAt
      simpa only [id_eq,hψ0] using (continuousAt_id.prodMk hψ').tendsto
    filter_upwards [ht.eventually huniq] with d hd
    exact hd.mpr rfl
  have hphase : ∀ᶠ d in 𝓝 ((0,r),x), endpointPhase ψ C.left (d,τ d)=0 := by
    have ht : Filter.Tendsto (fun d : ReturnData (ι → ℝ) => (d,τ d))
        (𝓝 ((0,r),x)) (𝓝 (((0,r),x),T)) := by
      simpa only [hτ0] using (continuousAt_id.prodMk hτ.continuousAt).tendsto
    filter_upwards [ht.eventually htime] with d hd
    exact hd.mpr rfl
  exact ⟨⟨ψ,τ,hψ,hτ,hs,hψ0,hτ0,hres,huniq,hphase,htime,hfixed⟩⟩

/-- Actual local scaling of the return map, from the residual and both
uniqueness statements (`GenericReturnScaling.actual_return_scaling`). -/
theorem ReturnFlow.scaling {C : ClosedPathFamily A0 D (GenericQuadraticTensor.pathField K) r w v}
    (R : ReturnFlow C) (hK : ∀ i j k, ContDiff ℝ ⊤ (fun s => K s i j k)) :
    ∀ᶠ z in 𝓝 (((0,r),GenericComplexification.realPart v),(1:ℝ)),
      R.τ (scaleReturnData z.1 z.2)=R.τ z.1 ∧
      returnPoint R.ψ R.τ (scaleReturnData z.1 z.2)=z.2 • returnPoint R.ψ R.τ z.1 :=
  actual_return_scaling A0.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap K hK
    r (2*Real.pi/w) _ _ C.left R.ψ R.τ
    R.ψ_smooth.continuousAt R.ψ_zero R.τ_smooth.continuousAt R.τ_zero
    R.residual R.phase R.time_unique

/-- Negative actual crossing gives the negative actual return parameter pairing. -/
theorem ReturnFlow.parameter_pairing_negative
    {C : ClosedPathFamily A0 D (GenericQuadraticTensor.pathField K) r w v}
    (R : ReturnFlow C) (hw : 0<w)
    (he : (GenericComplexification.complexMatrix (A0+r • D)).mulVec v=(Complex.I*(w:ℂ)) • v)
    (hcross : (C.left ((GenericComplexification.complexMatrix D).mulVec v)).re<0) :
    2*(C.left (GenericComplexification.complexify ((fderiv ℝ (returnPoint R.ψ R.τ)
      ((0,r),GenericComplexification.realPart v)) ((0,1),0)))).re<0 :=
  GenericReturnParameterPairing.return_parameter_pairing_negative A0 D _ r w hw v C.left he
    C.left_eigen C.left_normalized hcross R.ψ R.τ R.ψ_smooth R.τ_smooth R.τ_zero R.residual

end
end ThreeSitePhosphorylation.GenericReturnContracts
