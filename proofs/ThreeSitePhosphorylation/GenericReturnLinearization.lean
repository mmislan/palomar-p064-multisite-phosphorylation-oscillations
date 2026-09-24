import proofs.ThreeSitePhosphorylation.GenericReturnContracts
import proofs.ThreeSitePhosphorylation.GenericReturnBaseEigenbasis

/-! Linearization of the actual return map along the actual closed branch:
branch return data, the radial vector x+a*x', the state derivative family,
the kinetic-parameter derivative, and the exact radial vector identity. -/
namespace ThreeSitePhosphorylation.GenericReturnLinearization
noncomputable section
open Filter
open scoped Topology
open GenericReturnIFT GenericReturnDerivative GenericClosedPaths GenericReturnContracts

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A0 D : Matrix ι ι ℝ} {K : ℝ → GenericQuadraticTensor.Tensor ι}
variable {r w : ℝ} {v : ι → ℂ}

omit [DecidableEq ι] in
def returnReorder : ReturnVariables ι →L[ℝ] ReturnData (ι → ℝ) :=
  ({ toFun := fun z => ((z.1,z.2.1),z.2.2)
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } :
    ReturnVariables ι →ₗ[ℝ] ReturnData (ι → ℝ)).toContinuousLinearMap

omit [DecidableEq ι] in
theorem returnMap_fderiv_reorder
    (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (τ : ReturnData (ι → ℝ) → ℝ) (z : ReturnVariables ι)
    (hd : DifferentiableAt ℝ (returnPoint ψ τ) (returnReorder z)) :
    fderiv ℝ (returnMap ψ τ) z=fderiv ℝ (returnPoint ψ τ) (returnReorder z) ∘L returnReorder :=
  (hd.hasFDerivAt.comp z returnReorder.hasFDerivAt).fderiv

section
variable {B : ℝ → ContinuousPath (ι → ℝ) → ContinuousPath (ι → ℝ)}

omit [DecidableEq ι] in
def branchReturnData (C : ClosedPathFamily A0 D B r w v) (a : ℝ) : ReturnData (ι → ℝ) :=
  ((a,(C.parameters a).2.re),(C.parameters a).1)

omit [DecidableEq ι] in
def radialVector (C : ClosedPathFamily A0 D B r w v) (a : ℝ) : ι → ℝ :=
  (C.parameters a).1+a • (deriv C.parameters a).1

omit [DecidableEq ι] in
def kineticParameter (C : ClosedPathFamily A0 D B r w v) (a : ℝ) : ℝ :=
  (C.parameters a).2.re

omit [DecidableEq ι] in
theorem branchReturnData_zero (C : ClosedPathFamily A0 D B r w v) :
    branchReturnData C 0=((0,r),GenericComplexification.realPart v) := by
  simp [branchReturnData,C.parameters_zero]

omit [DecidableEq ι] in
theorem branchReturnData_smooth (C : ClosedPathFamily A0 D B r w v) :
    ContDiffAt ℝ ⊤ (branchReturnData C) 0 := by
  exact (contDiffAt_id.prodMk
    (Complex.reCLM.contDiff.contDiffAt.comp 0 C.parameters_smooth.snd)).prodMk
      C.parameters_smooth.fst

omit [DecidableEq ι] in
theorem radialVector_smooth (C : ClosedPathFamily A0 D B r w v) :
    ContDiffAt ℝ ⊤ (radialVector C) 0 := by
  exact C.parameters_smooth.fst.add
    (contDiffAt_id.smul (C.parameters_smooth.derivWithin (m := ⊤) (by simp)).fst)

omit [DecidableEq ι] in
theorem radialVector_zero (C : ClosedPathFamily A0 D B r w v) :
    radialVector C 0=GenericComplexification.realPart v := by
  simp [radialVector,C.parameters_zero]
end

variable {C : ClosedPathFamily A0 D (GenericQuadraticTensor.pathField K) r w v}

def branchDerivative (R : ReturnFlow C) (a : ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  GenericReturnBaseEigenbasis.stateDerivative R.ψ R.τ (branchReturnData C a)

def parameterVector (R : ReturnFlow C) (a : ℝ) : ι → ℝ :=
  fderiv ℝ (returnPoint R.ψ R.τ) (branchReturnData C a) ((0,1),0)

theorem branchFDeriv_smooth (R : ReturnFlow C) :
    ContDiffAt ℝ ⊤ (fun a => fderiv ℝ (returnPoint R.ψ R.τ) (branchReturnData C a)) 0 := by
  have hs := R.point_smooth.fderiv_right (m := ⊤) (by simp)
  have hs' : ContDiffAt ℝ ⊤ (fderiv ℝ (returnPoint R.ψ R.τ)) (branchReturnData C 0) := by
    simpa only [branchReturnData_zero] using hs
  exact hs'.comp 0 (branchReturnData_smooth C)

theorem branchDerivative_smooth (R : ReturnFlow C) : ContDiffAt ℝ ⊤ (branchDerivative R) 0 := by
  exact (((ContinuousLinearMap.compL ℝ (ι → ℝ) (ReturnData (ι → ℝ)) (ι → ℝ)).contDiff.contDiffAt.comp 0
    (branchFDeriv_smooth R)).clm_apply contDiffAt_const)

theorem parameterVector_smooth (R : ReturnFlow C) : ContDiffAt ℝ ⊤ (parameterVector R) 0 :=
  (branchFDeriv_smooth R).clm_apply contDiffAt_const

theorem parameterVector_zero (R : ReturnFlow C) : parameterVector R 0=
    fderiv ℝ (returnPoint R.ψ R.τ) ((0,r),GenericComplexification.realPart v) ((0,1),0) := by
  simp only [parameterVector,branchReturnData_zero]

theorem branchDerivative_zero (R : ReturnFlow C) : branchDerivative R 0=
    GenericReturnBaseEigenbasis.stateDerivative R.ψ R.τ
      ((0,r),GenericComplexification.realPart v) := by
  simp only [branchDerivative,branchReturnData_zero]

/-- The actual branch and scaling equations give the radial vector identity
for the derivative of the residual-defined return map. -/
theorem radial_vector_identity (R : ReturnFlow C)
    (hK : ∀ i j k, ContDiff ℝ ⊤ (fun s => K s i j k)) :
    ∀ᶠ a in 𝓝 (0:ℝ),
      branchDerivative R a (radialVector C a)-radialVector C a=
        (-a*deriv (kineticParameter C) a) • parameterVector R a := by
  have hid := closed_return_branch_vector_identity A0 D _ r w v C R.ψ R.τ R.point_smooth
    (R.scaling hK) (R.branch_closed.mono (fun _ ha => ha.2))
  have hC := (C.parameters_smooth.of_le (show (1:WithTop ℕ∞) ≤ ⊤ by simp)).eventually (by simp)
  have hp := (R.point_smooth.of_le (show (1:WithTop ℕ∞) ≤ ⊤ by simp)).eventually (by simp)
  have ht : Tendsto (branchReturnData C) (𝓝 (0:ℝ))
      (𝓝 ((0,r),GenericComplexification.realPart v)) := by
    simpa only [branchReturnData_zero] using (branchReturnData_smooth C).continuousAt.tendsto
  filter_upwards [hid,hC,ht.eventually hp] with a ha hca hpa
  have hdr : deriv (kineticParameter C) a=(deriv C.parameters a).2.re :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt a
      (hca.differentiableAt (by norm_num)).hasDerivAt.snd).deriv
  let d : ReturnVariables ι := (a,((C.parameters a).2.re,(C.parameters a).1))
  have hd : DifferentiableAt ℝ (returnPoint R.ψ R.τ) (returnReorder d) :=
    hpa.differentiableAt (by norm_num)
  have hstate (y : ι → ℝ) :
      fderiv ℝ (returnMap R.ψ R.τ) d (0,(0,y))=branchDerivative R a y := by
    rw [returnMap_fderiv_reorder R.ψ R.τ d hd]
    rfl
  have hparam : fderiv ℝ (returnMap R.ψ R.τ) d (0,(1,0))=parameterVector R a := by
    rw [returnMap_fderiv_reorder R.ψ R.τ d hd]
    rfl
  have h := ha.2.2
  change fderiv ℝ (returnMap R.ψ R.τ) d (0,(0,radialVector C a))-radialVector C a=
    (-a*(deriv C.parameters a).2.re) • fderiv ℝ (returnMap R.ψ R.τ) d (0,(1,0)) at h
  rw [hstate,hparam,← hdr] at h
  exact h

end
end ThreeSitePhosphorylation.GenericReturnLinearization
