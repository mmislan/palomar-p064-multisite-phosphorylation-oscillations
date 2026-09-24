import proofs.ThreeSitePhosphorylation.GenericPolynomialFlow

/-! Explicit finite-tensor quadratic fields and their smooth path lifts.
The factor one half matches the Hessian convention F=Jx+(1/2)H(x,x).
Symmetry and identification with a particular source Hessian are separate. -/
namespace ThreeSitePhosphorylation.GenericQuadraticTensor
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Tensor (ι : Type*) := ι → ι → ι → ℝ
abbrev Row (ι : Type*) := ι × (ι × ι)

def direction (i : Row ι) : ι → ℝ := Pi.single i.1 1
def coefficient (H : ℝ → Tensor ι) (i : Row ι) (r : ℝ) : ℝ :=
  H r i.1 i.2.1 i.2.2/2
def firstCoordinate (i : Row ι) : (ι → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i.2.1
def secondCoordinate (i : Row ι) : (ι → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i.2.2

def field (H : ℝ → Tensor ι) : ℝ → (ι → ℝ) → (ι → ℝ) :=
  GenericPolynomialFlow.field direction (coefficient H) (fun _ _ => 0) (fun _ _ => 0)
    firstCoordinate secondCoordinate

def pathField (H : ℝ → Tensor ι) :
    ℝ → ContinuousPath (ι → ℝ) → ContinuousPath (ι → ℝ) :=
  GenericPolynomialFlow.pathField direction (coefficient H) (fun _ _ => 0) (fun _ _ => 0)
    firstCoordinate secondCoordinate

theorem field_smooth (H : ℝ → Tensor ι)
    (hH : ∀ i j k, ContDiff ℝ ⊤ (fun r => H r i j k)) :
    ContDiff ℝ ⊤ (fun p : ℝ × (ι → ℝ) => field H p.1 p.2) :=
  GenericPolynomialFlow.field_smooth direction (coefficient H) _ _ firstCoordinate secondCoordinate
    (fun i => (hH i.1 i.2.1 i.2.2).div_const 2)
    (fun _ => contDiff_const) (fun _ => contDiff_const)

theorem pathField_smooth (H : ℝ → Tensor ι)
    (hH : ∀ i j k, ContDiff ℝ ⊤ (fun r => H r i j k)) :
    ContDiff ℝ ⊤ (fun p : ℝ × ContinuousPath (ι → ℝ) => pathField H p.1 p.2) :=
  GenericPolynomialFlow.pathField_smooth direction (coefficient H) _ _ firstCoordinate secondCoordinate
    (fun i => (hH i.1 i.2.1 i.2.2).div_const 2)
    (fun _ => contDiff_const) (fun _ => contDiff_const)

theorem pathField_apply (H : ℝ → Tensor ι) (r : ℝ)
    (u : ContinuousPath (ι → ℝ)) (t : UnitTime) :
    pathField H r u t=field H r (u t) :=
  GenericPolynomialFlow.pathField_apply direction (coefficient H) _ _ firstCoordinate secondCoordinate r u t

theorem field_zero (H : ℝ → Tensor ι) (r : ℝ) : field H r 0=0 := by
  simp [field,GenericPolynomialFlow.field]

theorem field_smul (H : ℝ → Tensor ι) (r a : ℝ) (x : ι → ℝ) :
    field H r (a • x)=a^2 • field H r x := by
  unfold field GenericPolynomialFlow.field
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul]
  congr 1
  simp only [map_smul,smul_eq_mul,zero_add]
  ring

end
end ThreeSitePhosphorylation.GenericQuadraticTensor
