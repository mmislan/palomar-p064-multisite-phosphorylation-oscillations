import proofs.ThreeSitePhosphorylation.GenericReturnScaling
import proofs.ThreeSitePhosphorylation.GenericClosedPaths

/-! Differentiating the actual return scaling and the fixed closed branch.
Both differential identities are derived from verified local identities of
the SAME residual-selected return map; neither is assumed. -/
namespace ThreeSitePhosphorylation.GenericReturnDerivative
noncomputable section
open scoped Topology
open GenericReturnIFT GenericReturnScaling

variable {ι : Type*} [Fintype ι]

abbrev ReturnVariables (ι : Type*) := ℝ × (ℝ × (ι → ℝ))

def returnMap (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (τ : ReturnData (ι → ℝ) → ℝ) (z : ReturnVariables ι) : ι → ℝ :=
  returnPoint ψ τ ((z.1,z.2.1),z.2.2)

theorem returnMap_smooth (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (τ : ReturnData (ι → ℝ) → ℝ) (z : ReturnVariables ι)
    (hs : ContDiffAt ℝ ⊤ (returnPoint ψ τ) ((z.1,z.2.1),z.2.2)) :
    ContDiffAt ℝ ⊤ (returnMap ψ τ) z := by
  exact hs.comp z (by fun_prop)

theorem return_scaling_euler (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (τ : ReturnData (ι → ℝ) → ℝ) (a r : ℝ) (x : ι → ℝ)
    (hD : DifferentiableAt ℝ (returnMap ψ τ) (a,(r,x)))
    (hscale : ∀ᶠ s in 𝓝 (1:ℝ),
      returnPoint ψ τ (scaleReturnData ((a,r),x) s)=s • returnPoint ψ τ ((a,r),x)) :
    fderiv ℝ (returnMap ψ τ) (a,(r,x)) (-a,(0,x))=returnMap ψ τ (a,(r,x)) := by
  have ha : HasDerivAt (fun s : ℝ => a/s) (-a) 1 := by
    simpa using (hasDerivAt_const (1:ℝ) a).div (hasDerivAt_id (1:ℝ)) (by norm_num)
  have hx : HasDerivAt (fun s : ℝ => s • x) x 1 := by
    simpa using (hasDerivAt_id (1:ℝ)).smul_const x
  have hl := ha.prodMk ((hasDerivAt_const (1:ℝ) r).prodMk hx)
  have hD' : HasFDerivAt (returnMap ψ τ) (fderiv ℝ (returnMap ψ τ) (a,(r,x)))
      (a/1,(r,(1:ℝ) • x)) := by simpa using hD.hasFDerivAt
  have hd := hD'.comp_hasDerivAt (1:ℝ) hl
  have hr : HasDerivAt (fun s : ℝ => returnMap ψ τ (a/s,(r,s • x)))
      (returnMap ψ τ (a,(r,x))) 1 :=
    HasDerivAt.congr_of_eventuallyEq
      (by simpa using (hasDerivAt_id (1:ℝ)).smul_const (returnMap ψ τ (a,(r,x)))) hscale
  exact hd.unique hr

theorem return_euler_eventually (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (τ : ReturnData (ι → ℝ) → ℝ) (r : ℝ) (x : ι → ℝ)
    (hs : ContDiffAt ℝ ⊤ (returnPoint ψ τ) ((0,r),x))
    (hscale : ∀ᶠ z in 𝓝 (((0,r),x),(1:ℝ)),
      τ (scaleReturnData z.1 z.2)=τ z.1 ∧
      returnPoint ψ τ (scaleReturnData z.1 z.2)=z.2 • returnPoint ψ τ z.1) :
    ∀ᶠ z in 𝓝 ((0:ℝ),(r,x)),
      DifferentiableAt ℝ (returnMap ψ τ) z ∧
      fderiv ℝ (returnMap ψ τ) z (-z.1,(0,z.2.2))=returnMap ψ τ z := by
  have hsm := returnMap_smooth ψ τ (0,(r,x)) hs
  have hd := (hsm.of_le (show (1:WithTop ℕ∞) ≤ ⊤ by simp)).eventually (by simp)
  have ht : Filter.Tendsto (fun z : ReturnVariables ι => ((z.1,z.2.1),z.2.2))
      (𝓝 (0,(r,x))) (𝓝 ((0,r),x)) := by
    exact (show ContinuousAt (fun z : ReturnVariables ι => ((z.1,z.2.1),z.2.2))
      (0,(r,x)) by fun_prop).tendsto
  filter_upwards [hd,ht.eventually hscale.curry_nhds] with z hz hsc
  have hdiff := hz.differentiableAt (by norm_num)
  refine ⟨hdiff,return_scaling_euler ψ τ z.1 z.2.1 z.2.2 hdiff ?_⟩
  exact hsc.mono (fun _ h => h.2)

omit [Fintype ι] in
/-- Euler scaling and differentiation of a fixed branch give the radial
state equation (the algebra of `AttractingScaling.branch_scaling_linear_identity`). -/
theorem branch_scaling_linear_identity {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : (ℝ × (ℝ × E)) →L[ℝ] E) (a r' : ℝ) (x x' : E)
    (hEuler : D (-a,(0,x))=x) (hBranch : D (1,(r',x'))=x') :
    D (0,(0,x+a • x'))-(x+a • x')=(-a*r') • D (0,(1,0)) := by
  have hv : ((0:ℝ),((0:ℝ),x+a • x'))=
      (-a,((0:ℝ),x))+a • ((1:ℝ),(r',x'))-(a*r') • ((0:ℝ),((1:ℝ),(0:E))) := by
    ext <;> simp
  rw [hv,map_sub,map_add,map_smul,map_smul,hEuler,hBranch]
  module

/-- The differential identities along the actual closed branch are obtained by
differentiating its verified fixed-point and scaling identities. -/
theorem closed_return_branch_vector_identity (A0 D : Matrix ι ι ℝ)
    (B : ℝ → ContinuousPath (ι → ℝ) → ContinuousPath (ι → ℝ))
    (r w : ℝ) (v : ι → ℂ) (C : GenericClosedPaths.ClosedPathFamily A0 D B r w v)
    (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (τ : ReturnData (ι → ℝ) → ℝ)
    (hs : ContDiffAt ℝ ⊤ (returnPoint ψ τ) ((0,r),GenericComplexification.realPart v))
    (hscale : ∀ᶠ z in 𝓝 (((0,r),GenericComplexification.realPart v),(1:ℝ)),
      τ (scaleReturnData z.1 z.2)=τ z.1 ∧
      returnPoint ψ τ (scaleReturnData z.1 z.2)=z.2 • returnPoint ψ τ z.1)
    (hfixed : ∀ᶠ a in 𝓝 (0:ℝ),
      returnPoint ψ τ ((a,(C.parameters a).2.re),(C.parameters a).1)=(C.parameters a).1) :
    ∀ᶠ a in 𝓝 (0:ℝ),
      let x := (C.parameters a).1
      let dx := (deriv C.parameters a).1
      let dr := (deriv C.parameters a).2.re
      let F := fderiv ℝ (returnMap ψ τ) (a,((C.parameters a).2.re,x))
      F (-a,(0,x))=x ∧ F (1,(dr,dx))=dx ∧
        F (0,(0,x+a • dx))-(x+a • dx)=(-a*dr) • F (0,(1,0)) := by
  let z := fun a : ℝ => (a,((C.parameters a).2.re,(C.parameters a).1))
  have hC := (C.parameters_smooth.of_le (show (1:WithTop ℕ∞) ≤ ⊤ by simp)).eventually (by simp)
  have hzc : ContinuousAt z 0 := by
    have hc := C.parameters_smooth.continuousAt
    exact continuousAt_id.prodMk ((Complex.reCLM.continuous.continuousAt.comp hc.snd).prodMk hc.fst)
  have hz0 : z 0=(0,(r,GenericComplexification.realPart v)) := by
    simp [z,C.parameters_zero]
  have ht := hzc.tendsto
  rw [hz0] at ht
  have hEuler := ht.eventually (return_euler_eventually ψ τ r _ hs hscale)
  filter_upwards [hC,hEuler,hfixed.eventually_nhds] with a ha he hfix
  let d := deriv C.parameters a
  have hd : HasDerivAt C.parameters d a := (ha.differentiableAt (by norm_num)).hasDerivAt
  have hx : HasDerivAt (fun a => (C.parameters a).1) d.1 a := hd.fst
  have hr : HasDerivAt (fun a => (C.parameters a).2.re) d.2.re a :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt a hd.snd
  have hline : HasDerivAt z (1,(d.2.re,d.1)) a :=
    (hasDerivAt_id a).prodMk (hr.prodMk hx)
  have hf := he.1.hasFDerivAt.comp_hasDerivAt a hline
  have hb := hf.unique (HasDerivAt.congr_of_eventuallyEq hx hfix)
  have hv := he.2.trans hfix.self_of_nhds
  exact ⟨hv,hb,branch_scaling_linear_identity _ a d.2.re (C.parameters a).1 d.1 hv hb⟩

end
end ThreeSitePhosphorylation.GenericReturnDerivative
