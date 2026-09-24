import proofs.ThreeSitePhosphorylation.GenericTensorDerivative
import proofs.ThreeSitePhosphorylation.GenericAmplitudeVariation

namespace ThreeSitePhosphorylation.GenericTensorSecondVariation
noncomputable section
open Filter
open scoped Topology
open GenericAffinePathResidual GenericVariationalODE
set_option maxHeartbeats 700000

section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem smooth_eventually_deriv {f : ℝ → E} (h : ContDiffAt ℝ ⊤ f 0) :
    ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt f (deriv f s) s := by
  filter_upwards [(h.of_le (show (1 : WithTop ℕ∞) ≤ ⊤ by simp)).eventually (by norm_num)] with s hs
  exact (hs.differentiableAt (by norm_num)).hasDerivAt

theorem smooth_second_deriv {f : ℝ → E} (h : ContDiffAt ℝ ⊤ f 0) :
    HasDerivAt (deriv f) (deriv (deriv f) 0) 0 :=
  ((h.derivWithin (m := 1) (by simp)).differentiableAt (by norm_num)).hasDerivAt

theorem second_deriv_add (f g : ℝ → E) (hf : ContDiffAt ℝ ⊤ f 0)
    (hg : ContDiffAt ℝ ⊤ g 0) :
    deriv (deriv (fun s => f s + g s)) 0 = deriv (deriv f) 0 + deriv (deriv g) 0 := by
  have he : deriv (fun s => f s + g s) =ᶠ[𝓝 (0 : ℝ)] fun s => deriv f s + deriv g s := by
    filter_upwards [smooth_eventually_deriv hf, smooth_eventually_deriv hg] with s hs ht
    exact (hs.add ht).deriv
  rw [he.deriv_eq]
  exact ((smooth_second_deriv hf).add (smooth_second_deriv hg)).deriv

theorem second_deriv_smul (a : ℝ → ℝ) (f : ℝ → E)
    (ha : ContDiffAt ℝ ⊤ a 0) (hf : ContDiffAt ℝ ⊤ f 0) :
    deriv (deriv (fun s => a s • f s)) 0 =
      a 0 • deriv (deriv f) 0 + (2 * deriv a 0) • deriv f 0 +
        deriv (deriv a) 0 • f 0 := by
  have he : deriv (fun s => a s • f s) =ᶠ[𝓝 (0 : ℝ)]
      fun s => a s • deriv f s + deriv a s • f s := by
    filter_upwards [smooth_eventually_deriv ha, smooth_eventually_deriv hf] with s hs ht
    exact (hs.smul ht).deriv
  rw [he.deriv_eq]
  have hh := (((ha.differentiableAt (by simp)).hasDerivAt).smul (smooth_second_deriv hf)).add
    ((smooth_second_deriv ha).smul ((hf.differentiableAt (by simp)).hasDerivAt))
  convert hh.deriv using 1
  module

theorem second_deriv_clm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] G) (f : ℝ → E) (hf : ContDiffAt ℝ ⊤ f 0) :
    deriv (deriv (fun s => L (f s))) 0 = L (deriv (deriv f) 0) := by
  have he : deriv (fun s => L (f s)) =ᶠ[𝓝 (0 : ℝ)] fun s => L (deriv f s) := by
    filter_upwards [smooth_eventually_deriv hf] with s hs
    exact (L.hasFDerivAt.comp_hasDerivAt s hs).deriv
  rw [he.deriv_eq]
  exact (L.hasFDerivAt.comp_hasDerivAt 0 (smooth_second_deriv hf)).deriv
end Calculus

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The literal tensor bilinear map applied pointwise to two continuous paths. -/
def pathHessian (H : GenericQuadraticTensor.Tensor ι)
    (u v : ContinuousPath (ι → ℝ)) : ContinuousPath (ι → ℝ) :=
  ⟨fun t => GenericTensorDerivative.realContinuousBilinear H (u t) (v t),
    ((GenericTensorDerivative.realContinuousBilinear H).continuous.comp u.continuous).clm_apply
      v.continuous⟩

@[simp] theorem pathHessian_apply (H : GenericQuadraticTensor.Tensor ι)
    (u v : ContinuousPath (ι → ℝ)) (t : UnitTime) :
    pathHessian H u v t=GenericTensorDerivative.realContinuousBilinear H (u t) (v t) := rfl

/-- The parameter really varies. Its contribution disappears because R'(0)=0,
as checked by the joint derivative before using the fixed-parameter Hessian. -/
theorem pathQuadratic_curve_stationary_parameter
    (H : ℝ → GenericQuadraticTensor.Tensor ι)
    (hH : ∀ i j k, ContDiff ℝ ⊤ (fun r => H r i j k))
    (R : ℝ → ℝ) (u : ℝ → ContinuousPath (ι → ℝ)) (v : ContinuousPath (ι → ℝ))
    (hR : HasDerivAt R 0 0) (hu : HasDerivAt u v 0)
    (hsym : ∀ i j k, H (R 0) i j k=H (R 0) i k j) :
    HasDerivAt (fun s => GenericQuadraticTensor.pathField H (R s) (u s))
      (pathHessian (H (R 0)) (u 0) v) 0 := by
  let F := fun p : ℝ × ContinuousPath (ι → ℝ) => GenericQuadraticTensor.pathField H p.1 p.2
  let J := fderiv ℝ F (R 0,u 0)
  have hF : HasFDerivAt F J (R 0,u 0) :=
    ((GenericQuadraticTensor.pathField_smooth H hH).differentiable (by simp) _).hasFDerivAt
  have hd : HasDerivAt (fun s => GenericQuadraticTensor.pathField H (R s) (u s))
      (J (0,v)) 0 := by
    simpa only [F,Function.comp_def] using hF.comp_hasDerivAt 0 (hR.prodMk hu)
  have he : J (0,v)=pathHessian (H (R 0)) (u 0) v := by
    apply ContinuousMap.ext
    intro t
    let ev := ContinuousMap.evalCLM (R := ℝ) (M := ι → ℝ) t
    have hu' : HasDerivAt (fun s => u s t) (v t) 0 :=
      ev.hasFDerivAt.comp_hasDerivAt 0 hu
    have hev : HasDerivAt
        (fun s => GenericQuadraticTensor.field H (R s) (u s t)) (J (0,v) t) 0 := by
      simpa only [ev,ContinuousMap.evalCLM_apply,Function.comp_def,GenericQuadraticTensor.pathField_apply] using
        ev.hasFDerivAt.comp_hasDerivAt 0 hd
    let G := fun p : ℝ × (ι → ℝ) => GenericQuadraticTensor.field H p.1 p.2
    let K := fderiv ℝ G (R 0,u 0 t)
    have hG : HasFDerivAt G K (R 0,u 0 t) :=
      ((GenericQuadraticTensor.field_smooth H hH).differentiable (by simp) _).hasFDerivAt
    have hvar : HasDerivAt (fun s => GenericQuadraticTensor.field H (R s) (u s t))
        (K (0,v t)) 0 := by
      simpa only [G,Function.comp_def] using hG.comp_hasDerivAt 0 (hR.prodMk hu')
    have hfixed : HasDerivAt (fun s => GenericQuadraticTensor.field H (R 0) (u s t))
        (K (0,v t)) 0 := by
      simpa only [G,Function.comp_def] using
        hG.comp_hasDerivAt 0 ((hasDerivAt_const (x := (0:ℝ)) (c := R 0)).prodMk hu')
    have hb := (GenericTensorDerivative.field_hasFDerivAt H (R 0) hsym (u 0 t)).comp_hasDerivAt 0 hu'
    exact (hev.unique hvar).trans (hfixed.unique hb)
  rw [← he]
  exact hd

def pathField (A0 D : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (H : ℝ → GenericQuadraticTensor.Tensor ι)
    (a r T : ℝ) (u : ContinuousPath (ι → ℝ)) : ContinuousPath (ι → ℝ) :=
  T • (pathLinear A0 D r u+a • GenericQuadraticTensor.pathField H r u)

theorem pathField_curve_second_derivative (A0 D : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (H : ℝ → GenericQuadraticTensor.Tensor ι)
    (hH : ∀ i j k, ContDiff ℝ ⊤ (fun r => H r i j k))
    (R T : ℝ → ℝ) (u : ℝ → ContinuousPath (ι → ℝ))
    (hR : ContDiffAt ℝ ⊤ R 0) (hT : ContDiffAt ℝ ⊤ T 0)
    (hu : ContDiffAt ℝ ⊤ u 0) (hR0 : deriv R 0=0) (hT0 : deriv T 0=0)
    (hsym : ∀ i j k, H (R 0) i j k=H (R 0) i k j) :
    HasDerivAt (deriv (fun s => pathField A0 D H s (R s) (T s) (u s)))
      (T 0 • pathLinear A0 D (R 0) (deriv (deriv u) 0)+
        deriv (deriv T) 0 • pathLinear A0 D (R 0) (u 0)+
        T 0 • (deriv (deriv R) 0 • D.compLeftContinuous ℝ UnitTime (u 0))+
        (2*T 0) • pathHessian (H (R 0)) (u 0) (deriv u 0)) 0 := by
  let L := A0.compLeftContinuous ℝ UnitTime
  let Δ := D.compLeftContinuous ℝ UnitTime
  let q := fun s => GenericQuadraticTensor.pathField H (R s) (u s)
  let l := fun s => L (u s)+R s • Δ (u s)
  have hq : ContDiffAt ℝ ⊤ q 0 :=
    (GenericQuadraticTensor.pathField_smooth H hH).contDiffAt.comp 0 (hR.prodMk hu)
  have hd : ContDiffAt ℝ ⊤ (fun s => Δ (u s)) 0 := Δ.contDiff.contDiffAt.comp 0 hu
  have hL : ContDiffAt ℝ ⊤ (fun s => L (u s)) 0 := L.contDiff.contDiffAt.comp 0 hu
  have hl : ContDiffAt ℝ ⊤ l 0 := hL.add (hR.smul hd)
  have hl2 : deriv (deriv l) 0=pathLinear A0 D (R 0) (deriv (deriv u) 0)+
      deriv (deriv R) 0 • Δ (u 0) := by
    dsimp only [l]
    rw [second_deriv_add (fun s => L (u s)) (fun s => R s • Δ (u s)) hL (hR.smul hd),second_deriv_clm L u hu,
      second_deriv_smul R (fun s => Δ (u s)) hR hd,second_deriv_clm Δ u hu,hR0]
    simp only [mul_zero,zero_smul,add_zero,pathLinear_decompose,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,L,Δ]
    module
  have hq1 : deriv q 0=pathHessian (H (R 0)) (u 0) (deriv u 0) :=
    (pathQuadratic_curve_stationary_parameter H hH R u (deriv u 0)
      (by simpa only [hR0] using (hR.differentiableAt (by simp)).hasDerivAt)
      (hu.differentiableAt (by simp)).hasDerivAt hsym).deriv
  have hs : ContDiffAt ℝ ⊤ (fun s : ℝ => s) 0 := contDiffAt_id
  have hi : ContDiffAt ℝ ⊤ (fun s => l s+s • q s) 0 := hl.add (hs.smul hq)
  have hf : ContDiffAt ℝ ⊤ (fun s => T s • (l s+s • q s)) 0 := hT.smul hi
  have hfun : (fun s => pathField A0 D H s (R s) (T s) (u s))=
      (fun s => T s • (l s+s • q s)) := by
    funext s
    simp only [pathField,l,q,L,Δ,pathLinear_decompose,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply]
  rw [hfun]
  convert smooth_second_deriv hf using 1
  rw [second_deriv_smul T _ hT hi,hT0,second_deriv_add l (fun s : ℝ => s • q s) hl (hs.smul hq),
    second_deriv_smul (fun s : ℝ => s) q hs hq,hl2,hq1]
  simp only [deriv_id'',deriv_const,zero_smul,zero_add,mul_zero,add_zero,mul_one]
  have hl0 : l 0=pathLinear A0 D (R 0) (u 0) := by
    simp only [l,L,Δ,pathLinear_decompose,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply]
  rw [hl0]
  module

/-- Twice differentiate the actual residual. No second-variation equation
is supplied as an input. -/
theorem second_variational_curve_equation (A0 D : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (H : ℝ → GenericQuadraticTensor.Tensor ι)
    (hH : ∀ i j k, ContDiff ℝ ⊤ (fun r => H r i j k))
    (R T : ℝ → ℝ) (x : ℝ → (ι → ℝ)) (u : ℝ → ContinuousPath (ι → ℝ))
    (hR : ContDiffAt ℝ ⊤ R 0) (hT : ContDiffAt ℝ ⊤ T 0)
    (hx : ContDiffAt ℝ ⊤ x 0) (hu : ContDiffAt ℝ ⊤ u 0)
    (hR0 : deriv R 0=0) (hT0 : deriv T 0=0)
    (hsym : ∀ i j k, H (R 0) i j k=H (R 0) i k j)
    (he : ∀ᶠ s in 𝓝 (0:ℝ), GenericAffinePathResidual.pathResidual A0 D
      (GenericQuadraticTensor.pathField H) (((s,(R s,T s)),x s),u s)=0) :
    deriv (deriv u) 0=constantPath (deriv (deriv x) 0)+
      linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ))
        (T 0 • pathLinear A0 D (R 0) (deriv (deriv u) 0)+
          deriv (deriv T) 0 • pathLinear A0 D (R 0) (u 0)+
          T 0 • (deriv (deriv R) 0 • D.compLeftContinuous ℝ UnitTime (u 0))+
          (2*T 0) • pathHessian (H (R 0)) (u 0) (deriv u 0)) := by
  let f := fun s => pathField A0 D H s (R s) (T s) (u s)
  let P := linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ))
  have hf : ContDiffAt ℝ ⊤ f 0 := by
    have hL := (A0.compLeftContinuous ℝ UnitTime).contDiff.contDiffAt.comp 0 hu
    have hD := (D.compLeftContinuous ℝ UnitTime).contDiff.contDiffAt.comp 0 hu
    have hQ := (GenericQuadraticTensor.pathField_smooth H hH).contDiffAt.comp 0 (hR.prodMk hu)
    simpa only [f,pathField,pathLinear_decompose,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply] using
      hT.smul ((hL.add (hR.smul hD)).add (contDiffAt_id.smul hQ))
  have hc := (constantPath (E := ι → ℝ)).contDiff.contDiffAt.comp 0 hx
  have hP := P.contDiff.contDiffAt.comp 0 hf
  simp only [Function.comp_def] at hc hP
  have he' : u =ᶠ[𝓝 (0:ℝ)] fun s => constantPath (x s)+P (f s) := by
    filter_upwards [he] with s hs
    change u s-constantPath (x s)-T s • P
      (pathLinear A0 D (R s) (u s)+s • GenericQuadraticTensor.pathField H (R s) (u s))=0 at hs
    rw [← map_smul] at hs
    exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hs)).trans (add_comm _ _)
  have hh := he'.deriv.deriv_eq
  rw [second_deriv_add _ _ hc hP,second_deriv_clm constantPath x hx,
    second_deriv_clm P f hf] at hh
  have hd := (pathField_curve_second_derivative A0 D H hH R T u hR hT hu hR0 hT0 hsym).deriv
  rw [hd] at hh
  exact hh

end
end ThreeSitePhosphorylation.GenericTensorSecondVariation

