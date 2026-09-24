import proofs.ThreeSitePhosphorylation.GenericShootingMap
import proofs.ThreeSitePhosphorylation.GenericVariationalODE

namespace ThreeSitePhosphorylation.GenericAffinePathResidual
noncomputable section
open scoped Topology
open GenericVariationalODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def pathLinear (A0 D : E →L[ℝ] E) (r : ℝ) :
    ContinuousPath E →L[ℝ] ContinuousPath E :=
  (A0+r • D).compLeftContinuous ℝ UnitTime

theorem pathLinear_decompose (A0 D : E →L[ℝ] E) (r : ℝ) :
    pathLinear A0 D r=A0.compLeftContinuous ℝ UnitTime+
      r • D.compLeftContinuous ℝ UnitTime := by
  ext u t
  rfl

/-- Literal amplitude-rescaled residual. B is an arbitrary path map here;
at amplitude zero its contribution vanishes without a smoothness assumption. -/
def pathResidual (A0 D : E →L[ℝ] E)
    (B : ℝ → ContinuousPath E → ContinuousPath E)
    (p : GenericShootingMap.FlowData E × ContinuousPath E) : ContinuousPath E :=
  p.2-constantPath p.1.2-p.1.1.2.2 • linearPicard (ContinuousLinearMap.id ℝ E)
    (pathLinear A0 D p.1.1.2.1 p.2+p.1.1.1 • B p.1.1.2.1 p.2)

theorem pathLinear_direction (A0 D : E →L[ℝ] E) (r dr : ℝ)
    (u : ℝ → ContinuousPath E) (q : ContinuousPath E) (hu : HasDerivAt u q 0) :
    HasDerivAt (fun s => pathLinear A0 D (r+s*dr) (u s))
      (pathLinear A0 D r q+dr • D.compLeftContinuous ℝ UnitTime (u 0)) 0 := by
  have hr : HasDerivAt (fun s : ℝ => r+s*dr) dr 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const dr).const_add r
  have h0 := (A0.compLeftContinuous ℝ UnitTime).hasFDerivAt.comp_hasDerivAt 0 hu
  have hd := (D.compLeftContinuous ℝ UnitTime).hasFDerivAt.comp_hasDerivAt 0 hu
  have hh := h0.add (hr.smul hd)
  simpa only [pathLinear_decompose,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,zero_mul,add_zero,Function.comp_def,add_assoc] using hh

theorem duration_linear_direction (A0 D : E →L[ℝ] E) (r T dr dT : ℝ)
    (u : ℝ → ContinuousPath E) (q : ContinuousPath E) (hu : HasDerivAt u q 0) :
    HasDerivAt (fun s => (T+s*dT) • pathLinear A0 D (r+s*dr) (u s))
      (variationField (A0+r • D) D T dr dT (u 0) q) 0 := by
  have ht : HasDerivAt (fun s : ℝ => T+s*dT) dT 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const dT).const_add T
  have hh := ht.smul (pathLinear_direction A0 D r dr u q hu)
  convert hh using 1
  simp only [variationField,pathLinear,zero_mul,add_zero,smul_add]
  abel

/-- Differentiation of the actual zero-amplitude residual supplies the exact
integral equation consumed by GenericVariationalODE. -/
theorem variational_path_equation (A0 D : E →L[ℝ] E)
    (B : ℝ → ContinuousPath E → ContinuousPath E)
    (r T dr dT : ℝ) (x dx : E)
    (u : ℝ → ContinuousPath E) (q : ContinuousPath E) (hu : HasDerivAt u q 0)
    (he : ∀ᶠ s in 𝓝 (0:ℝ),
      pathResidual A0 D B (((0,(r+s*dr,T+s*dT)),x+s • dx),u s)=0) :
    q=constantPath dx+linearPicard (ContinuousLinearMap.id ℝ E)
      (variationField (A0+r • D) D T dr dT (u 0) q) := by
  have hx : HasDerivAt (fun s : ℝ => x+s • dx) dx 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const dx).const_add x
  have hc := (constantPath (E := E)).hasFDerivAt.comp_hasDerivAt 0 hx
  have hf := (linearPicard (ContinuousLinearMap.id ℝ E)).hasFDerivAt.comp_hasDerivAt 0
    (duration_linear_direction A0 D r T dr dT u q hu)
  have hh : HasDerivAt
      (fun s => pathResidual A0 D B (((0,(r+s*dr,T+s*dT)),x+s • dx),u s))
      (q-constantPath dx-linearPicard (ContinuousLinearMap.id ℝ E)
        (variationField (A0+r • D) D T dr dT (u 0) q)) 0 := by
    simpa only [pathResidual,zero_smul,add_zero,Function.comp_def,map_smul] using (hu.sub hc).sub hf
  have hz : HasDerivAt
      (fun s => pathResidual A0 D B (((0,(r+s*dr,T+s*dT)),x+s • dx),u s)) 0 0 :=
    (hasDerivAt_const (x := (0:ℝ)) (c := (0:ContinuousPath E))).congr_of_eventuallyEq he
  have hd := hh.unique hz
  exact sub_eq_iff_eq_add.mp (sub_eq_zero.mp hd) |>.trans (add_comm _ _)

end
end ThreeSitePhosphorylation.GenericAffinePathResidual
