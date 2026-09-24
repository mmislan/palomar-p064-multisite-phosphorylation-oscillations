import proofs.ThreeSitePhosphorylation.GenericAffinePathResidual

namespace ThreeSitePhosphorylation.GenericAmplitudeVariation
noncomputable section
open scoped Topology
open GenericAffinePathResidual GenericVariationalODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem pathLinear_curve_direction (A0 D : E →L[ℝ] E)
    (R : ℝ → ℝ) (u : ℝ → ContinuousPath E) (dr : ℝ) (q : ContinuousPath E)
    (hr : HasDerivAt R dr 0) (hu : HasDerivAt u q 0) :
    HasDerivAt (fun s => pathLinear A0 D (R s) (u s))
      (pathLinear A0 D (R 0) q+dr • D.compLeftContinuous ℝ UnitTime (u 0)) 0 := by
  have h0 := (A0.compLeftContinuous ℝ UnitTime).hasFDerivAt.comp_hasDerivAt 0 hu
  have hd := (D.compLeftContinuous ℝ UnitTime).hasFDerivAt.comp_hasDerivAt 0 hu
  have hh := h0.add (hr.smul hd)
  simpa only [pathLinear_decompose,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,Function.comp_def,add_assoc] using hh

/-- Differentiate the actual duration-weighted path field along amplitude s.
The derivative of B itself is multiplied by zero at the base point. -/
theorem pathField_curve_direction (A0 D : E →L[ℝ] E)
    (B : ℝ → ContinuousPath E → ContinuousPath E)
    (R T : ℝ → ℝ) (u : ℝ → ContinuousPath E)
    (dr dT : ℝ) (q : ContinuousPath E)
    (hr : HasDerivAt R dr 0) (ht : HasDerivAt T dT 0) (hu : HasDerivAt u q 0)
    (hB : DifferentiableAt ℝ (fun p : ℝ × ContinuousPath E => B p.1 p.2) (R 0,u 0)) :
    HasDerivAt (fun s => T s • (pathLinear A0 D (R s) (u s)+s • B (R s) (u s)))
      (variationField (A0+(R 0) • D) D (T 0) dr dT (u 0) q+
        T 0 • B (R 0) (u 0)) 0 := by
  have hl := pathLinear_curve_direction A0 D R u dr q hr hu
  have hbc := hB.hasFDerivAt.comp_hasDerivAt 0 (hr.prodMk hu)
  have hh := ht.smul (hl.add ((hasDerivAt_id (0:ℝ)).smul hbc))
  convert hh using 1
  simp only [variationField,pathLinear,id_eq,Function.comp_def,Pi.add_apply,
    Pi.smul_apply',zero_smul,one_smul,add_zero,zero_add,smul_add]
  abel

/-- The full amplitude variation follows by differentiating an eventual
zero of the literal residual along arbitrary differentiable curves. -/
theorem amplitude_variational_curve_equation (A0 D : E →L[ℝ] E)
    (B : ℝ → ContinuousPath E → ContinuousPath E)
    (R T : ℝ → ℝ) (x : ℝ → E) (u : ℝ → ContinuousPath E)
    (dr dT : ℝ) (dx : E) (q : ContinuousPath E)
    (hr : HasDerivAt R dr 0) (ht : HasDerivAt T dT 0)
    (hx : HasDerivAt x dx 0) (hu : HasDerivAt u q 0)
    (hB : DifferentiableAt ℝ (fun p : ℝ × ContinuousPath E => B p.1 p.2) (R 0,u 0))
    (he : ∀ᶠ s in 𝓝 (0:ℝ), pathResidual A0 D B (((s,(R s,T s)),x s),u s)=0) :
    q=constantPath dx+linearPicard (ContinuousLinearMap.id ℝ E)
      (variationField (A0+(R 0) • D) D (T 0) dr dT (u 0) q+
        T 0 • B (R 0) (u 0)) := by
  have hc := (constantPath (E := E)).hasFDerivAt.comp_hasDerivAt 0 hx
  have hf := (linearPicard (ContinuousLinearMap.id ℝ E)).hasFDerivAt.comp_hasDerivAt 0
    (pathField_curve_direction A0 D B R T u dr dT q hr ht hu hB)
  have hh : HasDerivAt
      (fun s => pathResidual A0 D B (((s,(R s,T s)),x s),u s))
      (q-constantPath dx-linearPicard (ContinuousLinearMap.id ℝ E)
        (variationField (A0+(R 0) • D) D (T 0) dr dT (u 0) q+
          T 0 • B (R 0) (u 0))) 0 := by
    simpa only [pathResidual,Function.comp_def,map_smul] using (hu.sub hc).sub hf
  have hz : HasDerivAt
      (fun s => pathResidual A0 D B (((s,(R s,T s)),x s),u s)) 0 0 :=
    (hasDerivAt_const (x := (0:ℝ)) (c := (0:ContinuousPath E))).congr_of_eventuallyEq he
  have hd := hh.unique hz
  exact sub_eq_iff_eq_add.mp (sub_eq_zero.mp hd) |>.trans (add_comm _ _)

end
end ThreeSitePhosphorylation.GenericAmplitudeVariation
