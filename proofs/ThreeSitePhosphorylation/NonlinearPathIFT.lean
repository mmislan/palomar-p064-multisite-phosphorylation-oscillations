import proofs.ThreeSitePhosphorylation.VariableVolterra

/-! A full-interval path IFT at a supplied nonlinear reference path.
The smooth Nemytskii lift is an explicit input, not constructed here. -/
namespace ThreeSitePhosphorylation
noncomputable section
open scoped Topology
open MeasureTheory
set_option maxHeartbeats 500000

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev NonlinearPathData (P E : Type*) := (P × ℝ) × E

def nonlinearPathResidual (B : P → ContinuousPath E → ContinuousPath E)
    (d : NonlinearPathData P E × ContinuousPath E) : ContinuousPath E :=
  d.2-ContinuousLinearMap.const ℝ UnitTime d.1.2-
    d.1.1.2 • linearPicard (ContinuousLinearMap.id ℝ E) (B d.1.1.1 d.2)

theorem nonlinearPathResidual_smooth
    (B : P → ContinuousPath E → ContinuousPath E)
    (hB : ContDiff ℝ ⊤ (fun p : P × ContinuousPath E => B p.1 p.2)) :
    ContDiff ℝ ⊤ (nonlinearPathResidual B) := by
  have hb : ContDiff ℝ ⊤ (fun d : NonlinearPathData P E × ContinuousPath E =>
      B d.1.1.1 d.2) :=
    hB.comp (contDiff_fst.fst.fst.prodMk contDiff_snd)
  have hi := (linearPicard (ContinuousLinearMap.id ℝ E)).contDiff.comp hb
  have hx : ContDiff ℝ ⊤ (fun d : NonlinearPathData P E × ContinuousPath E =>
      ContinuousLinearMap.const ℝ UnitTime d.1.2) :=
    (ContinuousLinearMap.const ℝ UnitTime : E →L[ℝ] ContinuousPath E).contDiff.comp
      (f := fun d : NonlinearPathData P E × ContinuousPath E => d.1.2) contDiff_fst.snd
  exact (contDiff_snd.sub hx).sub (contDiff_fst.fst.snd.smul hi)

theorem nonlinearField_slice_smooth (F : P → E → E)
    (hF : ContDiff ℝ ⊤ (fun p : P × E => F p.1 p.2)) (p : P) :
    ContDiff ℝ ⊤ (F p) :=
  hF.comp (f := fun x : E => (p,x)) (contDiff_const.prodMk contDiff_id)

/-- The coefficient is the actual state derivative along the supplied path. -/
def nonlinearPathCoefficient (F : P → E → E)
    (hF : ContDiff ℝ ⊤ (fun p : P × E => F p.1 p.2))
    (p : P) (T : ℝ) (u : ContinuousPath E) : ContinuousPath (E →L[ℝ] E) :=
  ⟨fun t => T • fderiv ℝ (F p) (u t),
    continuous_const.smul
      (((nonlinearField_slice_smooth F hF p).continuous_fderiv (by simp)).comp u.continuous)⟩

/-- Differentiate the supplied lift by composing with bounded evaluation.
This identifies its derivative with the actual source derivative pointwise. -/
theorem nonlinearPathField_derivative_eval (F : P → E → E)
    (B : P → ContinuousPath E → ContinuousPath E)
    (hF : ContDiff ℝ ⊤ (fun p : P × E => F p.1 p.2))
    (hB : ContDiff ℝ ⊤ (fun p : P × ContinuousPath E => B p.1 p.2))
    (hpoint : ∀ p u t, B p u t = F p (u t))
    (p : P) (u v : ContinuousPath E) (t : UnitTime) :
    fderiv ℝ (B p) u v t = fderiv ℝ (F p) (u t) (v t) := by
  let ev := ContinuousMap.evalCLM (R := ℝ) (M := E) t
  have hbs : ContDiff ℝ ⊤ (B p) := hB.comp (contDiff_const.prodMk contDiff_id)
  have hl := ev.hasFDerivAt.comp u ((hbs.differentiable (by simp) u).hasFDerivAt)
  have hr := ((nonlinearField_slice_smooth F hF p).differentiable (by simp) (u t)).hasFDerivAt.comp
    u ev.hasFDerivAt
  have he : (fun w : ContinuousPath E => ev (B p w)) = (fun w => F p (ev w)) :=
    funext (fun w => hpoint p w t)
  simp only [Function.comp_def] at hl hr
  rw [he] at hl
  exact DFunLike.congr_fun (hl.unique hr) v

theorem nonlinearPathPicard_derivative (F : P → E → E)
    (B : P → ContinuousPath E → ContinuousPath E)
    (hF : ContDiff ℝ ⊤ (fun p : P × E => F p.1 p.2))
    (hB : ContDiff ℝ ⊤ (fun p : P × ContinuousPath E => B p.1 p.2))
    (hpoint : ∀ p u t, B p u t = F p (u t))
    (p : P) (T : ℝ) (u : ContinuousPath E) :
    T • ((linearPicard (ContinuousLinearMap.id ℝ E)).comp (fderiv ℝ (B p) u)) =
      variablePicard (nonlinearPathCoefficient F hF p T u) := by
  ext v t
  change T • (∫ s in (0:ℝ)..(t:ℝ), pathExtension (fderiv ℝ (B p) u v) s) =
    ∫ s in (0:ℝ)..(t:ℝ),
      variablePicardIntegrand (nonlinearPathCoefficient F hF p T u) v s
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [variablePicardIntegrand,pathExtension,nonlinearPathCoefficient,
    ContinuousMap.coe_mk,ContinuousLinearMap.smul_apply]
  rw [nonlinearPathField_derivative_eval F B hF hB hpoint]

theorem nonlinearPathResidual_path_derivative (F : P → E → E)
    (B : P → ContinuousPath E → ContinuousPath E)
    (hF : ContDiff ℝ ⊤ (fun p : P × E => F p.1 p.2))
    (hB : ContDiff ℝ ⊤ (fun p : P × ContinuousPath E => B p.1 p.2))
    (hpoint : ∀ p u t, B p u t = F p (u t))
    (d : NonlinearPathData P E) (u : ContinuousPath E) :
    fderiv ℝ (nonlinearPathResidual B) (d,u) ∘L
      ContinuousLinearMap.inr ℝ (NonlinearPathData P E) (ContinuousPath E) =
      1-variablePicard (nonlinearPathCoefficient F hF d.1.1 d.1.2 u) := by
  have hi : HasFDerivAt (fun v : ContinuousPath E => (d,v))
      (ContinuousLinearMap.inr ℝ (NonlinearPathData P E) (ContinuousPath E)) u := by
    convert (hasFDerivAt_const (𝕜 := ℝ) d u).prodMk (hasFDerivAt_id u) using 1
  have hj := ((nonlinearPathResidual_smooth B hB).differentiable (by simp) (d,u)).hasFDerivAt.comp u hi
  have hbs : ContDiff ℝ ⊤ (B d.1.1) := hB.comp (contDiff_const.prodMk contDiff_id)
  have hb := (hbs.differentiable (by simp) u).hasFDerivAt
  have hl := (linearPicard (ContinuousLinearMap.id ℝ E)).hasFDerivAt.comp u hb
  have hd := ((hasFDerivAt_id u).sub_const (ContinuousLinearMap.const ℝ UnitTime d.2)).sub
    (hl.const_smul d.1.2)
  have he : fderiv ℝ (nonlinearPathResidual B) (d,u) ∘L
      ContinuousLinearMap.inr ℝ (NonlinearPathData P E) (ContinuousPath E) =
      ContinuousLinearMap.id ℝ (ContinuousPath E) -
        d.1.2 • ((linearPicard (ContinuousLinearMap.id ℝ E)).comp
          (fderiv ℝ (B d.1.1) u)) := hj.unique hd
  rw [he,nonlinearPathPicard_derivative F B hF hB hpoint]
  rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The lifted residual is literally the source integral equation. -/
theorem nonlinearPathResidual_source (F : P → E → E)
    (B : P → ContinuousPath E → ContinuousPath E)
    (hpoint : ∀ p u t, B p u t = F p (u t))
    (d : NonlinearPathData P E) (u : ContinuousPath E)
    (hu : nonlinearPathResidual B (d,u)=0) (t : UnitTime) :
    u t = d.2+∫ s in (0:ℝ)..(t:ℝ), d.1.2 • F d.1.1 (pathExtension u s) := by
  have hh : u = ContinuousLinearMap.const ℝ UnitTime d.2 +
      d.1.2 • linearPicard (ContinuousLinearMap.id ℝ E) (B d.1.1 u) := by
    have he := sub_eq_iff_eq_add.mp (sub_eq_zero.mp hu)
    simpa only [add_comm] using he
  have he := congrArg (fun v : ContinuousPath E => v t) hh
  change u t = d.2+d.1.2 • (∫ s in (0:ℝ)..(t:ℝ), pathExtension (B d.1.1 u) s) at he
  rw [he,← intervalIntegral.integral_smul]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  simp only [pathExtension,hpoint]

/-- Smooth solutions and local uniqueness near any supplied nonlinear
reference path satisfying the full-interval integral equation. The smooth
Nemytskii lift B, including its pointwise source identity, is explicit input. -/
theorem smooth_nonlinear_full_interval_paths [CompleteSpace P] [CompleteSpace E] (F : P → E → E)
    (B : P → ContinuousPath E → ContinuousPath E)
    (hF : ContDiff ℝ ⊤ (fun p : P × E => F p.1 p.2))
    (hB : ContDiff ℝ ⊤ (fun p : P × ContinuousPath E => B p.1 p.2))
    (hpoint : ∀ p u t, B p u t = F p (u t))
    (d : NonlinearPathData P E) (u : ContinuousPath E)
    (hu : nonlinearPathResidual B (d,u)=0) :
    ∃ ψ : NonlinearPathData P E → ContinuousPath E,
      ContDiffAt ℝ ⊤ ψ d ∧ ψ d=u ∧
      (∀ᶠ p in 𝓝 d, nonlinearPathResidual B (p,ψ p)=0) ∧
      (∀ᶠ p in 𝓝 (d,u), nonlinearPathResidual B p=0 ↔ ψ p.1=p.2) ∧
      (∀ᶠ p in 𝓝 d, ∀ t : UnitTime,
        ψ p t=p.2+∫ s in (0:ℝ)..(t:ℝ), p.1.2 • F p.1.1 (pathExtension (ψ p) s)) := by
  have hi : (fderiv ℝ (nonlinearPathResidual B) (d,u) ∘L
      ContinuousLinearMap.inr ℝ (NonlinearPathData P E) (ContinuousPath E)).IsInvertible := by
    rw [nonlinearPathResidual_path_derivative F B hF hB hpoint]
    obtain ⟨v,hv⟩ := variablePicard_one_sub_isUnit (nonlinearPathCoefficient F hF d.1.1 d.1.2 u)
    exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ (ContinuousPath E) v,hv⟩
  let h := (nonlinearPathResidual_smooth B hB).contDiffAt (x := (d,u))
  let ψ := h.implicitFunction (by simp) hi
  have hz : ∀ᶠ p in 𝓝 d, nonlinearPathResidual B (p,ψ p)=0 := by
    simpa only [hu] using h.eventually_apply_implicitFunction (by simp) hi
  refine ⟨ψ,h.contDiffAt_implicitFunction (by simp) hi,
    h.implicitFunction_apply_self (by simp) hi,hz,?_,?_⟩
  · simpa only [hu] using h.eventually_apply_eq_iff_implicitFunction (by simp) hi
  · filter_upwards [hz] with p hp
    exact nonlinearPathResidual_source F B hpoint p (ψ p) hp

end
end ThreeSitePhosphorylation
