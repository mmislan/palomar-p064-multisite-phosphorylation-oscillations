import proofs.ThreeSitePhosphorylation.GenericAffinePathResidual
import proofs.ThreeSitePhosphorylation.NonlinearPathIFT

namespace ThreeSitePhosphorylation.GenericAffinePathExistence
noncomputable section
open scoped Topology
open GenericAffinePathResidual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def toNonlinear (d : GenericShootingMap.FlowData E) : NonlinearPathData (ℝ × ℝ) E :=
  (((d.1.1,d.1.2.1),d.1.2.2),d.2)

def fromNonlinear (d : NonlinearPathData (ℝ × ℝ) E) : GenericShootingMap.FlowData E :=
  ((d.1.1.1,(d.1.1.2,d.1.2)),d.2)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem from_to (d : GenericShootingMap.FlowData E) : fromNonlinear (toNonlinear d)=d := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem to_from (d : NonlinearPathData (ℝ × ℝ) E) : toNonlinear (fromNonlinear d)=d := rfl

theorem toNonlinear_smooth : ContDiff ℝ ⊤ (toNonlinear (E := E)) := by
  unfold toNonlinear
  fun_prop

theorem fromNonlinear_smooth : ContDiff ℝ ⊤ (fromNonlinear (E := E)) := by
  unfold fromNonlinear
  fun_prop

def affineField (A0 D : E →L[ℝ] E) (Q : ℝ → E → E) (p : ℝ × ℝ) (x : E) : E :=
  (A0+p.2 • D) x+p.1 • Q p.2 x

def affineLift (A0 D : E →L[ℝ] E)
    (B : ℝ → ContinuousPath E → ContinuousPath E)
    (p : ℝ × ℝ) (u : ContinuousPath E) : ContinuousPath E :=
  pathLinear A0 D p.2 u+p.1 • B p.2 u

theorem affineField_smooth (A0 D : E →L[ℝ] E) (Q : ℝ → E → E)
    (hQ : ContDiff ℝ ⊤ (fun p : ℝ × E => Q p.1 p.2)) :
    ContDiff ℝ ⊤ (fun p : (ℝ × ℝ) × E => affineField A0 D Q p.1 p.2) := by
  have hq : ContDiff ℝ ⊤ (fun p : (ℝ × ℝ) × E => Q p.1.2 p.2) :=
    hQ.comp (contDiff_fst.snd.prodMk contDiff_snd)
  simpa only [affineField,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply] using
    ((A0.contDiff.comp contDiff_snd).add
      (contDiff_fst.snd.smul (D.contDiff.comp contDiff_snd))).add
      (contDiff_fst.fst.smul hq)

theorem affineLift_smooth (A0 D : E →L[ℝ] E)
    (B : ℝ → ContinuousPath E → ContinuousPath E)
    (hB : ContDiff ℝ ⊤ (fun p : ℝ × ContinuousPath E => B p.1 p.2)) :
    ContDiff ℝ ⊤ (fun p : (ℝ × ℝ) × ContinuousPath E => affineLift A0 D B p.1 p.2) := by
  have hb : ContDiff ℝ ⊤ (fun p : (ℝ × ℝ) × ContinuousPath E => B p.1.2 p.2) :=
    hB.comp (contDiff_fst.snd.prodMk contDiff_snd)
  simpa only [affineLift,pathLinear_decompose,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply] using
    (((A0.compLeftContinuous ℝ UnitTime).contDiff.comp contDiff_snd).add
      (contDiff_fst.snd.smul ((D.compLeftContinuous ℝ UnitTime).contDiff.comp contDiff_snd))).add
      (contDiff_fst.fst.smul hb)

theorem affineLift_apply (A0 D : E →L[ℝ] E) (Q : ℝ → E → E)
    (B : ℝ → ContinuousPath E → ContinuousPath E)
    (hpoint : ∀ r u t, B r u t=Q r (u t))
    (p : ℝ × ℝ) (u : ContinuousPath E) (t : UnitTime) :
    affineLift A0 D B p u t=affineField A0 D Q p (u t) := by
  change (A0+p.2 • D) (u t)+p.1 • B p.2 u t=_
  rw [hpoint]
  rfl

theorem residual_correspondence (A0 D : E →L[ℝ] E)
    (B : ℝ → ContinuousPath E → ContinuousPath E)
    (d : GenericShootingMap.FlowData E) (u : ContinuousPath E) :
    nonlinearPathResidual (affineLift A0 D B) (toNonlinear d,u)=
      pathResidual A0 D B (d,u) := rfl

/-- The actual nonlinear path IFT, transported through the explicit data
reassociation. Joint smoothness of the supplied path lift remains an input. -/
theorem smooth_full_interval_paths [CompleteSpace E] (A0 D : E →L[ℝ] E) (Q : ℝ → E → E)
    (B : ℝ → ContinuousPath E → ContinuousPath E)
    (hQ : ContDiff ℝ ⊤ (fun p : ℝ × E => Q p.1 p.2))
    (hB : ContDiff ℝ ⊤ (fun p : ℝ × ContinuousPath E => B p.1 p.2))
    (hpoint : ∀ r u t, B r u t=Q r (u t))
    (d : GenericShootingMap.FlowData E) (u : ContinuousPath E)
    (hu : pathResidual A0 D B (d,u)=0) :
    ∃ ψ : GenericShootingMap.FlowData E → ContinuousPath E,
      ContDiffAt ℝ ⊤ ψ d ∧ ψ d=u ∧
      ∀ᶠ z in 𝓝 d, pathResidual A0 D B (z,ψ z)=0 := by
  have hbase : nonlinearPathResidual (affineLift A0 D B) (toNonlinear d,u)=0 := by
    rw [residual_correspondence]
    exact hu
  obtain ⟨χ,hχ,hχ0,hres,_,_⟩ := smooth_nonlinear_full_interval_paths
    (affineField A0 D Q) (affineLift A0 D B)
    (affineField_smooth A0 D Q hQ) (affineLift_smooth A0 D B hB)
    (affineLift_apply A0 D Q B hpoint) (toNonlinear d) u hbase
  refine ⟨fun z => χ (toNonlinear z),
    hχ.comp d toNonlinear_smooth.contDiffAt,hχ0,?_⟩
  have ht := toNonlinear_smooth.continuous.continuousAt.tendsto.eventually hres
  filter_upwards [ht] with z hz
  simpa only [residual_correspondence] using hz

end
end ThreeSitePhosphorylation.GenericAffinePathExistence
