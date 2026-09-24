import proofs.ThreeSitePhosphorylation.GenericAffinePathResidual
import proofs.ThreeSitePhosphorylation.GenericPathKernel

namespace ThreeSitePhosphorylation.GenericShootingInvertibility
noncomputable section
open scoped Topology
open GenericShootingMap GenericComplexification GenericLinearOrbit
open GenericPeriodicKernel GenericVariationalODE
set_option maxHeartbeats 500000

variable {ι σ : Type*} [Fintype ι] [DecidableEq σ]

def sourceGauge (p : (ι → ℂ) →ₗ[ℂ] ℂ) : (ι → ℝ) →L[ℝ] ℂ :=
  (p.toContinuousLinearMap.restrictScalars ℝ).comp GenericComplexification.complexify

theorem matrix_operator_affine (A D : Matrix ι ι ℝ) (r : ℝ) :
    (A+r • D).mulVecLin.toContinuousLinearMap=
      A.mulVecLin.toContinuousLinearMap+r • D.mulVecLin.toContinuousLinearMap := by
  ext x i
  simp

/-- Shooting invertibility follows from the actual affine path residual,
the critical eigenbasis, and crossing. No invertibility hypothesis is used. -/
theorem shooting_partial_invertible (A0 D : Matrix ι ι ℝ)
    (B : ℝ → ContinuousPath (ι → ℝ) → ContinuousPath (ι → ℝ))
    (r w : ℝ) (hw : 0<w) (roots : σ → ℝ) (hn : ∀ i, roots i<0)
    (basis : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ))
    (heigen : ∀ i, (GenericComplexification.complexMatrix (A0+r • D)).mulVec (basis i)=
      GenericPeriodicKernel.spectralValues roots w i • basis i)
    (hcross : (basis.coord (Sum.inr 0)
      ((GenericComplexification.complexMatrix D).mulVec (basis (Sum.inr 0)))).re<0)
    (ψ : GenericShootingMap.FlowData (ι → ℝ) → GenericShootingMap.SourcePath (ι → ℝ))
    (hψ : ContDiffAt ℝ ⊤ ψ ((0,(r,2*Real.pi/w)),GenericComplexification.realPart (basis (Sum.inr 0))))
    (hb : ψ ((0,(r,2*Real.pi/w)),GenericComplexification.realPart (basis (Sum.inr 0)))=
      GenericLinearOrbit.referencePath (GenericComplexification.realPart (basis (Sum.inr 0))) (GenericComplexification.imagPart (basis (Sum.inr 0))) w (2*Real.pi/w))
    (he : ∀ᶠ p in 𝓝 ((0,(r,2*Real.pi/w)),GenericComplexification.realPart (basis (Sum.inr 0))),
      GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
        D.mulVecLin.toContinuousLinearMap B (p,ψ p)=0) :
    (fderiv ℝ (GenericShootingMap.shootingMap ψ (sourceGauge (basis.coord (Sum.inr 0)))
        (GenericComplexification.realPart (basis (Sum.inr 0))))
      (0,(GenericComplexification.realPart (basis (Sum.inr 0)),(r:ℂ)+Complex.I*((2*Real.pi/w:ℝ):ℂ))) ∘L
        ContinuousLinearMap.inr ℝ ℝ (GenericShootingMap.ShootingState (ι → ℝ))).IsInvertible := by
  let x := GenericComplexification.realPart (basis (Sum.inr (0:Fin 2)))
  let T := 2*Real.pi/w
  let s0 : GenericShootingMap.ShootingState (ι → ℝ) := (x,(r:ℂ)+Complex.I*(T:ℂ))
  let F := GenericShootingMap.shootingMap ψ (sourceGauge (basis.coord (Sum.inr 0))) x
  let J := fderiv ℝ F (0,s0) ∘L ContinuousLinearMap.inr ℝ ℝ (GenericShootingMap.ShootingState (ι → ℝ))
  have hs : ContDiffAt ℝ ⊤ F (0,s0) :=
    GenericShootingMap.shootingMap_smooth ψ (sourceGauge (basis.coord (Sum.inr 0))) x (0,s0)
      (by simpa [GenericShootingMap.shootingArgument,s0] using hψ)
  have hker (d : GenericShootingMap.ShootingState (ι → ℝ)) (hjd : J d=0) : d=0 := by
    let q := fderiv ℝ ψ ((0,(r,T)),x) ((0,(d.2.re,d.2.im)),d.1)
    have hline := GenericShootingMap.flowLine_derivative r T d.2.re d.2.im x d.1
    have hqd : HasDerivAt (fun s : ℝ => ψ ((0,(r+s*d.2.re,T+s*d.2.im)),x+s • d.1)) q 0 := by
      exact hψ.differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp [x,T])
    have hev : ∀ᶠ s in 𝓝 (0:ℝ),
        GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
          D.mulVecLin.toContinuousLinearMap B
          (((0,(r+s*d.2.re,T+s*d.2.im)),x+s • d.1),
            ψ ((0,(r+s*d.2.re,T+s*d.2.im)),x+s • d.1))=0 := by
      have hh := hline.continuousAt.tendsto
      simp only [zero_mul,add_zero,zero_smul] at hh
      exact hh.eventually he
    have hq := GenericAffinePathResidual.variational_path_equation
      A0.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap B
      r T d.2.re d.2.im x d.1 _ q hqd hev
    simp only [zero_mul,add_zero,zero_smul] at hq
    have hb' : ψ ((0,(r,T)),x)=GenericLinearOrbit.referencePath x (GenericComplexification.imagPart (basis (Sum.inr 0))) w T := hb
    rw [hb',← matrix_operator_affine] at hq
    have hsd := GenericShootingMap.shootingMap_direction ψ (sourceGauge (basis.coord (Sum.inr 0)))
      x d.1 r T d.2.re d.2.im q hqd
    have hfd := hs.differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt_of_eq 0
      (GenericShootingMap.shootingLine_derivative r T x d) (by simp [s0])
    have hunique := hsd.unique hfd
    change (q ⟨1,by norm_num⟩-d.1,sourceGauge (basis.coord (Sum.inr 0)) d.1)=J d at hunique
    rw [hjd] at hunique
    have h1 : q ⟨1,by norm_num⟩=d.1 := sub_eq_zero.mp (congrArg Prod.fst hunique)
    have hnorm : basis.coord (Sum.inr 0) (GenericComplexification.complexify d.1)=0 := congrArg Prod.snd hunique
    have h0 : q ⟨0,by norm_num⟩=d.1 :=
      (GenericVariationalODE.integralVariation_eq d.1 _ q hq ⟨0,by norm_num⟩).symm.trans
        (GenericVariationalODE.integralVariation_initial d.1 _)
    obtain ⟨hdr,hdt,hdx⟩ := GenericPathKernel.periodic_path_kernel (A0+r • D) D w hw
      roots hn basis heigen hcross d.2.re d.2.im d.1 q hq (h1.trans h0.symm) hnorm
    exact Prod.ext hdx (Complex.ext hdr hdt)
  have hinj : Function.Injective J := by
    intro d e h
    exact sub_eq_zero.mp (hker (d-e) (by rw [map_sub,h,sub_self]))
  have hsurj : Function.Surjective J :=
    (LinearMap.injective_iff_surjective (f := J.toLinearMap)).mp hinj
  obtain ⟨v,hv⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj,hsurj⟩
  exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ (GenericShootingMap.ShootingState (ι → ℝ)) v,hv⟩

end
end ThreeSitePhosphorylation.GenericShootingInvertibility
