import proofs.ThreeSitePhosphorylation.AttractingShootingMap
import proofs.ThreeSitePhosphorylation.AttractingPathKernel

namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section
open scoped Topology
set_option maxHeartbeats 200000

theorem shooting_partial_invertible (r w : ℝ) (hw : 0<w)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0)
    (roots : Fin 7 → ℝ) (hn : ∀ i, roots i < 0)
    (basis : Module.Basis SpectralIndex ℂ (Fin 9 → ℂ))
    (hbasis : ∀ i, basis i=adjugateVector (spectralValues roots w i))
    (heigen : ∀ i, (complexSource r).mulVec (basis i)=spectralValues roots w i • basis i)
    (ψ : FlowData → SourcePath)
    (hψ : ContDiffAt ℝ ⊤ ψ ((0,(r,2*Real.pi/w)),realPart (adjugateVector (Complex.I*(w:ℂ)))))
    (hb : ψ ((0,(r,2*Real.pi/w)),realPart (adjugateVector (Complex.I*(w:ℂ))))=
      referencePath (realPart (adjugateVector (Complex.I*(w:ℂ))))
        (imagPart (adjugateVector (Complex.I*(w:ℂ)))) w (2*Real.pi/w))
    (he : ∀ᶠ p in 𝓝 ((0,(r,2*Real.pi/w)),realPart (adjugateVector (Complex.I*(w:ℂ)))),
      pathResidual (p,ψ p)=0) :
    (fderiv ℝ (shootingMap ψ (sourceGauge (basis.coord (Sum.inr 0))) (realPart (adjugateVector (Complex.I*(w:ℂ)))))
      (0,(realPart (adjugateVector (Complex.I*(w:ℂ))),(r:ℂ)+Complex.I*((2*Real.pi/w:ℝ):ℂ))) ∘L
        ContinuousLinearMap.inr ℝ ℝ ShootingState).IsInvertible := by
  let x := realPart (adjugateVector (Complex.I*(w:ℂ)))
  let T := 2*Real.pi/w
  let s0 : ShootingState := (x,(r:ℂ)+Complex.I*(T:ℂ))
  let F := shootingMap ψ (sourceGauge (basis.coord (Sum.inr 0))) x
  let A := fderiv ℝ F (0,s0) ∘L ContinuousLinearMap.inr ℝ ℝ ShootingState
  have hs : ContDiffAt ℝ ⊤ F (0,s0) :=
    shootingMap_smooth ψ (sourceGauge (basis.coord (Sum.inr 0))) x (0,s0) (by simpa [shootingArgument,s0] using hψ)
  have hker (d : ShootingState) (had : A d=0) : d=0 := by
    let q := fderiv ℝ ψ ((0,(r,T)),x) ((0,(d.2.re,d.2.im)),d.1)
    have hline := flowLine_derivative r T d.2.re d.2.im x d.1
    have hqd : HasDerivAt (fun s : ℝ => ψ ((0,(r+s*d.2.re,T+s*d.2.im)),x+s • d.1)) q 0 := by
      exact hψ.differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp [x,T])
    have hev : ∀ᶠ s in 𝓝 (0:ℝ),
        pathResidual (((0,(r+s*d.2.re,T+s*d.2.im)),x+s • d.1),
          ψ ((0,(r+s*d.2.re,T+s*d.2.im)),x+s • d.1))=0 := by
      have hh := hline.continuousAt.tendsto
      simp only [zero_mul,add_zero,zero_smul] at hh
      exact hh.eventually he
    have hq := variational_path_equation r T d.2.re d.2.im x d.1 _ q hqd hev
    simp only [zero_mul,add_zero,zero_smul] at hq
    have hb' : ψ ((0,(r,T)),x)=
        referencePath x (imagPart (adjugateVector (Complex.I*(w:ℂ)))) w T := hb
    rw [hb'] at hq
    have hsd := shootingMap_direction ψ (sourceGauge (basis.coord (Sum.inr 0))) x d.1 r T d.2.re d.2.im q hqd
    have hfd := hs.differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt_of_eq 0
      (shootingLine_derivative r T x d) (by simp [s0])
    have hunique := hsd.unique hfd
    change (q ⟨1,by norm_num⟩-d.1,sourceGauge (basis.coord (Sum.inr 0)) d.1)=A d at hunique
    rw [had] at hunique
    have h1 : q ⟨1,by norm_num⟩=d.1 := sub_eq_zero.mp (congrArg Prod.fst hunique)
    have hnorm : basis.coord (Sum.inr 0) (complexify d.1)=0 := congrArg Prod.snd hunique
    have h0 : q ⟨0,by norm_num⟩=d.1 := by
      exact (integralVariation_eq d.1 _ q hq ⟨0,by norm_num⟩).symm.trans
        (integralVariation_initial d.1 _)
    obtain ⟨hdr,hdt,hdx⟩ := periodic_path_kernel r w hw hp roots hn basis hbasis heigen d.2.re d.2.im d.1 q hq
      (h1.trans h0.symm) hnorm
    apply Prod.ext hdx
    exact Complex.ext hdr hdt
  have hinj : Function.Injective A := by
    intro d e h
    exact sub_eq_zero.mp (hker (d-e) (by rw [map_sub,h,sub_self]))
  have hsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp hinj
  obtain ⟨v,hv⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj,hsurj⟩
  exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ ShootingState v,hv⟩

end

noncomputable section
open scoped Topology

structure ClosedPathFamily (r w : ℝ) where
  left : (Fin 9 → ℂ) →ₗ[ℂ] ℂ
  left_eigen : ∀ v, left ((complexSource r).mulVec v)=(Complex.I*(w:ℂ))*left v
  left_normalized : left (adjugateVector (Complex.I*(w:ℂ)))=1
  parameters : ℝ → ShootingState
  paths : ℝ → SourcePath
  parameters_smooth : ContDiffAt ℝ ⊤ parameters 0
  paths_smooth : ContDiffAt ℝ ⊤ paths 0
  parameters_zero : parameters 0=
    (realPart (adjugateVector (Complex.I*(w:ℂ))),(r:ℂ)+Complex.I*((2*Real.pi/w:ℝ):ℂ))
  paths_zero : paths 0=referencePath (realPart (adjugateVector (Complex.I*(w:ℂ))))
    (imagPart (adjugateVector (Complex.I*(w:ℂ)))) w (2*Real.pi/w)
  residual : ∀ᶠ a in 𝓝 (0:ℝ), pathResidual (shootingArgument (a,parameters a),paths a)=0
  closed : ∀ᶠ a in 𝓝 (0:ℝ), paths a ⟨1,by norm_num⟩=(parameters a).1
  normalized : ∀ᶠ a in 𝓝 (0:ℝ),
    sourceGauge left ((parameters a).1-realPart (adjugateVector (Complex.I*(w:ℂ))))=0

theorem closed_path_family_exists (r w : ℝ) (hw : 0<w)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0)
    (roots : Fin 7 → ℝ) (hn : ∀ i, roots i < 0)
    (basis : Module.Basis SpectralIndex ℂ (Fin 9 → ℂ))
    (hbasis : ∀ i, basis i=adjugateVector (spectralValues roots w i))
    (heigen : ∀ i, (complexSource r).mulVec (basis i)=spectralValues roots w i • basis i)
    : Nonempty (ClosedPathFamily r w) := by
  let v := adjugateVector (Complex.I*(w:ℂ))
  let x := realPart v
  let T := 2*Real.pi/w
  let s0 : ShootingState := (x,(r:ℂ)+Complex.I*(T:ℂ))
  let u0 := referencePath x (imagPart v) w T
  have hev := (source_root_eigenvector r (Complex.I*(w:ℂ)) hp).2
  obtain ⟨ψ,hψ,hψ0,hres⟩ := smooth_full_interval_paths r T x u0
    (source_reference_solution r w T v hev)
  have hi := shooting_partial_invertible r w hw hp roots hn basis hbasis heigen ψ hψ hψ0 hres
  have hs := shootingMap_smooth ψ (sourceGauge (basis.coord (Sum.inr 0))) x (0,s0)
    (by simpa [shootingArgument,s0] using hψ)
  have hzero : shootingMap ψ (sourceGauge (basis.coord (Sum.inr 0))) x (0,s0)=0 := by
    apply shootingMap_zero
    rw [hψ0]
    exact (referencePath_endpoints x (imagPart v) w (ne_of_gt hw)).2
  let b := hs.implicitFunction (by simp) hi
  have hb : ContDiffAt ℝ ⊤ b 0 := hs.contDiffAt_implicitFunction (by simp) hi
  have hb0 : b 0=s0 := hs.implicitFunction_apply_self (by simp) hi
  have hclosed : ∀ᶠ a in 𝓝 (0:ℝ), shootingMap ψ (sourceGauge (basis.coord (Sum.inr 0))) x (a,b a)=0 := by
    simpa only [hzero] using hs.eventually_apply_implicitFunction (by simp) hi
  have harg : ContDiffAt ℝ ⊤ (fun a => shootingArgument (a,b a)) 0 :=
    shootingArgument_smooth.contDiffAt.comp 0 (contDiffAt_id.prodMk hb)
  have harg0 : shootingArgument (0,b 0)=((0,(r,T)),x) := by
    rw [hb0]
    simp [shootingArgument,s0]
  have hpath : ContDiffAt ℝ ⊤ (fun a => ψ (shootingArgument (a,b a))) 0 := by
    apply ContDiffAt.comp 0 _ harg
    rwa [harg0]
  refine ⟨{
    left := basis.coord (Sum.inr 0)
    left_eigen := (source_left_eigenfunctional r w roots basis heigen).2
    left_normalized := by
      have h := (source_left_eigenfunctional r w roots basis heigen).1
      rw [hbasis] at h
      simpa [spectralValues] using h
    parameters := b
    paths := fun a => ψ (shootingArgument (a,b a))
    parameters_smooth := hb
    paths_smooth := hpath
    parameters_zero := hb0
    paths_zero := by rw [harg0,hψ0]
    residual := ?_
    closed := ?_
    normalized := ?_ }⟩
  · have ht := harg.continuousAt.tendsto
    rw [harg0] at ht
    exact ht.eventually hres
  · filter_upwards [hclosed] with a ha
    exact sub_eq_zero.mp (congrArg Prod.fst ha)
  · filter_upwards [hclosed] with a ha
    exact congrArg Prod.snd ha

end

end ThreeSitePhosphorylation.AttractingWitness
