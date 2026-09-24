import proofs.ThreeSitePhosphorylation.AttractingFlow
import proofs.ThreeSitePhosphorylation.AttractingComplexOrbit

namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section
open scoped Topology

abbrev ShootingState := ReducedState × ℂ

def sourceGauge (p : (Fin 9 → ℂ) →ₗ[ℂ] ℂ) : ReducedState →L[ℝ] ℂ :=
  (p.toContinuousLinearMap.restrictScalars ℝ).comp complexify

def shootingArgument (p : ℝ × ShootingState) : FlowData :=
  ((p.1,(p.2.2.re,p.2.2.im)),p.2.1)

def shootingMap (ψ : FlowData → SourcePath) (L : ReducedState →L[ℝ] ℂ)
    (x : ReducedState) (p : ℝ × ShootingState) : ShootingState :=
  ((ψ (shootingArgument p)) ⟨1,by norm_num⟩-p.2.1,L (p.2.1-x))

theorem shootingArgument_smooth : ContDiff ℝ ⊤ shootingArgument := by
  unfold shootingArgument
  have hr : ContDiff ℝ ⊤ (fun p : ℝ × ShootingState => p.2.2.re) :=
    Complex.reCLM.contDiff.comp (f := fun p : ℝ × ShootingState => p.2.2) contDiff_snd.snd
  have hi : ContDiff ℝ ⊤ (fun p : ℝ × ShootingState => p.2.2.im) :=
    Complex.imCLM.contDiff.comp (f := fun p : ℝ × ShootingState => p.2.2) contDiff_snd.snd
  exact (contDiff_fst.prodMk (hr.prodMk hi)).prodMk contDiff_snd.fst

theorem shootingMap_smooth (ψ : FlowData → SourcePath) (L : ReducedState →L[ℝ] ℂ)
    (x : ReducedState) (p : ℝ × ShootingState)
    (hψ : ContDiffAt ℝ ⊤ ψ (shootingArgument p)) :
    ContDiffAt ℝ ⊤ (shootingMap ψ L x) p := by
  have he := (ContinuousMap.evalCLM (R := ℝ) (M := ReducedState) (⟨1,by norm_num⟩:UnitTime)).contDiff (n := ⊤)
  have hu := hψ.comp p shootingArgument_smooth.contDiffAt
  unfold shootingMap
  exact ((he.contDiffAt.comp p hu).sub contDiffAt_snd.fst).prodMk
    (L.contDiff.contDiffAt.comp p (contDiffAt_snd.fst.sub contDiffAt_const))

theorem shootingMap_zero (ψ : FlowData → SourcePath) (L : ReducedState →L[ℝ] ℂ)
    (x : ReducedState) (r T : ℝ)
    (hψ : ψ ((0,(r,T)),x) ⟨1,by norm_num⟩=x) :
    shootingMap ψ L x (0,(x,(r:ℂ)+Complex.I*(T:ℂ)))=0 := by
  have ha : shootingArgument (0,(x,(r:ℂ)+Complex.I*(T:ℂ)))=((0,(r,T)),x) := by
    simp [shootingArgument]
  unfold shootingMap
  rw [ha,hψ]
  simp

theorem shootingMap_direction (ψ : FlowData → SourcePath) (L : ReducedState →L[ℝ] ℂ)
    (x dx : ReducedState) (r T dr dT : ℝ) (q : SourcePath)
    (hψ : HasDerivAt (fun s : ℝ => ψ ((0,(r+s*dr,T+s*dT)),x+s • dx)) q 0) :
    HasDerivAt (fun s : ℝ => shootingMap ψ L x
      (0,(x+s • dx,((r+s*dr:ℝ):ℂ)+Complex.I*((T+s*dT:ℝ):ℂ))))
      (q ⟨1,by norm_num⟩-dx,L dx) 0 := by
  have hx : HasDerivAt (fun s : ℝ => x+s • dx) dx 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const dx).const_add x
  have he := (ContinuousMap.evalCLM (R := ℝ) (M := ReducedState)
    (⟨1,by norm_num⟩:UnitTime)).hasFDerivAt.comp_hasDerivAt 0 hψ
  have hg := L.hasFDerivAt.comp_hasDerivAt 0 (hx.sub_const x)
  simpa [shootingMap,shootingArgument,Function.comp_def] using (he.sub hx).prodMk hg

theorem flowLine_derivative (r T dr dT : ℝ) (x dx : ReducedState) :
    HasDerivAt (fun s : ℝ => ((0,(r+s*dr,T+s*dT)),x+s • dx) : ℝ → FlowData)
      ((0,(dr,dT)),dx) 0 := by
  have hr : HasDerivAt (fun s : ℝ => r+s*dr) dr 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const dr).const_add r
  have ht : HasDerivAt (fun s : ℝ => T+s*dT) dT 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const dT).const_add T
  have hx : HasDerivAt (fun s : ℝ => x+s • dx) dx 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const dx).const_add x
  exact ((hasDerivAt_const (x := (0:ℝ)) (c := (0:ℝ))).prodMk (hr.prodMk ht)).prodMk hx

theorem shootingLine_derivative (r T : ℝ) (x : ReducedState) (d : ShootingState) :
    HasDerivAt (fun s : ℝ => (0,(x+s • d.1,
      ((r+s*d.2.re:ℝ):ℂ)+Complex.I*((T+s*d.2.im:ℝ):ℂ))) : ℝ → ℝ × ShootingState)
      (0,d) 0 := by
  have hr : HasDerivAt (fun s : ℝ => r+s*d.2.re) d.2.re 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const d.2.re).const_add r
  have ht : HasDerivAt (fun s : ℝ => T+s*d.2.im) d.2.im 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const d.2.im).const_add T
  have hx : HasDerivAt (fun s : ℝ => x+s • d.1) d.1 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const d.1).const_add x
  have hc := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hr).add
    ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 ht).const_mul Complex.I)
  have hd : (d.2.re:ℂ)+Complex.I*(d.2.im:ℂ)=d.2 := by
    simpa only [mul_comm Complex.I] using Complex.re_add_im d.2
  have hc' : HasDerivAt (fun s : ℝ => ((r+s*d.2.re:ℝ):ℂ)+Complex.I*((T+s*d.2.im:ℝ):ℂ)) d.2 0 := by
    simpa only [Function.comp_apply,Complex.ofRealCLM_apply,hd] using hc
  exact (hasDerivAt_const (x := (0:ℝ)) (c := (0:ℝ))).prodMk (hx.prodMk hc')

end
end ThreeSitePhosphorylation.AttractingWitness
