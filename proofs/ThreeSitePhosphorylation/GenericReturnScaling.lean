import proofs.ThreeSitePhosphorylation.GenericReturnIFT
import proofs.ThreeSitePhosphorylation.GenericAffinePathUniqueness
import proofs.ThreeSitePhosphorylation.GenericQuadraticTensor

namespace ThreeSitePhosphorylation.GenericReturnScaling
noncomputable section
open scoped Topology
open GenericReturnIFT

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pathQuadratic_scaling (H : ℝ → GenericQuadraticTensor.Tensor ι)
    (r s : ℝ) (u : ContinuousPath (ι → ℝ)) :
    GenericQuadraticTensor.pathField H r (s • u)=s^2 • GenericQuadraticTensor.pathField H r u := by
  apply ContinuousMap.ext
  intro t
  change GenericQuadraticTensor.pathField H r (s • u) t=
    s^2 • GenericQuadraticTensor.pathField H r u t
  rw [GenericQuadraticTensor.pathField_apply,GenericQuadraticTensor.pathField_apply]
  exact GenericQuadraticTensor.field_smul H r s (u t)

theorem pathResidual_scaling (A0 A1 : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (H : ℝ → GenericQuadraticTensor.Tensor ι) (a r T s : ℝ) (hs : s ≠ 0)
    (x : ι → ℝ) (u : ContinuousPath (ι → ℝ)) :
    GenericAffinePathResidual.pathResidual A0 A1 (GenericQuadraticTensor.pathField H)
      (((a/s,(r,T)),s • x),s • u)=
    s • GenericAffinePathResidual.pathResidual A0 A1 (GenericQuadraticTensor.pathField H)
      (((a,(r,T)),x),u) := by
  have hc : a/s*s^2=s*a := by field_simp
  simp only [GenericAffinePathResidual.pathResidual]
  rw [map_smul,map_smul,pathQuadratic_scaling,smul_smul,hc,mul_smul,← smul_add,map_smul,
    smul_comm T s]
  simp only [smul_sub]

def scaleFlowData (d : GenericShootingMap.FlowData (ι → ℝ)) (s : ℝ) :
    GenericShootingMap.FlowData (ι → ℝ) := ((d.1.1/s,d.1.2),s • d.2)

/-- Local scaling of the SAME selected solution follows from the literal
residual and the selected-solution uniqueness theorem. -/
theorem selected_solution_scaling (A0 A1 : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (H : ℝ → GenericQuadraticTensor.Tensor ι)
    (hH : ∀ i j k, ContDiff ℝ ⊤ (fun r => H r i j k))
    (r T : ℝ) (x : ι → ℝ) (u : ContinuousPath (ι → ℝ))
    (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (hψ : ContinuousAt ψ ((0,(r,T)),x)) (hψ0 : ψ ((0,(r,T)),x)=u)
    (hres : ∀ᶠ d in 𝓝 ((0,(r,T)),x),
      GenericAffinePathResidual.pathResidual A0 A1 (GenericQuadraticTensor.pathField H) (d,ψ d)=0) :
    ∀ᶠ z in 𝓝 ((((0,(r,T)),x),(1:ℝ))),
      ψ (scaleFlowData z.1 z.2)=z.2 • ψ z.1 := by
  have hu : GenericAffinePathResidual.pathResidual A0 A1 (GenericQuadraticTensor.pathField H)
      (((0,(r,T)),x),u)=0 := by rw [← hψ0]; exact hres.self_of_nhds
  have hpath := GenericAffinePathUniqueness.selected_solution_unique A0 A1
    (GenericQuadraticTensor.field H) (GenericQuadraticTensor.pathField H)
    (GenericQuadraticTensor.field_smooth H hH) (GenericQuadraticTensor.pathField_smooth H hH)
    (GenericQuadraticTensor.pathField_apply H) _ u hu ψ hψ hψ0 hres
  let z0 : GenericShootingMap.FlowData (ι → ℝ) × ℝ := (((0,(r,T)),x),1)
  have hscaled : ContinuousAt (fun z : GenericShootingMap.FlowData (ι → ℝ) × ℝ =>
      scaleFlowData z.1 z.2) z0 := by
    have ha : ContinuousAt (fun z : GenericShootingMap.FlowData (ι → ℝ) × ℝ =>
        z.1.1.1/z.2) z0 := continuousAt_fst.fst.fst.div continuousAt_snd (by norm_num [z0])
    exact (ha.prodMk continuousAt_fst.fst.snd).prodMk (continuousAt_snd.smul continuousAt_fst.snd)
  have hp : Filter.Tendsto (fun z : GenericShootingMap.FlowData (ι → ℝ) × ℝ =>
      (scaleFlowData z.1 z.2,z.2 • ψ z.1)) (𝓝 z0) (𝓝 (((0,(r,T)),x),u)) := by
    have hψz : ContinuousAt (fun z : GenericShootingMap.FlowData (ι → ℝ) × ℝ => ψ z.1) z0 :=
      (show ContinuousAt ψ z0.1 from hψ).comp
        (show ContinuousAt (fun z : GenericShootingMap.FlowData (ι → ℝ) × ℝ => z.1) z0 from
          continuousAt_fst)
    have hh := hscaled.prodMk (continuousAt_snd.smul hψz)
    simpa [scaleFlowData,z0,hψ0] using hh.tendsto
  have hr : ∀ᶠ z in 𝓝 z0,
      GenericAffinePathResidual.pathResidual A0 A1 (GenericQuadraticTensor.pathField H)
        (z.1,ψ z.1)=0 := by
    have hf : Filter.Tendsto (fun z : GenericShootingMap.FlowData (ι → ℝ) × ℝ => z.1) (𝓝 z0)
        (𝓝 ((0,(r,T)),x)) := continuousAt_fst.tendsto
    exact hf.eventually hres
  have hn : ∀ᶠ z in 𝓝 z0, z.2 ≠ 0 := continuousAt_snd.eventually_ne (by norm_num [z0])
  filter_upwards [hp.eventually hpath,hr,hn] with z hz hr hs
  apply hz.mp
  change GenericAffinePathResidual.pathResidual A0 A1 (GenericQuadraticTensor.pathField H)
    (((z.1.1.1/z.2,z.1.1.2),z.2 • z.1.2),z.2 • ψ z.1)=0
  rw [pathResidual_scaling A0 A1 H _ _ _ _ hs,hr,smul_zero]

def scaleReturnData (d : ReturnData (ι → ℝ)) (s : ℝ) : ReturnData (ι → ℝ) :=
  ((d.1.1/s,d.1.2),s • d.2)

/-- Actual local return scaling from the source residual identity and both
implicit-function uniqueness statements. No scaling of the return is assumed. -/
theorem actual_return_scaling
    (A0 A1 : (ι → ℝ) →L[ℝ] (ι → ℝ)) (K : ℝ → GenericQuadraticTensor.Tensor ι)
    (hK : ∀ i j k, ContDiff ℝ ⊤ (fun r => K r i j k)) (r T : ℝ) (x : (ι → ℝ)) (u : (ContinuousPath (ι → ℝ)))
    (p : (ι → ℂ) →ₗ[ℂ] ℂ) (ψ : GenericShootingMap.FlowData (ι → ℝ) → (ContinuousPath (ι → ℝ))) (τ : ReturnData (ι → ℝ) → ℝ)
    (hψ : ContinuousAt ψ ((0,(r,T)),x)) (hψ0 : ψ ((0,(r,T)),x)=u)
    (hτ : ContinuousAt τ ((0,r),x)) (hτ0 : τ ((0,r),x)=T)
    (hres : ∀ᶠ d in 𝓝 ((0,(r,T)),x), GenericAffinePathResidual.pathResidual A0 A1 (GenericQuadraticTensor.pathField K) (d,ψ d)=0)
    (hphase : ∀ᶠ d in 𝓝 ((0,r),x), endpointPhase ψ p (d,τ d)=0)
    (htime : ∀ᶠ d in 𝓝 (((0,r),x),T), endpointPhase ψ p d=0 ↔ τ d.1=d.2) :
    ∀ᶠ z in 𝓝 (((0,r),x),(1:ℝ)),
      τ (scaleReturnData z.1 z.2)=τ z.1 ∧
      returnPoint ψ τ (scaleReturnData z.1 z.2)=z.2 • returnPoint ψ τ z.1 := by
  have hu : GenericAffinePathResidual.pathResidual A0 A1 (GenericQuadraticTensor.pathField K)
      (((0,(r,T)),x),u)=0 := by rw [← hψ0]; exact hres.self_of_nhds
  have hpath := GenericAffinePathUniqueness.selected_solution_unique A0 A1
    (GenericQuadraticTensor.field K) (GenericQuadraticTensor.pathField K)
    (GenericQuadraticTensor.field_smooth K hK) (GenericQuadraticTensor.pathField_smooth K hK)
    (GenericQuadraticTensor.pathField_apply K) _ u hu ψ hψ hψ0 hres
  let d0 : ReturnData (ι → ℝ) := ((0,r),x)
  let z0 : ReturnData (ι → ℝ) × ℝ := (d0,1)
  let O : ReturnData (ι → ℝ) × ℝ → GenericShootingMap.FlowData (ι → ℝ) := fun z => returnArgument (z.1,τ z.1)
  let D : ReturnData (ι → ℝ) × ℝ → ReturnData (ι → ℝ) := fun z => scaleReturnData z.1 z.2
  let V : ReturnData (ι → ℝ) × ℝ → GenericShootingMap.FlowData (ι → ℝ) := fun z => returnArgument (D z,τ z.1)
  have hτc : ContinuousAt (fun z : ReturnData (ι → ℝ) × ℝ => τ z.1) z0 :=
    (show ContinuousAt τ z0.1 from hτ).comp
      (show ContinuousAt (fun z : ReturnData (ι → ℝ) × ℝ => z.1) z0 from continuousAt_fst)
  have hDc : ContinuousAt D z0 := by
    have ha : ContinuousAt (fun z : ReturnData (ι → ℝ) × ℝ => z.1.1.1/z.2) z0 :=
      continuousAt_fst.fst.fst.div continuousAt_snd (by norm_num [z0])
    exact (ha.prodMk continuousAt_fst.fst.snd).prodMk
      (continuousAt_snd.smul continuousAt_fst.snd)
  have hOc : ContinuousAt O z0 := returnArgument_smooth.continuous.continuousAt.comp
    (continuousAt_fst.prodMk hτc)
  have hVc : ContinuousAt V z0 := returnArgument_smooth.continuous.continuousAt.comp
    (hDc.prodMk hτc)
  have hO0 : O z0=((0,(r,T)),x) := by simp [O,z0,d0,hτ0,returnArgument]
  have hV0 : V z0=((0,(r,T)),x) := by simp [V,D,z0,d0,hτ0,returnArgument,scaleReturnData]
  have huc : ContinuousAt (fun z => ψ (O z)) z0 := by
    apply ContinuousAt.comp _ hOc
    rwa [hO0]
  have hpair : Filter.Tendsto (fun z : ReturnData (ι → ℝ) × ℝ => (V z,z.2 • ψ (O z)))
      (𝓝 z0) (𝓝 (((0,(r,T)),x),u)) := by
    have hh := hVc.prodMk (continuousAt_snd.smul huc)
    simpa [hV0,hO0,hψ0,z0] using hh.tendsto
  have hret : Filter.Tendsto (fun z : ReturnData (ι → ℝ) × ℝ => (D z,τ z.1))
      (𝓝 z0) (𝓝 (d0,T)) := by
    have hh := hDc.prodMk hτc
    simpa [D,z0,d0,hτ0,scaleReturnData] using hh.tendsto
  have horig : ∀ᶠ z in 𝓝 z0, GenericAffinePathResidual.pathResidual A0 A1 (GenericQuadraticTensor.pathField K) (O z,ψ (O z))=0 := by
    have ht := hOc.tendsto
    rw [hO0] at ht
    exact ht.eventually hres
  have hph : ∀ᶠ z in 𝓝 z0, endpointPhase ψ p (z.1,τ z.1)=0 := by
    have hf : Filter.Tendsto (fun z : ReturnData (ι → ℝ) × ℝ => z.1) (𝓝 z0) (𝓝 d0) :=
      continuousAt_fst.tendsto
    exact hf.eventually hphase
  have hne : ∀ᶠ z in 𝓝 z0, z.2 ≠ 0 :=
    continuousAt_snd.eventually_ne (by norm_num [z0])
  filter_upwards [hpair.eventually hpath,hret.eventually htime,horig,hph,hne]
    with z hp ht hr hf hn
  have hscaled : GenericAffinePathResidual.pathResidual A0 A1 (GenericQuadraticTensor.pathField K) (V z,z.2 • ψ (O z))=0 := by
    change GenericAffinePathResidual.pathResidual A0 A1 (GenericQuadraticTensor.pathField K) (((z.1.1.1/z.2,(z.1.1.2,τ z.1)),z.2 • z.1.2),z.2 • ψ (O z))=0
    rw [pathResidual_scaling A0 A1 K _ _ _ _ hn]
    change z.2 • GenericAffinePathResidual.pathResidual A0 A1 (GenericQuadraticTensor.pathField K) (O z,ψ (O z))=0
    rw [hr,smul_zero]
  have hsol : ψ (V z)=z.2 • ψ (O z) := hp.mp hscaled
  have hzero : endpointPhase ψ p (D z,τ z.1)=0 := by
    let H : (ι → ℝ) →L[ℝ] ℝ := Complex.imCLM.comp (GenericShootingInvertibility.sourceGauge p)
    change H (ψ (V z) ⟨1,by norm_num⟩)=0
    rw [hsol]
    change H (z.2 • (ψ (O z) ⟨1,by norm_num⟩))=0
    rw [map_smul]
    change z.2 • endpointPhase ψ p (z.1,τ z.1)=0
    rw [hf,smul_zero]
  have he := ht.mp hzero
  refine ⟨he,?_⟩
  unfold returnPoint
  change ψ (returnArgument (D z,τ (D z))) ⟨1,by norm_num⟩=
    z.2 • ψ (O z) ⟨1,by norm_num⟩
  rw [he]
  change ψ (V z) ⟨1,by norm_num⟩=z.2 • ψ (O z) ⟨1,by norm_num⟩
  rw [hsol]
  rfl

end
end ThreeSitePhosphorylation.GenericReturnScaling
