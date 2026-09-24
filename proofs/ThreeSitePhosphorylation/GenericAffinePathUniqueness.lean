import proofs.ThreeSitePhosphorylation.GenericAffinePathExistence

/-! Local uniqueness for the same affine-residual path solution already
chosen by a shooting construction. No equality of independent choices is
assumed; an arbitrary existing solution map is identified locally. -/
namespace ThreeSitePhosphorylation.GenericAffinePathUniqueness
noncomputable section
open Filter
open scoped Topology
open GenericAffinePathResidual GenericAffinePathExistence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Preserve both existence and uniqueness when reassociating the nonlinear
path IFT data into the existing affine shooting interface. -/
theorem smooth_full_interval_paths_unique (A0 D : E →L[ℝ] E) (Q : ℝ → E → E)
    (B : ℝ → ContinuousPath E → ContinuousPath E)
    (hQ : ContDiff ℝ ⊤ (fun p : ℝ × E => Q p.1 p.2))
    (hB : ContDiff ℝ ⊤ (fun p : ℝ × ContinuousPath E => B p.1 p.2))
    (hpoint : ∀ r u t, B r u t=Q r (u t))
    (d : GenericShootingMap.FlowData E) (u : ContinuousPath E)
    (hu : pathResidual A0 D B (d,u)=0) :
    ∃ ψ : GenericShootingMap.FlowData E → ContinuousPath E,
      ContDiffAt ℝ ⊤ ψ d ∧ ψ d=u ∧
      (∀ᶠ z in 𝓝 d, pathResidual A0 D B (z,ψ z)=0) ∧
      (∀ᶠ z in 𝓝 (d,u), pathResidual A0 D B z=0 ↔ ψ z.1=z.2) := by
  have hbase : nonlinearPathResidual (affineLift A0 D B) (toNonlinear d,u)=0 := by
    rw [residual_correspondence]
    exact hu
  obtain ⟨χ,hχ,hχ0,hres,hunique,_⟩ := smooth_nonlinear_full_interval_paths
    (affineField A0 D Q) (affineLift A0 D B)
    (affineField_smooth A0 D Q hQ) (affineLift_smooth A0 D B hB)
    (affineLift_apply A0 D Q B hpoint) (toNonlinear d) u hbase
  refine ⟨fun z => χ (toNonlinear z),
    hχ.comp d toNonlinear_smooth.contDiffAt,hχ0,?_,?_⟩
  · have ht := toNonlinear_smooth.continuous.continuousAt.tendsto.eventually hres
    filter_upwards [ht] with z hz
    simpa only [residual_correspondence] using hz
  · have hpair : ContinuousAt
        (fun z : GenericShootingMap.FlowData E × ContinuousPath E => (toNonlinear z.1,z.2))
        (d,u) :=
      (toNonlinear_smooth.continuous.continuousAt.comp continuousAt_fst).prodMk continuousAt_snd
    filter_upwards [hpair.tendsto.eventually hunique] with z hz
    simpa only [residual_correspondence] using hz

/-- Upgrade ANY previously chosen continuous residual solution map. This
applies directly to a witness returned by GenericAffinePathExistence and
keeps the exact map used by its shooting/closed-path construction. -/
theorem selected_solution_unique (A0 D : E →L[ℝ] E) (Q : ℝ → E → E)
    (B : ℝ → ContinuousPath E → ContinuousPath E)
    (hQ : ContDiff ℝ ⊤ (fun p : ℝ × E => Q p.1 p.2))
    (hB : ContDiff ℝ ⊤ (fun p : ℝ × ContinuousPath E => B p.1 p.2))
    (hpoint : ∀ r u t, B r u t=Q r (u t))
    (d : GenericShootingMap.FlowData E) (u : ContinuousPath E)
    (hu : pathResidual A0 D B (d,u)=0)
    (ψ : GenericShootingMap.FlowData E → ContinuousPath E)
    (hψ : ContinuousAt ψ d) (hψ0 : ψ d=u)
    (hres : ∀ᶠ z in 𝓝 d, pathResidual A0 D B (z,ψ z)=0) :
    ∀ᶠ z in 𝓝 (d,u), pathResidual A0 D B z=0 ↔ ψ z.1=z.2 := by
  obtain ⟨χ,_,_,_,hunique⟩ :=
    smooth_full_interval_paths_unique A0 D Q B hQ hB hpoint d u hu
  have hp : Tendsto (fun z => (z,ψ z)) (𝓝 d) (𝓝 (d,u)) := by
    simpa only [hψ0] using (continuousAt_id.prodMk hψ).tendsto
  have heq : ∀ᶠ z in 𝓝 d, χ z=ψ z := by
    filter_upwards [hp.eventually hunique,hres] with z hz hzr
    exact hz.mp hzr
  have hf : Tendsto (fun z : GenericShootingMap.FlowData E × ContinuousPath E => z.1)
      (𝓝 (d,u)) (𝓝 d) := continuousAt_fst.tendsto
  filter_upwards [hunique,hf.eventually heq] with z hz he
  simpa only [he] using hz

omit [CompleteSpace E] in
/-- A nearby parameterized residual curve is the SAME selected solution
map applied to its data. This is the exact comparison needed for closed
families and for scaled return paths. -/
theorem solution_curve_identity {α : Type*} (l : Filter α)
    (A0 D : E →L[ℝ] E) (B : ℝ → ContinuousPath E → ContinuousPath E)
    (d : GenericShootingMap.FlowData E) (u : ContinuousPath E)
    (ψ : GenericShootingMap.FlowData E → ContinuousPath E)
    (hunique : ∀ᶠ z in 𝓝 (d,u), pathResidual A0 D B z=0 ↔ ψ z.1=z.2)
    (data : α → GenericShootingMap.FlowData E) (paths : α → ContinuousPath E)
    (hdata : Tendsto data l (𝓝 d)) (hpaths : Tendsto paths l (𝓝 u))
    (hres : ∀ᶠ a in l, pathResidual A0 D B (data a,paths a)=0) :
    ∀ᶠ a in l, ψ (data a)=paths a := by
  filter_upwards [(hdata.prodMk_nhds hpaths).eventually hunique,hres] with a ha hr
  exact ha.mp hr

end
end ThreeSitePhosphorylation.GenericAffinePathUniqueness
