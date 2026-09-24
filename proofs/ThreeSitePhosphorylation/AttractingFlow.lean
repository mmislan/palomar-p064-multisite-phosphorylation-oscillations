import proofs.ThreeSitePhosphorylation.AttractingSource
import proofs.ThreeSitePhosphorylation.Volterra

/-! Smooth path-space solutions for the distinct P064 witness A.
No periodicity or orbital attraction is asserted in this module. -/

namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section
set_option maxHeartbeats 300000

theorem linearPart_affine (r : ℝ) :
    linearPart r = linearPart 0 + r • (linearPart 1-linearPart 0) := by
  ext y i
  fin_cases i <;>
    simp [linearPart,linearRows,complexRow,binding,exitRate,
      state,inputSpecies,enzymeSpecies,boundCoordinate,coordinate,speciesVariation]
  ring

theorem linearPart_smooth : ContDiff ℝ ⊤ linearPart := by
  have he : linearPart = (fun r => linearPart 0+r •
      (linearPart 1-linearPart 0)) := funext linearPart_affine
  rw [he]
  fun_prop

theorem quadraticPart_smooth :
    ContDiff ℝ ⊤ (fun p : ℝ × ReducedState => quadraticPart p.1 p.2) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;>
    simp [quadraticPart,quadraticRow,binding] <;> fun_prop

theorem quadraticPart_homogeneous (r a : ℝ) (y : ReducedState) :
    quadraticPart r (a • y) = (a*a) • quadraticPart r y := by
  ext i
  fin_cases i <;> simp [quadraticPart,quadraticRow] <;> ring

/-- Smooth amplitude-rescaled source, including the zero-amplitude limit. -/
def rescaledField (a r : ℝ) (y : ReducedState) : ReducedState :=
  linearPart r y + a • quadraticPart r y

theorem rescaledField_smooth :
    ContDiff ℝ ⊤ (fun p : (ℝ × ℝ) × ReducedState => rescaledField p.1.1 p.1.2 p.2) := by
  have hj : ContDiff ℝ ⊤ (fun p : (ℝ × ℝ) × ReducedState => linearPart p.1.2) :=
    linearPart_smooth.comp (f := fun p : (ℝ × ℝ) × ReducedState => p.1.2)
      contDiff_fst.snd
  have hq : ContDiff ℝ ⊤ (fun p : (ℝ × ℝ) × ReducedState => quadraticPart p.1.2 p.2) :=
    quadraticPart_smooth.comp (f := fun p : (ℝ × ℝ) × ReducedState => (p.1.2,p.2))
      (contDiff_fst.snd.prodMk contDiff_snd)
  unfold rescaledField
  apply ContDiff.add
  · exact hj.clm_apply contDiff_snd
  · exact contDiff_fst.fst.smul hq

theorem rescaledField_source (a r : ℝ) (y : ReducedState) :
    a • rescaledField a r y = reduced r (a • y) := by
  rw [taylor_exact,quadraticPart_homogeneous]
  simp [rescaledField,smul_add,smul_smul]

theorem rescaledField_zero (r : ℝ) (y : ReducedState) :
    rescaledField 0 r y = linearPart r y := by simp [rescaledField]

theorem rescaledField_zero_derivative (r : ℝ) (y : ReducedState) :
    HasFDerivAt (rescaledField 0 r) (linearPart r) y := by
  have he : rescaledField 0 r = linearPart r := funext (rescaledField_zero r)
  rw [he]
  exact (linearPart r).hasFDerivAt

end
end ThreeSitePhosphorylation.AttractingWitness

namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section
set_option maxHeartbeats 300000

abbrev SourcePath := ContinuousPath ReducedState
abbrev RealPath := ContinuousPath ℝ

def assemblePathLinear : (Fin 9 → RealPath) →ₗ[ℝ] SourcePath where
  toFun u := ⟨fun t i => u i t,continuous_pi (fun i => (u i).continuous)⟩
  map_add' _ _ := by ext t i; rfl
  map_smul' _ _ := by ext t i; rfl

def assemblePath : (Fin 9 → RealPath) →L[ℝ] SourcePath :=
  assemblePathLinear.mkContinuous 1 (by
    intro u
    simp only [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
    intro t
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
    intro i
    exact (ContinuousMap.norm_coe_le_norm (u i) t).trans (norm_le_pi_norm u i))

@[simp] theorem assemblePath_apply (u : Fin 9 → RealPath) (t : UnitTime) (i : Fin 9) :
    assemblePath u t i = u i t := rfl

def pathSpecies (j : Fin 12) : SourcePath →L[ℝ] RealPath :=
  (speciesVariation j).compLeftContinuous ℝ UnitTime

@[simp] theorem pathSpecies_apply (j : Fin 12) (u : SourcePath) (t : UnitTime) :
    pathSpecies j u t = speciesVariation j (u t) := rfl

def pathLinear (r : ℝ) : SourcePath →L[ℝ] SourcePath :=
  (linearPart 0).compLeftContinuous ℝ UnitTime + r •
    ((linearPart 1).compLeftContinuous ℝ UnitTime-
      (linearPart 0).compLeftContinuous ℝ UnitTime)

theorem pathLinear_apply (r : ℝ) (u : SourcePath) (t : UnitTime) :
    pathLinear r u t = linearPart r (u t) := by
  rw [linearPart_affine]
  rfl

theorem pathLinear_smooth : ContDiff ℝ ⊤ (fun p : ℝ × SourcePath => pathLinear p.1 p.2) := by
  unfold pathLinear
  fun_prop

def pathComplexQuadratic (r : ℝ) (j : Fin 6) (u : SourcePath) : RealPath :=
  binding r j • (pathSpecies (inputSpecies j) u * pathSpecies (enzymeSpecies j) u)

def pathQuadratic (r : ℝ) (u : SourcePath) : SourcePath :=
  assemblePath ![0,0,0,pathComplexQuadratic r 0 u,pathComplexQuadratic r 1 u,
    pathComplexQuadratic r 2 u,pathComplexQuadratic r 3 u,pathComplexQuadratic r 4 u,
    pathComplexQuadratic r 5 u]

theorem pathQuadratic_apply (r : ℝ) (u : SourcePath) (t : UnitTime) :
    pathQuadratic r u t = quadraticPart r (u t) := by
  ext i
  fin_cases i <;> simp [pathQuadratic,pathComplexQuadratic,quadraticPart,
    quadraticRow,mul_assoc]

theorem pathQuadratic_smooth :
    ContDiff ℝ ⊤ (fun p : ℝ × SourcePath => pathQuadratic p.1 p.2) := by
  unfold pathQuadratic
  apply assemblePath.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [pathComplexQuadratic,binding] <;> fun_prop

def pathField (p : ℝ × (ℝ × ℝ)) (u : SourcePath) : SourcePath :=
  p.2.2 • (pathLinear p.2.1 u+p.1 • pathQuadratic p.2.1 u)

theorem pathField_apply (a r T : ℝ) (u : SourcePath) (t : UnitTime) :
    pathField (a,(r,T)) u t = T • rescaledField a r (u t) := by
  simp [pathField,pathLinear_apply,pathQuadratic_apply,rescaledField]

theorem pathField_smooth :
    ContDiff ℝ ⊤ (fun p : (ℝ × (ℝ × ℝ)) × SourcePath => pathField p.1 p.2) := by
  have hl : ContDiff ℝ ⊤ (fun p : (ℝ × (ℝ × ℝ)) × SourcePath => pathLinear p.1.2.1 p.2) :=
    pathLinear_smooth.comp (f := fun p : (ℝ × (ℝ × ℝ)) × SourcePath => (p.1.2.1,p.2))
      (contDiff_fst.snd.fst.prodMk contDiff_snd)
  have hq : ContDiff ℝ ⊤ (fun p : (ℝ × (ℝ × ℝ)) × SourcePath => pathQuadratic p.1.2.1 p.2) :=
    pathQuadratic_smooth.comp (f := fun p : (ℝ × (ℝ × ℝ)) × SourcePath => (p.1.2.1,p.2))
      (contDiff_fst.snd.fst.prodMk contDiff_snd)
  unfold pathField
  have ht : ContDiff ℝ ⊤ (fun p : (ℝ × (ℝ × ℝ)) × SourcePath => p.1.2.2) := by fun_prop
  have ha : ContDiff ℝ ⊤ (fun p : (ℝ × (ℝ × ℝ)) × SourcePath => p.1.1) := by fun_prop
  exact ht.smul (hl.add (ha.smul hq))

theorem linearPicard_pathLinear (r T : ℝ) (u : SourcePath) :
    linearPicard (ContinuousLinearMap.id ℝ ReducedState) (T • pathLinear r u) =
      linearPicard (T • linearPart r) u := by
  ext t i
  change (∫ s in (0:ℝ)..(t:ℝ), pathExtension (T • pathLinear r u) s) i =
    (∫ s in (0:ℝ)..(t:ℝ), (T • linearPart r) (pathExtension u s)) i
  apply congrArg (fun v : ReducedState => v i)
  apply intervalIntegral.integral_congr
  intro s _
  simp [pathExtension,pathLinear_apply]

end
end ThreeSitePhosphorylation.AttractingWitness

namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section
open scoped Topology
set_option maxHeartbeats 200000

abbrev FlowData := (ℝ × (ℝ × ℝ)) × ReducedState

def constantPath : ReducedState →L[ℝ] SourcePath := ContinuousLinearMap.const ℝ UnitTime

def pathResidual (p : FlowData × SourcePath) : SourcePath :=
  p.2-constantPath p.1.2-
    linearPicard (ContinuousLinearMap.id ℝ ReducedState) (pathField p.1.1 p.2)

theorem pathResidual_smooth : ContDiff ℝ ⊤ pathResidual := by
  have hf : ContDiff ℝ ⊤ (fun p : FlowData × SourcePath => pathField p.1.1 p.2) :=
    pathField_smooth.comp (f := fun p : FlowData × SourcePath => (p.1.1,p.2))
      (contDiff_fst.fst.prodMk contDiff_snd)
  unfold pathResidual
  exact (contDiff_snd.sub (constantPath.contDiff.comp
    (f := fun p : FlowData × SourcePath => p.1.2) contDiff_fst.snd)).sub
    ((linearPicard (ContinuousLinearMap.id ℝ ReducedState)).contDiff.comp
      (f := fun p : FlowData × SourcePath => pathField p.1.1 p.2) hf)

theorem pathResidual_zero_amplitude (r T : ℝ) (x : ReducedState) (u : SourcePath) :
    pathResidual (((0,(r,T)),x),u) =
      (1-linearPicard (T • linearPart r)) u-constantPath x := by
  simp only [pathResidual,pathField,zero_smul,add_zero,linearPicard_pathLinear]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply]
  abel

theorem pathResidual_path_derivative (r T : ℝ) (x : ReducedState) (u : SourcePath) :
    fderiv ℝ pathResidual (((0,(r,T)),x),u) ∘L
      ContinuousLinearMap.inr ℝ FlowData SourcePath =
        1-linearPicard (T • linearPart r) := by
  have hi : HasFDerivAt (fun v : SourcePath => (((0,(r,T)),x),v))
      (ContinuousLinearMap.inr ℝ FlowData SourcePath) u := by
    convert (hasFDerivAt_const (𝕜 := ℝ) (((0,(r,T)),x) : FlowData) u).prodMk
      (hasFDerivAt_id u) using 1
  have hc := (pathResidual_smooth.differentiable (by simp)
    (((0,(r,T)),x),u)).hasFDerivAt.comp u hi
  have he : (fun v : SourcePath => pathResidual (((0,(r,T)),x),v)) =
      (fun v => (1-linearPicard (T • linearPart r)) v-constantPath x) :=
    funext (pathResidual_zero_amplitude r T x)
  have hd : HasFDerivAt (fun v : SourcePath => pathResidual (((0,(r,T)),x),v))
      (1-linearPicard (T • linearPart r)) u := by
    rw [he]
    exact (1-linearPicard (T • linearPart r)).hasFDerivAt.sub_const _
  exact hc.unique hd

/-- Smooth full-interval solutions near any zero-amplitude linear solution.
The base residual hypothesis is an explicit integral equation, not a flow theorem. -/
theorem smooth_full_interval_paths (r T : ℝ) (x : ReducedState) (u : SourcePath)
    (hu : pathResidual (((0,(r,T)),x),u)=0) :
    ∃ ψ : FlowData → SourcePath,
      ContDiffAt ℝ ⊤ ψ ((0,(r,T)),x) ∧ ψ ((0,(r,T)),x)=u ∧
      ∀ᶠ p in 𝓝 ((0,(r,T)),x), pathResidual (p,ψ p)=0 := by
  have hi : (fderiv ℝ pathResidual (((0,(r,T)),x),u) ∘L
      ContinuousLinearMap.inr ℝ FlowData SourcePath).IsInvertible := by
    rw [pathResidual_path_derivative]
    obtain ⟨v,hv⟩ := linearPicard_one_sub_isUnit (T • linearPart r)
    exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ SourcePath v,hv⟩
  let h := pathResidual_smooth.contDiffAt (x := (((0,(r,T)),x),u))
  refine ⟨h.implicitFunction (by simp) hi,h.contDiffAt_implicitFunction (by simp) hi,
    h.implicitFunction_apply_self (by simp) hi,?_⟩
  simpa only [hu] using h.eventually_apply_implicitFunction (by simp) hi

end
end ThreeSitePhosphorylation.AttractingWitness
