import proofs.ThreeSitePhosphorylation.GenericLocalAttraction
import proofs.ThreeSitePhosphorylation.LinearEndpointInjective
import proofs.ThreeSitePhosphorylation.PhaseImageNeighborhood
import proofs.ThreeSitePhosphorylation.SmoothForwardUniqueness
import proofs.ThreeSitePhosphorylation.ForwardSolutionShift

/-! Upgrade of attraction at one actual return point to orbital asymptotic
stability of the WHOLE exact orbit, for the actual finite-coordinate quadratic
source. The fixed-duration solution maps have invertible state derivatives
(derived from the actual variable-coefficient variational equation and
backward uniqueness); their phase images give an open neighborhood of the
entire orbit, and ODE uniqueness identifies every forward solution. -/
namespace ThreeSitePhosphorylation.GenericWholeOrbit
noncomputable section
open Filter
open scoped Topology
open GenericReturnIFT GenericVariationalODE GenericLocalAttraction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (A0 D : Matrix ι ι ℝ) (K : ℝ → GenericQuadraticTensor.Tensor ι)
variable (hK : ∀ i j k, ContDiff ℝ ⊤ (fun s => K s i j k))

/-- Lyapunov-stable orbital attraction of a set Γ for the autonomous field F,
from an open neighborhood of the whole set, with global forward existence and
uniqueness of forward solutions. -/
def OrbitalAttraction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → E) (Γ : Set E) : Prop :=
  ∀ ε>0, ∃ U : Set E, IsOpen U ∧ Γ ⊆ U ∧ ∀ z∈U, ∃ v : ℝ → E,
    v 0=z ∧
    (∀ t, 0≤t → HasDerivWithinAt v (F (v t)) (Set.Ici 0) t) ∧
    (∀ t, 0≤t → ∃ y∈Γ, dist (v t) y<ε) ∧
    Tendsto (fun t => Metric.infDist (v t) Γ) atTop (𝓝 0) ∧
    (∀ w : ℝ → E, w 0=z →
      (∀ t, 0≤t → HasDerivWithinAt w (F (w t)) (Set.Ici 0) t) →
      ∀ t, 0≤t → w t=v t)

include hK in
theorem rescaledField_smooth (a r : ℝ) : ContDiff ℝ ⊤ (rescaledField A0 D K a r) :=
  (GenericAffinePathExistence.affineField_smooth A0.mulVecLin.toContinuousLinearMap
    D.mulVecLin.toContinuousLinearMap (GenericQuadraticTensor.field K)
    (GenericQuadraticTensor.field_smooth K hK)).comp (contDiff_const.prodMk contDiff_id)

/-- Duration-weighted path field of the residual at fixed amplitude/rate/period. -/
def pathMap (a r T : ℝ) (u : ContinuousPath (ι → ℝ)) : ContinuousPath (ι → ℝ) :=
  T • GenericAffinePathExistence.affineLift A0.mulVecLin.toContinuousLinearMap
    D.mulVecLin.toContinuousLinearMap (GenericQuadraticTensor.pathField K) (a,r) u

set_option maxHeartbeats 2000000 in
include hK in
theorem pathMap_smooth (a r T : ℝ) : ContDiff ℝ ⊤ (pathMap A0 D K a r T) := by
  have heq : pathMap A0 D K a r T=fun u => T • (GenericAffinePathResidual.pathLinear
      A0.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap r u+
        a • GenericQuadraticTensor.pathField K r u) := rfl
  have hB : ContDiff ℝ ⊤ (fun u : ContinuousPath (ι → ℝ) => GenericQuadraticTensor.pathField K r u) :=
    (GenericQuadraticTensor.pathField_smooth K hK).comp (contDiff_const.prodMk contDiff_id)
  have hL := (GenericAffinePathResidual.pathLinear A0.mulVecLin.toContinuousLinearMap
    D.mulVecLin.toContinuousLinearMap r).contDiff (n := ⊤)
  rw [heq]
  exact (contDiff_const (c := T)).smul (hL.add ((contDiff_const (c := a)).smul hB))

theorem pathMap_apply (a r T : ℝ) (u : ContinuousPath (ι → ℝ)) (t : UnitTime) :
    pathMap A0 D K a r T u t=T • rescaledField A0 D K a r (u t) := by
  change T • GenericAffinePathExistence.affineLift A0.mulVecLin.toContinuousLinearMap
    D.mulVecLin.toContinuousLinearMap (GenericQuadraticTensor.pathField K) (a,r) u t=_
  rw [GenericAffinePathExistence.affineLift_apply A0.mulVecLin.toContinuousLinearMap
    D.mulVecLin.toContinuousLinearMap (GenericQuadraticTensor.field K)
    (GenericQuadraticTensor.pathField K) (GenericQuadraticTensor.pathField_apply K)]

theorem residual_eq (a r T : ℝ) (x : ι → ℝ) (u : ContinuousPath (ι → ℝ)) :
    residual A0 D K (((a,(r,T)),x),u)=
      u-constantPath x-linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ)) (pathMap A0 D K a r T u) := by
  simp only [GenericLocalAttraction.residual,GenericAffinePathResidual.pathResidual,pathMap,
    GenericAffinePathExistence.affineLift,map_smul]

include hK in
/-- Actual state derivative along a source path, including physical duration. -/
def stateCoefficient (a r T : ℝ) (u : ContinuousPath (ι → ℝ)) :
    ContinuousPath ((ι → ℝ) →L[ℝ] (ι → ℝ)) :=
  ⟨fun t => T • fderiv ℝ (rescaledField A0 D K a r) (u t),
    continuous_const.smul
      (((rescaledField_smooth A0 D K hK a r).continuous_fderiv (by simp)).comp u.continuous)⟩

omit [DecidableEq ι] in
def coefficientAction (A : ContinuousPath ((ι → ℝ) →L[ℝ] (ι → ℝ)))
    (q : ContinuousPath (ι → ℝ)) : ContinuousPath (ι → ℝ) :=
  ⟨fun t => A t (q t),A.continuous.clm_apply q.continuous⟩

include hK in
/-- Bounded evaluation identifies the derivative of the actual path field. -/
theorem pathMap_fderiv_apply (a r T : ℝ) (u q : ContinuousPath (ι → ℝ)) (t : UnitTime) :
    fderiv ℝ (pathMap A0 D K a r T) u q t=
      T • fderiv ℝ (rescaledField A0 D K a r) (u t) (q t) := by
  let ev := ContinuousMap.evalCLM (R := ℝ) (M := ι → ℝ) t
  have hs := pathMap_smooth A0 D K hK a r T
  have hl := ev.hasFDerivAt.comp u ((hs.differentiable (by simp) u).hasFDerivAt)
  have hr := (((rescaledField_smooth A0 D K hK a r).differentiable (by simp) (u t)).hasFDerivAt.comp
    u ev.hasFDerivAt).const_smul T
  have he : (fun v : ContinuousPath (ι → ℝ) => ev (pathMap A0 D K a r T v))=
      (fun v => T • rescaledField A0 D K a r (ev v)) :=
    funext (fun v => pathMap_apply A0 D K a r T v t)
  simp only [Function.comp_def] at hl hr
  rw [he] at hl
  exact DFunLike.congr_fun (hl.unique hr) q

theorem pathMap_state_direction (a r T : ℝ) (u : ℝ → ContinuousPath (ι → ℝ))
    (q : ContinuousPath (ι → ℝ)) (hu : HasDerivAt u q 0) :
    HasDerivAt (fun s => pathMap A0 D K a r T (u s))
      (coefficientAction (stateCoefficient A0 D K hK a r T (u 0)) q) 0 := by
  have hs := pathMap_smooth A0 D K hK a r T
  have h := ((hs.differentiable (by simp) (u 0)).hasFDerivAt).comp_hasDerivAt 0 hu
  have he : fderiv ℝ (pathMap A0 D K a r T) (u 0) q=
      coefficientAction (stateCoefficient A0 D K hK a r T (u 0)) q := by
    apply ContinuousMap.ext
    intro t
    exact pathMap_fderiv_apply A0 D K hK a r T (u 0) q t
  rwa [he] at h

/-- Differentiating the actual residual with only the initial state varying
yields the variable-coefficient Volterra equation at any amplitude. -/
theorem variable_state_curve_equation (a r T : ℝ) (x dx : ι → ℝ)
    (u : ℝ → ContinuousPath (ι → ℝ)) (q : ContinuousPath (ι → ℝ)) (hu : HasDerivAt u q 0)
    (hres : ∀ᶠ s in 𝓝 (0:ℝ), residual A0 D K (((a,(r,T)),x+s • dx),u s)=0) :
    q=constantPath dx+linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ))
      (coefficientAction (stateCoefficient A0 D K hK a r T (u 0)) q) := by
  have hx : HasDerivAt (fun s : ℝ => x+s • dx) dx 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const dx).const_add x
  have hc := (constantPath (E := ι → ℝ)).hasFDerivAt.comp_hasDerivAt 0 hx
  have hi := (linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ))).hasFDerivAt.comp_hasDerivAt 0
    (pathMap_state_direction A0 D K hK a r T u q hu)
  have hh := (hu.sub hc).sub hi
  have hres' : ∀ᶠ s in 𝓝 (0:ℝ), u s-constantPath (x+s • dx)-
      linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ)) (pathMap A0 D K a r T (u s))=0 := by
    filter_upwards [hres] with s hs
    rwa [residual_eq] at hs
  have hz : HasDerivAt (fun s : ℝ => u s-constantPath (x+s • dx)-
      linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ)) (pathMap A0 D K a r T (u s))) 0 0 :=
    (hasDerivAt_const (x := (0:ℝ)) (c := (0:ContinuousPath (ι → ℝ)))).congr_of_eventuallyEq hres'
  have hd := hh.unique hz
  exact sub_eq_iff_eq_add.mp (sub_eq_zero.mp hd) |>.trans (add_comm _ _)

variable (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))

theorem variable_state_path_equation (a r T : ℝ) (x dx : ι → ℝ)
    (hψ : ContDiffAt ℝ ⊤ ψ ((a,(r,T)),x))
    (hres : ∀ᶠ d in 𝓝 ((a,(r,T)),x), residual A0 D K (d,ψ d)=0) :
    let q := fderiv ℝ ψ ((a,(r,T)),x) ((0,(0,0)),dx)
    q=constantPath dx+linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ))
      (coefficientAction (stateCoefficient A0 D K hK a r T (ψ ((a,(r,T)),x))) q) := by
  let e : ℝ → GenericShootingMap.FlowData (ι → ℝ) := fun s => ((a,(r,T)),x+s • dx)
  let u : ℝ → ContinuousPath (ι → ℝ) := fun s => ψ (e s)
  let q := fderiv ℝ ψ ((a,(r,T)),x) ((0,(0,0)),dx)
  have hx : HasDerivAt (fun s : ℝ => x+s • dx) dx 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const dx).const_add x
  have he : HasDerivAt e (((0:ℝ),(0,0)),dx) 0 :=
    (hasDerivAt_const (0:ℝ) ((a:ℝ),(r,T))).prodMk hx
  have hu : HasDerivAt u q 0 :=
    (hψ.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 he (by simp [e])
  have hev : ∀ᶠ s in 𝓝 (0:ℝ), residual A0 D K (((a,(r,T)),x+s • dx),u s)=0 := by
    have ht : Filter.Tendsto e (𝓝 0) (𝓝 ((a,(r,T)),x)) := by
      simpa only [e,zero_smul,add_zero] using he.continuousAt.tendsto
    exact ht.eventually hres
  simpa only [u,e,zero_smul,add_zero] using
    variable_state_curve_equation A0 D K hK a r T x dx u q hu hev

include hK in
theorem variable_state_path_initial (a r T : ℝ) (x dx : ι → ℝ)
    (hψ : ContDiffAt ℝ ⊤ ψ ((a,(r,T)),x))
    (hres : ∀ᶠ d in 𝓝 ((a,(r,T)),x), residual A0 D K (d,ψ d)=0) :
    fderiv ℝ ψ ((a,(r,T)),x) ((0,(0,0)),dx) (⟨0,by norm_num⟩ : UnitTime)=dx := by
  have h := variable_state_path_equation A0 D K hK ψ a r T x dx hψ hres
  have he := congrArg (fun q : ContinuousPath (ι → ℝ) => q (⟨0,by norm_num⟩ : UnitTime)) h
  change _=dx+∫ s in (0:ℝ)..0, _ at he
  simpa using he

omit [DecidableEq ι] in
def statePathOperator (a r T : ℝ) (x : ι → ℝ) : (ι → ℝ) →L[ℝ] ContinuousPath (ι → ℝ) :=
  (fderiv ℝ ψ ((a,(r,T)),x)).comp (ContinuousLinearMap.inr ℝ (ℝ × (ℝ × ℝ)) (ι → ℝ))

omit [DecidableEq ι] in
def variableEndpoint (a r T : ℝ) (x : ι → ℝ) (t : ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  (ContinuousMap.evalCLM (R := ℝ) (M := ι → ℝ)
    (Set.projIcc 0 1 (by norm_num) t)).comp (statePathOperator ψ a r T x)

omit [DecidableEq ι] in
/-- A continuous path satisfying the variable Volterra equation solves its
linear ODE from the left at every positive phase, including phase one. -/
theorem coefficient_equation_left_derivative
    (A : ContinuousPath ((ι → ℝ) →L[ℝ] (ι → ℝ))) (q : ContinuousPath (ι → ℝ))
    (dx : ι → ℝ)
    (hq : q=constantPath dx+linearPicard (ContinuousLinearMap.id ℝ (ι → ℝ))
      (coefficientAction A q)) (t : ℝ) (ht : 0<t) (ht1 : t≤1) :
    HasDerivWithinAt (pathExtension q)
      (pathExtension A t (pathExtension q t)) (Set.Iic t) t := by
  let f : ℝ → (ι → ℝ) := pathExtension (coefficientAction A q)
  let v : ℝ → (ι → ℝ) := fun s => dx+∫ z in (0:ℝ)..s, f z
  have hc : Continuous f := pathExtension_continuous (coefficientAction A q)
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (0:ℝ) t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add dx
  have he (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) : pathExtension q s=v s := by
    rw [pathExtension,Set.projIcc_of_mem _ hs]
    have hh := congrArg (fun u : ContinuousPath (ι → ℝ) => u ⟨s,hs⟩) hq
    exact hh
  have hev : pathExtension q =ᶠ[𝓝[Set.Iic t] t] v := by
    filter_upwards [Ioc_mem_nhdsLE ht] with s hs
    exact he s ⟨hs.1.le,hs.2.trans ht1⟩
  have hh := hd.hasDerivWithinAt.congr_of_eventuallyEq hev (he t ⟨ht.le,ht1⟩)
  exact hh

include hK in
theorem variableEndpoint_initial (a r T : ℝ) (x : ι → ℝ)
    (hψ : ContDiffAt ℝ ⊤ ψ ((a,(r,T)),x))
    (hres : ∀ᶠ d in 𝓝 ((a,(r,T)),x), residual A0 D K (d,ψ d)=0) :
    variableEndpoint ψ a r T x 0=1 := by
  apply ContinuousLinearMap.ext
  intro dx
  simpa [variableEndpoint,statePathOperator,Set.projIcc_of_mem]
    using variable_state_path_initial A0 D K hK ψ a r T x dx hψ hres

theorem variableEndpoint_left_derivative (a r T : ℝ) (x : ι → ℝ)
    (hψ : ContDiffAt ℝ ⊤ ψ ((a,(r,T)),x))
    (hres : ∀ᶠ d in 𝓝 ((a,(r,T)),x), residual A0 D K (d,ψ d)=0)
    (dx : ι → ℝ) (t : ℝ) (ht : 0<t) (ht1 : t≤1) :
    HasDerivWithinAt (fun s => variableEndpoint ψ a r T x s dx)
      (pathExtension (stateCoefficient A0 D K hK a r T (ψ ((a,(r,T)),x))) t
        (variableEndpoint ψ a r T x t dx)) (Set.Iic t) t := by
  exact coefficient_equation_left_derivative
    (stateCoefficient A0 D K hK a r T (ψ ((a,(r,T)),x))) (statePathOperator ψ a r T x dx) dx
    (variable_state_path_equation A0 D K hK ψ a r T x dx hψ hres) t ht ht1

include hK in
/-- Actual endpoint invertibility at each phase, from the derived
variable-coefficient ODE and backward uniqueness in finite dimension. -/
theorem variableEndpoint_isUnit (a r T : ℝ) (x : ι → ℝ)
    (hψ : ContDiffAt ℝ ⊤ ψ ((a,(r,T)),x))
    (hres : ∀ᶠ d in 𝓝 ((a,(r,T)),x), residual A0 D K (d,ψ d)=0) (s : UnitTime) :
    IsUnit (variableEndpoint ψ a r T x (s:ℝ)) := by
  let A := stateCoefficient A0 D K hK a r T (ψ ((a,(r,T)),x))
  apply LinearEndpointInjective.endpoint_isUnit (pathExtension A)
    (variableEndpoint ψ a r T x) (s:ℝ) s.2.1 ⟨‖A‖,norm_nonneg A⟩
  · intro t _
    exact ContinuousMap.norm_coe_le_norm A _
  · exact variableEndpoint_initial A0 D K hK ψ a r T x hψ hres
  · intro dx
    exact (pathExtension_continuous (statePathOperator ψ a r T x dx)).continuousOn
  · intro dx t ht
    exact variableEndpoint_left_derivative A0 D K hK ψ a r T x hψ hres dx t ht.1
      (ht.2.trans s.2.2)

omit [DecidableEq ι] in
theorem variableEndpoint_fderiv (a r T : ℝ) (x : ι → ℝ)
    (hψ : ContDiffAt ℝ ⊤ ψ ((a,(r,T)),x)) (s : UnitTime) :
    fderiv ℝ (fun y : ι → ℝ => ψ ((a,(r,T)),y) s) x=variableEndpoint ψ a r T x (s:ℝ) := by
  have hi : HasFDerivAt (fun y : ι → ℝ => ((a,(r,T)),y))
      (ContinuousLinearMap.inr ℝ (ℝ × (ℝ × ℝ)) (ι → ℝ)) x := by
    convert (hasFDerivAt_const (𝕜 := ℝ) (a,(r,T)) x).prodMk (hasFDerivAt_id x) using 1
  have hp := (hψ.differentiableAt (by simp)).hasFDerivAt.comp x hi
  have he := (ContinuousMap.evalCLM (R := ℝ) (M := ι → ℝ) s).hasFDerivAt.comp x hp
  simpa only [variableEndpoint,statePathOperator,Set.projIcc_of_mem _ s.2] using he.fderiv

include hK in
/-- The actual fixed-duration source maps send a neighborhood of the initial
point to an open set containing the entire reference path, and every point
of this open set has a phase and an initial preimage in the prescribed set. -/
theorem phase_neighborhood (a r T : ℝ) (p : ι → ℝ)
    (hψ : ContDiffAt ℝ ⊤ ψ ((a,(r,T)),p))
    (hres : ∀ᶠ d in 𝓝 ((a,(r,T)),p), residual A0 D K (d,ψ d)=0)
    (B : Set (ι → ℝ)) (hB : B∈𝓝 p) :
    ∃ U : Set (ι → ℝ), IsOpen U ∧
      Set.range (ψ ((a,(r,T)),p)) ⊆ U ∧
      ∀ z∈U, ∃ s : UnitTime, ∃ x∈B, ψ ((a,(r,T)),x) s=z := by
  let Φ : UnitTime → (ι → ℝ) → (ι → ℝ) := fun s x => ψ ((a,(r,T)),x) s
  have hΦ (s : UnitTime) : map (Φ s) (𝓝 p)=𝓝 (Φ s p) := by
    have hs : ContDiffAt ℝ ⊤ (Φ s) p :=
      (ContinuousMap.evalCLM (R := ℝ) (M := ι → ℝ) s).contDiff.contDiffAt.comp p
        (hψ.comp p (by fun_prop))
    have hu : IsUnit (fderiv ℝ (Φ s) p) := by
      change IsUnit (fderiv ℝ (fun y : ι → ℝ => ψ ((a,(r,T)),y) s) p)
      rw [variableEndpoint_fderiv ψ a r T p hψ s]
      exact variableEndpoint_isUnit A0 D K hK ψ a r T p hψ hres s
    exact PhaseImageNeighborhood.map_nhds_of_isUnit_derivative (Φ s) p
      (fderiv ℝ (Φ s) p) (hs.hasStrictFDerivAt (by simp)) hu
  refine ⟨PhaseImageNeighborhood.phaseImages Φ B,
    PhaseImageNeighborhood.phaseImages_open Φ B,?_,?_⟩
  · exact PhaseImageNeighborhood.reference_range_subset Φ p B hB hΦ
  · intro z hz
    exact PhaseImageNeighborhood.phaseImages_has_preimage Φ B hz

include hK in
/-- Every actual forward solution agrees with the residual-defined fixed
duration arc. -/
theorem fixed_arc_matches_forward (a r T : ℝ) (x : ι → ℝ) (hT : 0<T)
    (hres : residual A0 D K (((a,(r,T)),x),ψ ((a,(r,T)),x))=0)
    (v : ℝ → (ι → ℝ)) (hv0 : v 0=x)
    (hv : ∀ t, 0≤t → HasDerivWithinAt v (rescaledField A0 D K a r (v t)) (Set.Ici 0) t) :
    ∀ s : UnitTime, v (T*(s:ℝ))=ψ ((a,(r,T)),x) s := by
  let p : GenericShootingMap.FlowData (ι → ℝ) := ((a,(r,T)),x)
  let u := ψ p
  let pc := GenericPathContinuation.pathContinuation A0.mulVecLin.toContinuousLinearMap
    D.mulVecLin.toContinuousLinearMap (GenericQuadraticTensor.pathField K) p u
  let g : ℝ → (ι → ℝ) := fun t => pc (t/T)
  have hg (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) T) :
      HasDerivAt g (rescaledField A0 D K a r (g t)) t := by
    have hs : t/T ∈ Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg ht.1 hT.le,(div_le_one hT).mpr ht.2⟩
    have hd := GenericPathContinuation.pathContinuation_solves A0.mulVecLin.toContinuousLinearMap
      D.mulVecLin.toContinuousLinearMap (GenericQuadraticTensor.field K)
      (GenericQuadraticTensor.pathField K) (GenericQuadraticTensor.pathField_apply K)
      p u hres (t/T) hs
    have ht' : HasDerivAt (fun t : ℝ => t/T) (1/T) t := by
      simpa using (hasDerivAt_id t).div_const T
    have hh := hd.scomp t ht'
    simpa only [g,pc,p,smul_smul,one_div,inv_mul_cancel₀ (ne_of_gt hT),one_smul] using hh
  have hvc : ContinuousOn v (Set.Icc (0:ℝ) T) := by
    intro t ht
    exact (hv t ht.1).continuousWithinAt.mono (fun _ hs => hs.1)
  have hgc : ContinuousOn g (Set.Icc (0:ℝ) T) := by
    intro t ht
    exact (hg t ht).continuousAt.continuousWithinAt
  have hvd : ∀ t ∈ Set.Ico (0:ℝ) T,
      HasDerivWithinAt v (rescaledField A0 D K a r (v t)) (Set.Ici t) t := by
    intro t ht
    exact (hv t ht.1).mono (fun _ hs => ht.1.trans hs)
  have hgd : ∀ t ∈ Set.Ico (0:ℝ) T,
      HasDerivWithinAt g (rescaledField A0 D K a r (g t)) (Set.Ici t) t := by
    intro t ht
    exact (hg t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt
  have hinit : v 0=g 0 := by
    simpa [g,pc,GenericPathContinuation.pathContinuation_initial,p] using hv0
  have he := SmoothForwardUniqueness.eqOn_Icc (rescaledField A0 D K a r)
    (rescaledField_smooth A0 D K hK a r) v g 0 T hvc hgc hvd hgd hinit
  intro s
  have ht : T*(s:ℝ) ∈ Set.Icc (0:ℝ) T :=
    ⟨mul_nonneg hT.le s.2.1,by nlinarith [s.2.2]⟩
  have hs : (T*(s:ℝ))/T=(s:ℝ) := by field_simp [ne_of_gt hT]
  have hh := he ht
  dsimp only [g] at hh
  rw [hs] at hh
  exact hh.trans (GenericPathContinuation.pathContinuation_eq _ _ _ p u hres s).symm

include hK in
/-- Actual fixed-time endpoint openness and ODE uniqueness upgrade attraction
at one return point to orbital attraction from a neighborhood of the entire
orbit. The variable return-time maps need not be locally invertible. -/
theorem local_to_whole_orbit (a r T : ℝ) (p : ι → ℝ) (hT : 0<T)
    (hψ : ContDiffAt ℝ ⊤ ψ ((a,(r,T)),p))
    (hres : ∀ᶠ d in 𝓝 ((a,(r,T)),p), residual A0 D K (d,ψ d)=0)
    (hlocal : ∀ ε>0, ∃ η>0, ∀ x, dist x p<η → ∃ y : ℝ → (ι → ℝ),
      y 0=x ∧
      (∀ t, 0≤t → HasDerivWithinAt y (rescaledField A0 D K a r (y t)) (Set.Ici 0) t) ∧
      (∀ t, 0≤t → ∃ s : UnitTime, dist (y t) (ψ ((a,(r,T)),p) s)<ε) ∧
      Tendsto (fun t => Metric.infDist (y t) (Set.range (ψ ((a,(r,T)),p)))) atTop (𝓝 0)) :
    OrbitalAttraction (rescaledField A0 D K a r) (Set.range (ψ ((a,(r,T)),p))) := by
  intro ε hε
  obtain ⟨η,hη,hloc⟩ := hlocal ε hε
  let B : Set (ι → ℝ) := {x | dist x p<η ∧ residual A0 D K (((a,(r,T)),x),ψ ((a,(r,T)),x))=0}
  have hB : B∈𝓝 p := by
    have hi : ContinuousAt (fun x : ι → ℝ => ((a,(r,T)),x)) p := by fun_prop
    exact Filter.inter_mem (Metric.ball_mem_nhds p hη) (hi.tendsto.eventually hres)
  obtain ⟨V,hV,hcover,hpre⟩ := phase_neighborhood A0 D K hK ψ a r T p hψ hres B hB
  refine ⟨V,hV,hcover,?_⟩
  intro z hz
  obtain ⟨s,x,hx,hxz⟩ := hpre z hz
  obtain ⟨v,hv0,hvd,hvt,hva⟩ := hloc x hx.1
  let σ : ℝ := T*(s:ℝ)
  have hσ : 0≤σ := mul_nonneg hT.le s.2.1
  have hmatch : v σ=z := by
    rw [fixed_arc_matches_forward A0 D K hK ψ a r T x hT hx.2 v hv0 hvd s,hxz]
  let vshift : ℝ → (ι → ℝ) := fun t => v (t+σ)
  have hs0 : vshift 0=z := by simpa only [vshift,zero_add] using hmatch
  have hsd : ∀ t, 0≤t → HasDerivWithinAt vshift
      (rescaledField A0 D K a r (vshift t)) (Set.Ici 0) t :=
    ForwardSolutionShift.source (rescaledField A0 D K a r) v σ hσ hvd
  refine ⟨vshift,hs0,hsd,?_,?_,?_⟩
  · intro t ht
    obtain ⟨s',hs'⟩ := hvt (t+σ) (add_nonneg ht hσ)
    exact ⟨_,Set.mem_range_self s',hs'⟩
  · exact ForwardSolutionShift.orbit_attraction v _ σ hva
  · intro w hw0 hwd
    exact SmoothForwardUniqueness.forward_unique (rescaledField A0 D K a r)
      (rescaledField_smooth A0 D K hK a r) w vshift hwd hsd (hw0.trans hs0.symm)

end
end ThreeSitePhosphorylation.GenericWholeOrbit
