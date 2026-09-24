import proofs.ThreeSitePhosphorylation.GenericWholeOrbit
import proofs.ThreeSitePhosphorylation.GenericBranchMultipliers
import proofs.ThreeSitePhosphorylation.GenericPeriodicExtension

/-! The dimension-independent attracting Hopf family. For an actual finite
coordinate quadratic source with a full simple complex eigenbasis (real stable
columns, conjugate critical pair), negative crossing and negative normalized
branch coefficient, the actual closed branch consists, for small positive
amplitude, of nonconstant periodic solutions of the literal centered field
`(A0+rD)z+Q_r(z)` that are orbitally asymptotically stable from an open
neighborhood of the whole orbit. The period tends to `2π/ω`, the kinetic
parameter to its critical value, and the orbits shrink uniformly to the
equilibrium `z=0`. Attraction is produced, not assumed. -/
namespace ThreeSitePhosphorylation.GenericAttractingFamily
noncomputable section
open Filter
open scoped Topology Pointwise
open GenericReturnIFT GenericClosedPaths GenericReturnContracts GenericReturnLinearization
open GenericLocalAttraction GenericWholeOrbit

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {A0 D : Matrix ι ι ℝ} {K : ℝ → GenericQuadraticTensor.Tensor ι}
variable {r w : ℝ} {v : ι → ℂ}

omit [Fintype σ] [DecidableEq σ] in
/-- Local regularity and residual hypotheses of the return estimates hold at
nearby points of the actual closed branch. -/
theorem reference_regular {C : ClosedPathFamily A0 D (GenericQuadraticTensor.pathField K) r w v}
    (R : ReturnFlow C) (hw : 0<w) :
    ∀ᶠ a in 𝓝 (0:ℝ),
      ContDiffAt ℝ ⊤ R.τ (branchReturnData C a) ∧
      ContDiffAt ℝ ⊤ R.ψ (returnArgument (branchReturnData C a,R.τ (branchReturnData C a))) ∧
      (∀ᶠ z in 𝓝 (returnArgument (branchReturnData C a,R.τ (branchReturnData C a))),
        residual A0 D K (z,R.ψ z)=0) ∧
      0<R.τ (branchReturnData C a) ∧
      returnPoint R.ψ R.τ (branchReturnData C a)=(C.parameters a).1 := by
  let d := branchReturnData C
  let e : ℝ → GenericShootingMap.FlowData (ι → ℝ) := fun a => returnArgument (d a,R.τ (d a))
  have hd0 : d 0=((0,r),GenericComplexification.realPart v) := branchReturnData_zero C
  have hd : ContDiffAt ℝ ⊤ d 0 := branchReturnData_smooth C
  have hτ : ContDiffAt ℝ ⊤ R.τ (d 0) := by simpa only [hd0] using R.τ_smooth
  have hτd := hτ.comp 0 hd
  have he : ContDiffAt ℝ ⊤ e 0 := returnArgument_smooth.contDiffAt.comp 0 (hd.prodMk hτd)
  have he0 : e 0=((0,(r,2*Real.pi/w)),GenericComplexification.realPart v) := by
    simp only [e,hd0,R.τ_zero,returnArgument]
  have hψ : ContDiffAt ℝ ⊤ R.ψ (e 0) := by simpa only [he0] using R.ψ_smooth
  have hres : ∀ᶠ z in 𝓝 (e 0), residual A0 D K (z,R.ψ z)=0 := by
    simpa only [he0] using R.residual
  have hpos : 0<R.τ (d 0) := by rw [hd0,R.τ_zero]; positivity
  filter_upwards [hd.continuousAt.tendsto.eventually (hτ.eventually (by simp)),
    he.continuousAt.tendsto.eventually (hψ.eventually (by simp)),
    he.continuousAt.tendsto.eventually hres.eventually_nhds,
    hτd.continuousAt.tendsto.eventually (Ioi_mem_nhds hpos),R.branch_closed]
    with a ha hb hc ht hclosed
  exact ⟨ha,hb,hc,ht,hclosed.2⟩

omit [Fintype σ] [DecidableEq σ] in
/-- The reference arc of the return construction is the closed path of the
source shooting construction, and its duration is the branch period. -/
theorem reference_arc {C : ClosedPathFamily A0 D (GenericQuadraticTensor.pathField K) r w v}
    (R : ReturnFlow C) :
    ∀ᶠ a in 𝓝 (0:ℝ),
      R.τ (branchReturnData C a)=(C.parameters a).2.im ∧
      R.ψ (returnArgument (branchReturnData C a,R.τ (branchReturnData C a)))=C.paths a := by
  filter_upwards [R.branch_closed,
    GenericReturnBranch.closed_family_solution_operator A0 D _ v r w C R.ψ R.path_unique]
    with a ha hb
  refine ⟨ha.1,?_⟩
  change R.ψ ((a,((C.parameters a).2.re,R.τ (branchReturnData C a))),(C.parameters a).1)=_
  rw [show R.τ (branchReturnData C a)=(C.parameters a).2.im from ha.1]
  exact hb

omit [DecidableEq ι] [Fintype σ] [DecidableEq σ] in
theorem return_state_slice_fderiv
    (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (τ : ReturnData (ι → ℝ) → ℝ) (a r : ℝ) (p : ι → ℝ)
    (hd : DifferentiableAt ℝ (returnPoint ψ τ) ((a,r),p)) :
    fderiv ℝ (fun x => returnPoint ψ τ ((a,r),x)) p=
      GenericReturnBaseEigenbasis.stateDerivative ψ τ ((a,r),p) := by
  have hi : HasFDerivAt (fun x : ι → ℝ => ((a,r),x))
      (ContinuousLinearMap.inr ℝ (ℝ×ℝ) (ι → ℝ)) p := by
    simpa using (hasFDerivAt_const (a,r) p).prodMk (hasFDerivAt_id p)
  exact (hd.hasFDerivAt.comp p hi).fderiv

omit [DecidableEq σ] in
/-- Strict multipliers of the actual branch return derivative give orbital
attraction of the WHOLE exact closed orbit in rescaled coordinates. -/
theorem closed_branch_rescaled_orbital_attraction
    (hK : ∀ i j k, ContDiff ℝ ⊤ (fun s => K s i j k)) (hw : 0<w)
    {C : ClosedPathFamily A0 D (GenericQuadraticTensor.pathField K) r w v}
    (R : ReturnFlow C)
    (hstrict : ∀ᶠ a in 𝓝[>] (0:ℝ), ∃ c : Module.Basis (σ ⊕ Fin 2) ℝ (ι → ℝ),
      ∃ eig : σ ⊕ Fin 2 → ℝ,
        (∀ i, branchDerivative R a (c i)=eig i • c i) ∧ ∀ i, |eig i|<1) :
    ∀ᶠ a in 𝓝[>] (0:ℝ),
      OrbitalAttraction (rescaledField A0 D K a (C.parameters a).2.re)
        (Set.range (C.paths a)) := by
  filter_upwards [hstrict,(reference_regular R hw).filter_mono nhdsWithin_le_nhds,
    (reference_arc R).filter_mono nhdsWithin_le_nhds]
    with a hmult hregular href
  obtain ⟨c,eig,he,heig⟩ := hmult
  obtain ⟨hτ,hψ,hreslocal,hT,hp⟩ := hregular
  have hd := (returnPoint_smooth R.ψ R.τ (branchReturnData C a) hτ hψ).differentiableAt (by simp)
  have he' : ∀ i, (fderiv ℝ
      (fun x => returnPoint R.ψ R.τ ((a,(C.parameters a).2.re),x))
      (C.parameters a).1) (c i)=eig i • c i := by
    rw [return_state_slice_fderiv R.ψ R.τ a (C.parameters a).2.re (C.parameters a).1 hd]
    exact he
  have hlocal := local_rescaled_attraction A0 D K R.ψ R.τ a (C.parameters a).2.re
    (C.parameters a).1 hτ hψ hT hp hreslocal c eig he' heig
  have hwhole := local_to_whole_orbit A0 D K hK R.ψ a (C.parameters a).2.re
    (R.τ (branchReturnData C a)) (C.parameters a).1 hT hψ hreslocal hlocal
  have hr : R.ψ ((a,((C.parameters a).2.re,R.τ (branchReturnData C a))),(C.parameters a).1)=
      C.paths a := href.2
  rw [hr] at hwhole
  exact hwhole

omit [Fintype σ] [DecidableEq σ] in
/-- Physical-time orbital attraction is transported exactly by the amplitude
scaling `z=a*y`, from the rescaled field to the literal centered field. -/
theorem scale_orbital_attraction
    (a r : ℝ) (ha : a ≠ 0) (Γ : Set (ι → ℝ))
    (h : OrbitalAttraction (rescaledField A0 D K a r) Γ) :
    OrbitalAttraction (GenericQuadraticDynamics.field A0 D K r) (a • Γ) := by
  have hfield (y : ι → ℝ) : GenericQuadraticDynamics.field A0 D K r (a • y)=
      a • rescaledField A0 D K a r y := by
    rw [GenericQuadraticDynamics.field_scaling,rescaledField_eq]
  have hna : 0<‖a‖ := norm_pos_iff.mpr ha
  intro ε hε
  obtain ⟨U,hU,hΓU,hsol⟩ := h (ε/‖a‖) (div_pos hε hna)
  refine ⟨a • U,isOpenMap_smul₀ ha U hU,Set.smul_set_mono hΓU,?_⟩
  rintro _ ⟨z,hz,rfl⟩
  obtain ⟨y,hy0,hyd,hyt,hya,hyu⟩ := hsol z hz
  refine ⟨fun t => a • y t,by simp only [hy0],?_,?_,?_,?_⟩
  · intro t ht
    have hh := (hyd t ht).const_smul a
    rwa [← hfield] at hh
  · intro t ht
    obtain ⟨g,hg,hgt⟩ := hyt t ht
    refine ⟨a • g,Set.smul_mem_smul_set hg,?_⟩
    rw [dist_smul₀]
    calc ‖a‖*dist (y t) g<‖a‖*(ε/‖a‖) := mul_lt_mul_of_pos_left hgt hna
      _ = ε := by field_simp
  · have hh := hya.const_mul ‖a‖
    rw [mul_zero] at hh
    refine hh.congr' (Eventually.of_forall (fun t => ?_))
    exact (infDist_smul₀ ha Γ (y t)).symm
  · intro u hu0 hud t ht
    let y' : ℝ → (ι → ℝ) := fun s => a⁻¹ • u s
    have hy'0 : y' 0=z := by simp only [y',hu0,inv_smul_smul₀ ha]
    have hy'd : ∀ s : ℝ, 0 ≤ s → HasDerivWithinAt y' (rescaledField A0 D K a r (y' s)) (Set.Ici 0) s := by
      intro s hs
      have hh := (hud s hs).const_smul a⁻¹
      have he : u s=a • y' s := by simp only [y',smul_inv_smul₀ ha]
      rw [he,hfield,inv_smul_smul₀ ha] at hh
      exact hh
    have hy := hyu y' hy'0 hy'd t ht
    have : u t=a • y' t := by simp only [y',smul_inv_smul₀ ha]
    rw [this,hy]

omit [DecidableEq ι] [Fintype σ] [DecidableEq σ] in
def periodicOrbit (C : ClosedPathFamily A0 D (GenericQuadraticTensor.pathField K) r w v)
    (a t : ℝ) : ι → ℝ :=
  a • GenericPeriodicExtension.periodicCurve 1 (by norm_num)
    (GenericPathContinuation.pathContinuation A0.mulVecLin.toContinuousLinearMap
      D.mulVecLin.toContinuousLinearMap (GenericQuadraticTensor.pathField K)
      (GenericShootingMap.shootingArgument (a,C.parameters a)) (C.paths a))
    (t/(C.parameters a).2.im)

omit [Fintype σ] [DecidableEq σ] in
/-- The physical periodic solution: exact range, period, literal centered
dynamics, and initial point. -/
theorem periodicOrbit_properties (C : ClosedPathFamily A0 D (GenericQuadraticTensor.pathField K) r w v)
    (a : ℝ) (hT : 0<(C.parameters a).2.im)
    (hres : residual A0 D K (GenericShootingMap.shootingArgument (a,C.parameters a),C.paths a)=0)
    (hclosed : C.paths a ⟨1,by norm_num⟩=(C.parameters a).1) :
    Set.range (periodicOrbit C a)=a • Set.range (C.paths a) ∧
    Function.Periodic (periodicOrbit C a) (C.parameters a).2.im ∧
    (∀ t, HasDerivAt (periodicOrbit C a)
      (GenericQuadraticDynamics.field A0 D K (C.parameters a).2.re (periodicOrbit C a t)) t) ∧
    periodicOrbit C a 0=a • (C.parameters a).1 := by
  let T := (C.parameters a).2.im
  let p := GenericShootingMap.shootingArgument (a,C.parameters a)
  let f : ℝ → (ι → ℝ) := GenericPathContinuation.pathContinuation
    A0.mulVecLin.toContinuousLinearMap D.mulVecLin.toContinuousLinearMap
    (GenericQuadraticTensor.pathField K) p (C.paths a)
  let g := GenericPeriodicExtension.periodicCurve 1 (by norm_num) f
  have hT0 : T ≠ 0 := ne_of_gt hT
  have hf0 : f 0=(C.parameters a).1 := GenericPathContinuation.pathContinuation_initial _ _ _ _ _
  have he : f 0=f 1 := by
    rw [hf0]
    exact hclosed.symm.trans
      (GenericPathContinuation.pathContinuation_eq _ _ _ p (C.paths a) hres ⟨1,by norm_num⟩)
  have hf (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :
      HasDerivAt f (T • rescaledField A0 D K a (C.parameters a).2.re (f s)) s :=
    GenericPathContinuation.pathContinuation_solves A0.mulVecLin.toContinuousLinearMap
      D.mulVecLin.toContinuousLinearMap (GenericQuadraticTensor.field K)
      (GenericQuadraticTensor.pathField K) (GenericQuadraticTensor.pathField_apply K)
      p (C.paths a) hres s hs
  have hg := GenericPeriodicExtension.periodicCurve_source 1 (by norm_num)
    (fun x => T • rescaledField A0 D K a (C.parameters a).2.re x) f he hf
  refine ⟨?_,?_,?_,?_⟩
  · have hr := GenericPeriodicExtension.periodicCurve_physical_range T hT0 f he
    have hpath : (fun t : Set.Icc (0:ℝ) 1 => f t)=⇑(C.paths a) := by
      funext t
      exact (GenericPathContinuation.pathContinuation_eq _ _ _ p (C.paths a) hres t).symm
    rw [hpath] at hr
    ext z
    constructor
    · rintro ⟨t,rfl⟩
      have hm : g (t/T) ∈ Set.range (C.paths a) := by
        rw [← hr]
        exact Set.mem_range_self t
      exact Set.smul_mem_smul_set hm
    · rintro ⟨y,hy,rfl⟩
      rw [← hr] at hy
      obtain ⟨t,rfl⟩ := hy
      exact ⟨t,rfl⟩
  · intro t
    change a • g ((t+T)/T)=a • g (t/T)
    rw [add_div,div_self hT0]
    exact congrArg (fun y => a • y) (GenericPeriodicExtension.periodicCurve_periodic 1
      (by norm_num) f (t/T))
  · intro t
    have hh := (hg (t/T)).scomp t ((hasDerivAt_id t).div_const T)
    have hh' : HasDerivAt (fun s => g (s/T))
        (rescaledField A0 D K a (C.parameters a).2.re (g (t/T))) t := by
      simpa only [id_eq,one_div,smul_smul,inv_mul_cancel₀ hT0,one_smul,Function.comp_def]
        using hh
    have hs := hh'.const_smul a
    have hfe : GenericQuadraticDynamics.field A0 D K (C.parameters a).2.re (a • g (t/T))=
        a • rescaledField A0 D K a (C.parameters a).2.re (g (t/T)) := by
      rw [GenericQuadraticDynamics.field_scaling,rescaledField_eq]
    show HasDerivAt (fun s => a • g (s/T))
      (GenericQuadraticDynamics.field A0 D K (C.parameters a).2.re (a • g (t/T))) t
    rw [hfe]
    exact hs
  · change a • g (0/T)=_
    rw [zero_div]
    change a • GenericPeriodicExtension.periodicCurve 1 (by norm_num) f 0=_
    rw [GenericPeriodicExtension.periodicCurve_eq 1 (by norm_num) f 0 (by norm_num),hf0]
end
end ThreeSitePhosphorylation.GenericAttractingFamily
