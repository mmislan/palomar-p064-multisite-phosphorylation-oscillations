import proofs.ThreeSitePhosphorylation.GenericReturnIFT
import proofs.ThreeSitePhosphorylation.GenericPathContinuation
import proofs.ThreeSitePhosphorylation.GenericQuadraticDynamics
import proofs.ThreeSitePhosphorylation.RealEigenbasisContraction
import proofs.ThreeSitePhosphorylation.ReturnIterateControl
import proofs.ThreeSitePhosphorylation.ReturnArcConcatenation

/-! Continuous-time local attraction for the actual residual-defined return
map of a finite-coordinate quadratic source. From an actual derivative
eigenbasis with strict multipliers we obtain a contracting power, control of
every intermediate iterate, uniform positive return times, concatenation of
actual solution arcs into a global forward solution, arbitrarily small tubes
and convergence of the distance to the exact orbit. No contraction, forward
existence or tube estimate is assumed. -/
namespace ThreeSitePhosphorylation.GenericLocalAttraction
noncomputable section
open Filter NonZenoReturns
open scoped Topology
open GenericReturnIFT

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (A0 D : Matrix ι ι ℝ) (K : ℝ → GenericQuadraticTensor.Tensor ι)

/-- The literal amplitude-rescaled residual of the quadratic source. -/
abbrev residual : GenericShootingMap.FlowData (ι → ℝ) × ContinuousPath (ι → ℝ) →
    ContinuousPath (ι → ℝ) :=
  GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
    D.mulVecLin.toContinuousLinearMap (GenericQuadraticTensor.pathField K)

/-- The literal amplitude-rescaled field `(A0+rD)y+a Q_r(y)`. -/
abbrev rescaledField (a r : ℝ) (y : ι → ℝ) : ι → ℝ :=
  GenericAffinePathExistence.affineField A0.mulVecLin.toContinuousLinearMap
    D.mulVecLin.toContinuousLinearMap (GenericQuadraticTensor.field K) (a,r) y

omit [Fintype ι] [DecidableEq ι] in
theorem derivative_local_radial_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (p : E) (L : E →L[ℝ] F) (hd : HasFDerivAt f L p) :
    ∀ᶠ x in 𝓝 p, ‖f x-f p‖ ≤ (‖L‖+1)*‖x-p‖ := by
  filter_upwards [hd.isLittleO.bound (show (0:ℝ)<1 by norm_num)] with x hx
  calc
    _ = ‖(f x-f p-L (x-p))+L (x-p)‖ := by congr 1; abel
    _ ≤ ‖f x-f p-L (x-p)‖+‖L (x-p)‖ := norm_add_le _ _
    _ ≤ 1*‖x-p‖+‖L‖*‖x-p‖ := add_le_add hx (L.le_opNorm _)
    _ = _ := by ring

variable (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
variable (τ : ReturnData (ι → ℝ) → ℝ)

/-- Actual return arcs inherit a uniform phase bound from their path-space
derivative, with actual residual equations and positive bounded return times. -/
theorem return_arc_control (a r : ℝ) (p : ι → ℝ)
    (hτ : ContDiffAt ℝ ⊤ τ ((a,r),p))
    (hψ : ContDiffAt ℝ ⊤ ψ (returnArgument (((a,r),p),τ ((a,r),p))))
    (hT : 0<τ ((a,r),p))
    (hres : ∀ᶠ d in 𝓝 (returnArgument (((a,r),p),τ ((a,r),p))),
      residual A0 D K (d,ψ d)=0) :
    ∃ C δ : ℝ, 0<C ∧ 0<δ ∧ ∀ x, dist x p<δ →
      residual A0 D K (returnArgument (((a,r),x),τ ((a,r),x)),
        ψ (returnArgument (((a,r),x),τ ((a,r),x))))=0 ∧
      τ ((a,r),p)/2<τ ((a,r),x) ∧ τ ((a,r),x)<2*τ ((a,r),p) ∧
      ∀ t : UnitTime,
        dist (ψ (returnArgument (((a,r),x),τ ((a,r),x))) t)
          (ψ (returnArgument (((a,r),p),τ ((a,r),p))) t) ≤ C*dist x p := by
  let d : (ι → ℝ) → ReturnData (ι → ℝ) := fun x => ((a,r),x)
  let e : (ι → ℝ) → GenericShootingMap.FlowData (ι → ℝ) := fun x => returnArgument (d x,τ (d x))
  let g : (ι → ℝ) → ContinuousPath (ι → ℝ) := fun x => ψ (e x)
  have hd : ContDiffAt ℝ ⊤ d p := by fun_prop
  have ht : ContDiffAt ℝ ⊤ (fun x => τ (d x)) p := hτ.comp p hd
  have he : ContDiffAt ℝ ⊤ e p :=
    returnArgument_smooth.contDiffAt.comp p (hd.prodMk ht)
  have hg : ContDiffAt ℝ ⊤ g p := ContDiffAt.comp (f := e) (g := ψ) p hψ he
  let L := fderiv ℝ g p
  have hb := derivative_local_radial_bound g p L
    (hg.differentiableAt (by simp)).hasFDerivAt
  have hr := he.continuousAt.tendsto.eventually hres
  have htime : ∀ᶠ x in 𝓝 p,
      τ ((a,r),p)/2<τ (d x) ∧ τ (d x)<2*τ ((a,r),p) := by
    exact ht.continuousAt.tendsto.eventually
      (Ioo_mem_nhds (by dsimp [d]; linarith) (by dsimp [d]; linarith))
  have hall := hb.and (hr.and htime)
  obtain ⟨δ,hδ,hδbound⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨‖L‖+1,δ,by positivity,hδ,?_⟩
  intro x hx
  obtain ⟨hbound,hresx,hlo,hhi⟩ := hδbound hx
  refine ⟨hresx,hlo,hhi,?_⟩
  intro t
  have hh := (ContinuousMap.norm_coe_le_norm (g x-g p) t).trans hbound
  simpa only [dist_eq_norm,ContinuousMap.sub_apply,g,e,d] using hh

/-- Strict multipliers of the actual return derivative give an invariant
contracting-iterate neighborhood and uniform source-arc control. -/
theorem return_estimates (a r : ℝ) (p : ι → ℝ)
    (hτ : ContDiffAt ℝ ⊤ τ ((a,r),p))
    (hψ : ContDiffAt ℝ ⊤ ψ (returnArgument (((a,r),p),τ ((a,r),p))))
    (hT : 0<τ ((a,r),p)) (hp : returnPoint ψ τ ((a,r),p)=p)
    (hres : ∀ᶠ d in 𝓝 (returnArgument (((a,r),p),τ ((a,r),p))),
      residual A0 D K (d,ψ d)=0)
    {σ : Type*} [Fintype σ]
    (b : Module.Basis σ ℝ (ι → ℝ)) (eig : σ → ℝ)
    (he : ∀ i, (fderiv ℝ (fun x => returnPoint ψ τ ((a,r),x)) p) (b i)=eig i • b i)
    (heig : ∀ i, |eig i|<1) :
    ∃ N : ℕ, 0<N ∧ ∃ q C δ : ℝ, 0≤q ∧ q<1 ∧ 0<C ∧ 0<δ ∧
      (∀ x, dist x p<δ → ∀ n : ℕ,
        dist (((fun x => returnPoint ψ τ ((a,r),x))^[N])^[n] x) p ≤ q^n*dist x p ∧
        dist (((fun x => returnPoint ψ τ ((a,r),x))^[N])^[n] x) p<δ) ∧
      (∀ x, dist x p<δ →
        residual A0 D K (returnArgument (((a,r),x),τ ((a,r),x)),
          ψ (returnArgument (((a,r),x),τ ((a,r),x))))=0 ∧
        τ ((a,r),p)/2<τ ((a,r),x) ∧ τ ((a,r),x)<2*τ ((a,r),p) ∧
        ∀ t : UnitTime,
          dist (ψ (returnArgument (((a,r),x),τ ((a,r),x))) t)
            (ψ (returnArgument (((a,r),p),τ ((a,r),p))) t) ≤ C*dist x p) := by
  let P : (ι → ℝ) → (ι → ℝ) := fun x => returnPoint ψ τ ((a,r),x)
  have hs : ContDiffAt ℝ ⊤ P p :=
    (returnPoint_smooth ψ τ ((a,r),p) hτ hψ).comp p (by fun_prop)
  obtain ⟨N,hN,q,hq,hq1,δ₁,hδ₁,hbound⟩ :=
    RealEigenbasisContraction.eigenbasis_return_bound P p (fderiv ℝ P p) b eig hp
      (hs.differentiableAt (by simp)).hasFDerivAt he heig
  obtain ⟨C,δ₂,hC,hδ₂,harc⟩ := return_arc_control A0 D K ψ τ a r p hτ hψ hT hres
  refine ⟨N,hN,q,C,min δ₁ δ₂,hq,hq1,hC,lt_min hδ₁ hδ₂,?_,?_⟩
  · intro x hx n
    have hh := hbound x (hx.trans_le (min_le_left _ _)) n
    refine ⟨hh.1,?_⟩
    exact (hh.1.trans (mul_le_of_le_one_left dist_nonneg
      (pow_le_one₀ hq hq1.le))).trans_lt hx
  · intro x hx
    exact harc x (hx.trans_le (min_le_right _ _))

def returnStates (a r : ℝ) (x : ι → ℝ) (n : ℕ) : ι → ℝ :=
  (fun y => returnPoint ψ τ ((a,r),y))^[n] x

def returnTimes (a r : ℝ) (x : ι → ℝ) (n : ℕ) : ℝ := τ ((a,r),returnStates ψ τ a r x n)

def returnFlowData (a r : ℝ) (x : ι → ℝ) (n : ℕ) : GenericShootingMap.FlowData (ι → ℝ) :=
  ((a,(r,returnTimes ψ τ a r x n)),returnStates ψ τ a r x n)

def absoluteReturnArc (a r : ℝ) (x : ι → ℝ) (n : ℕ) (t : ℝ) : ι → ℝ :=
  GenericPathContinuation.pathContinuation A0.mulVecLin.toContinuousLinearMap
    D.mulVecLin.toContinuousLinearMap (GenericQuadraticTensor.pathField K)
    (returnFlowData ψ τ a r x n) (ψ (returnFlowData ψ τ a r x n))
    ((t-elapsed (returnTimes ψ τ a r x) n)/returnTimes ψ τ a r x n)

theorem absoluteReturnArc_initial (a r : ℝ) (x : ι → ℝ) (n : ℕ) :
    absoluteReturnArc A0 D K ψ τ a r x n (elapsed (returnTimes ψ τ a r x) n)=
      returnStates ψ τ a r x n := by
  simp [absoluteReturnArc,GenericPathContinuation.pathContinuation_initial,returnFlowData]

theorem absoluteReturnArc_endpoint (a r : ℝ) (x : ι → ℝ) (n : ℕ)
    (hT : returnTimes ψ τ a r x n ≠ 0)
    (hres : residual A0 D K (returnFlowData ψ τ a r x n,ψ (returnFlowData ψ τ a r x n))=0) :
    absoluteReturnArc A0 D K ψ τ a r x n (elapsed (returnTimes ψ τ a r x) (n+1))=
      returnStates ψ τ a r x (n+1) := by
  rw [absoluteReturnArc,elapsed_succ,add_sub_cancel_left,div_self hT]
  rw [← GenericPathContinuation.pathContinuation_eq _ _ _ _ _ hres (⟨1,by norm_num⟩:UnitTime)]
  simp only [returnStates,Function.iterate_succ_apply']
  rfl

theorem absoluteReturnArc_derivative (a r : ℝ) (x : ι → ℝ) (n : ℕ)
    (hT : 0<returnTimes ψ τ a r x n)
    (hres : residual A0 D K (returnFlowData ψ τ a r x n,ψ (returnFlowData ψ τ a r x n))=0)
    (t : ℝ) (ht : t ∈ Set.Icc (elapsed (returnTimes ψ τ a r x) n)
      (elapsed (returnTimes ψ τ a r x) (n+1))) :
    HasDerivAt (absoluteReturnArc A0 D K ψ τ a r x n)
      (rescaledField A0 D K a r (absoluteReturnArc A0 D K ψ τ a r x n t)) t := by
  let T := returnTimes ψ τ a r x n
  let S := elapsed (returnTimes ψ τ a r x) n
  have hs : (t-S)/T ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) hT.le
    · apply (div_le_one hT).mpr
      have hh := ht.2
      rw [elapsed_succ] at hh
      dsimp [S,T]
      linarith
  have hh := GenericPathContinuation.pathContinuation_solves A0.mulVecLin.toContinuousLinearMap
    D.mulVecLin.toContinuousLinearMap (GenericQuadraticTensor.field K)
    (GenericQuadraticTensor.pathField K) (GenericQuadraticTensor.pathField_apply K)
    (returnFlowData ψ τ a r x n) (ψ (returnFlowData ψ τ a r x n)) hres ((t-S)/T) hs
  have hd : HasDerivAt (fun s : ℝ => (s-S)/T) (1/T) t := by
    simpa using ((hasDerivAt_id t).sub_const S).div_const T
  have h := hh.scomp t hd
  simpa [absoluteReturnArc,returnFlowData,T,S,smul_smul,ne_of_gt hT] using h

def forwardReturnCurve (a r : ℝ) (x : ι → ℝ) (c : ℝ) (hc : 0<c)
    (hT : ∀ n, c≤returnTimes ψ τ a r x n) : ℝ → (ι → ℝ) :=
  ReturnArcConcatenation.curve (returnTimes ψ τ a r x) c hc hT
    (absoluteReturnArc A0 D K ψ τ a r x)

theorem forwardReturnCurve_initial (a r : ℝ) (x : ι → ℝ) (c : ℝ) (hc : 0<c)
    (hT : ∀ n, c≤returnTimes ψ τ a r x n) :
    forwardReturnCurve A0 D K ψ τ a r x c hc hT 0=x := by
  rw [forwardReturnCurve,ReturnArcConcatenation.curve_initial]
  simpa [returnStates] using absoluteReturnArc_initial A0 D K ψ τ a r x 0

/-- The actual residual-defined return arcs concatenate to a global forward
solution of the rescaled source under the stated non-Zeno and residual inputs. -/
theorem forwardReturnCurve_solves (a r : ℝ) (x : ι → ℝ) (c : ℝ) (hc : 0<c)
    (hT : ∀ n, c≤returnTimes ψ τ a r x n)
    (hres : ∀ n, residual A0 D K (returnFlowData ψ τ a r x n,ψ (returnFlowData ψ τ a r x n))=0)
    (t : ℝ) (ht : 0≤t) :
    HasDerivWithinAt (forwardReturnCurve A0 D K ψ τ a r x c hc hT)
      (rescaledField A0 D K a r (forwardReturnCurve A0 D K ψ τ a r x c hc hT t))
        (Set.Ici 0) t := by
  apply ReturnArcConcatenation.curve_source (returnTimes ψ τ a r x) c hc hT
    (absoluteReturnArc A0 D K ψ τ a r x) (rescaledField A0 D K a r) _ _ t ht
  · intro n
    rw [absoluteReturnArc_initial,absoluteReturnArc_endpoint A0 D K ψ τ a r x n
      (ne_of_gt (hc.trans_le (hT n))) (hres n)]
  · intro n s hs
    exact (absoluteReturnArc_derivative A0 D K ψ τ a r x n (hc.trans_le (hT n)) (hres n)
      s hs).hasDerivWithinAt

/-- Every physical time in the concatenated forward solution belongs to an
actual residual-defined source arc, at a normalized phase in [0,1]. -/
theorem forwardReturnCurve_on_arc (a r : ℝ) (x : ι → ℝ) (c : ℝ) (hc : 0<c)
    (hT : ∀ n, c≤returnTimes ψ τ a r x n)
    (hres : ∀ n, residual A0 D K (returnFlowData ψ τ a r x n,ψ (returnFlowData ψ τ a r x n))=0)
    (t : ℝ) (ht : 0≤t) :
    ∃ s : UnitTime, forwardReturnCurve A0 D K ψ τ a r x c hc hT t=
      ψ (returnFlowData ψ τ a r x (count (returnTimes ψ τ a r x) c hc hT t)) s := by
  let n := count (returnTimes ψ τ a r x) c hc hT t
  let S := elapsed (returnTimes ψ τ a r x) n
  let T := returnTimes ψ τ a r x n
  have hTp : 0<T := hc.trans_le (hT n)
  have hlo : S≤t := count_lower _ c hc hT t ht
  have hup : t<S+T := by simpa only [elapsed_succ] using count_upper _ c hc hT t
  have hs : (t-S)/T ∈ Set.Icc (0:ℝ) 1 := by
    exact ⟨div_nonneg (sub_nonneg.mpr hlo) hTp.le,
      (div_le_one hTp).mpr (by linarith)⟩
  refine ⟨⟨(t-S)/T,hs⟩,?_⟩
  exact (GenericPathContinuation.pathContinuation_eq _ _ _ _ _ (hres n) ⟨(t-S)/T,hs⟩).symm

/-- Uniformly small return errors control every physical time. -/
theorem forwardReturnCurve_tube (a r : ℝ) (x p : ι → ℝ) (u : ContinuousPath (ι → ℝ))
    (c C ε : ℝ) (hc : 0<c) (hC : 0≤C)
    (hT : ∀ n, c≤returnTimes ψ τ a r x n)
    (hres : ∀ n, residual A0 D K (returnFlowData ψ τ a r x n,ψ (returnFlowData ψ τ a r x n))=0)
    (harc : ∀ n s, dist (ψ (returnFlowData ψ τ a r x n) s) (u s) ≤
      C*dist (returnStates ψ τ a r x n) p)
    (hsmall : ∀ n, dist (returnStates ψ τ a r x n) p<ε/(C+1)) :
    ∀ t, 0≤t → ∃ s : UnitTime,
      dist (forwardReturnCurve A0 D K ψ τ a r x c hc hT t) (u s)<ε := by
  intro t ht
  obtain ⟨s,hs⟩ := forwardReturnCurve_on_arc A0 D K ψ τ a r x c hc hT hres t ht
  refine ⟨s,?_⟩
  rw [hs]
  have hh := (lt_div_iff₀ (show 0<C+1 by linarith)).mp
    (hsmall (count (returnTimes ψ τ a r x) c hc hT t))
  have hd := dist_nonneg (x := returnStates ψ τ a r x
    (count (returnTimes ψ τ a r x) c hc hT t)) (y := p)
  have ha := harc (count (returnTimes ψ τ a r x) c hc hT t) s
  nlinarith

/-- Convergence of every return and uniform control of the actual source arcs
give physical-time convergence of the distance to the exact orbit. -/
theorem forwardReturnCurve_orbit_attraction (a r : ℝ) (x p : ι → ℝ)
    (u : ContinuousPath (ι → ℝ)) (c C : ℝ) (hc : 0<c)
    (hT : ∀ n, c≤returnTimes ψ τ a r x n)
    (hres : ∀ n, residual A0 D K (returnFlowData ψ τ a r x n,ψ (returnFlowData ψ τ a r x n))=0)
    (hconv : Tendsto (returnStates ψ τ a r x) atTop (𝓝 p))
    (harc : ∀ n s, dist (ψ (returnFlowData ψ τ a r x n) s) (u s) ≤
      C*dist (returnStates ψ τ a r x n) p) :
    Tendsto (fun t => Metric.infDist (forwardReturnCurve A0 D K ψ τ a r x c hc hT t)
      (Set.range u)) atTop (𝓝 0) := by
  let n := count (returnTimes ψ τ a r x) c hc hT
  have hcount : Tendsto n atTop atTop := count_tendsto_atTop _ c hc hT
  have hz : Tendsto (fun t => C*dist (returnStates ψ τ a r x (n t)) p) atTop (𝓝 0) := by
    simpa using ((hconv.comp hcount).dist (tendsto_const_nhds (x := p))).const_mul C
  have hb : ∀ᶠ t in atTop, Metric.infDist (forwardReturnCurve A0 D K ψ τ a r x c hc hT t)
      (Set.range u) ≤ C*dist (returnStates ψ τ a r x (n t)) p := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    obtain ⟨s,hs⟩ := forwardReturnCurve_on_arc A0 D K ψ τ a r x c hc hT hres t ht
    rw [hs]
    exact (Metric.infDist_le_dist_of_mem (Set.mem_range_self s)).trans (harc (n t) s)
  exact squeeze_zero' (Eventually.of_forall (fun _ => Metric.infDist_nonneg)) hb hz

/-- Local attraction in rescaled coordinates at an actual fixed return point:
global forward solutions of the actual rescaled field, arbitrarily small
tubes about the exact return arc, and convergence of the distance to it. -/
theorem local_rescaled_attraction (a r : ℝ) (p : ι → ℝ)
    (hτ : ContDiffAt ℝ ⊤ τ ((a,r),p))
    (hψ : ContDiffAt ℝ ⊤ ψ (returnArgument (((a,r),p),τ ((a,r),p))))
    (hT : 0<τ ((a,r),p)) (hp : returnPoint ψ τ ((a,r),p)=p)
    (hres : ∀ᶠ d in 𝓝 (returnArgument (((a,r),p),τ ((a,r),p))),
      residual A0 D K (d,ψ d)=0)
    {σ : Type*} [Fintype σ]
    (b : Module.Basis σ ℝ (ι → ℝ)) (eig : σ → ℝ)
    (he : ∀ i, (fderiv ℝ (fun x => returnPoint ψ τ ((a,r),x)) p) (b i)=eig i • b i)
    (heig : ∀ i, |eig i|<1) :
    ∀ ε>0, ∃ η>0, ∀ x, dist x p<η → ∃ y : ℝ → (ι → ℝ),
      y 0=x ∧
      (∀ t, 0≤t → HasDerivWithinAt y (rescaledField A0 D K a r (y t)) (Set.Ici 0) t) ∧
      (∀ t, 0≤t → ∃ s : UnitTime,
        dist (y t) (ψ (returnArgument (((a,r),p),τ ((a,r),p))) s)<ε) ∧
      Tendsto (fun t => Metric.infDist (y t)
        (Set.range (ψ (returnArgument (((a,r),p),τ ((a,r),p)))))) atTop (𝓝 0) := by
  intro ε hε
  let P : (ι → ℝ) → (ι → ℝ) := fun x => returnPoint ψ τ ((a,r),x)
  let u := ψ (returnArgument (((a,r),p),τ ((a,r),p)))
  have hs : ContinuousAt P p :=
    ((returnPoint_smooth ψ τ ((a,r),p) hτ hψ).comp p (by fun_prop)).continuousAt
  obtain ⟨N,hN,q,C,δ,hq,hq1,hC,hδ,hblock,harc⟩ :=
    return_estimates A0 D K ψ τ a r p hτ hψ hT hp hres b eig he heig
  have hρ : 0 < min δ (ε/(C+1)) := lt_min hδ (div_pos hε (by linarith))
  obtain ⟨η,hη,_,hcontrol⟩ := ReturnIterateControl.all_iterates_control P p hp N hN
    (fun j => hs.iterate hp j.val) q δ hq hq1 hδ
    (fun x hx n => (hblock x hx n).1) (min δ (ε/(C+1))) hρ
  refine ⟨η,hη,?_⟩
  intro x hx
  obtain ⟨hsmall,hconv⟩ := hcontrol x hx
  have hall (n : ℕ) := harc (P^[n] x) ((hsmall n).trans_le (min_le_left _ _))
  let c := τ ((a,r),p)/2
  have hc : 0<c := half_pos hT
  have htimes : ∀ n, c≤returnTimes ψ τ a r x n := fun n => (hall n).2.1.le
  have hresidual : ∀ n,
      residual A0 D K (returnFlowData ψ τ a r x n,ψ (returnFlowData ψ τ a r x n))=0 :=
    fun n => (hall n).1
  have hdist : ∀ n s, dist (ψ (returnFlowData ψ τ a r x n) s) (u s) ≤
      C*dist (returnStates ψ τ a r x n) p := fun n => (hall n).2.2.2
  refine ⟨forwardReturnCurve A0 D K ψ τ a r x c hc htimes,
    forwardReturnCurve_initial A0 D K ψ τ a r x c hc htimes,
    forwardReturnCurve_solves A0 D K ψ τ a r x c hc htimes hresidual,?_,?_⟩
  · exact forwardReturnCurve_tube A0 D K ψ τ a r x p u c C ε hc hC.le htimes hresidual hdist
      (fun n => (hsmall n).trans_le (min_le_right _ _))
  · exact forwardReturnCurve_orbit_attraction A0 D K ψ τ a r x p u c C hc
      htimes hresidual hconv hdist

/-- The rescaled field is the literal centered field after amplitude scaling. -/
theorem rescaledField_eq (a r : ℝ) (y : ι → ℝ) :
    rescaledField A0 D K a r y=GenericQuadraticDynamics.rescaledField A0 D K a r y := by
  simp only [rescaledField,GenericAffinePathExistence.affineField,
    GenericQuadraticDynamics.rescaledField,← GenericShootingInvertibility.matrix_operator_affine]
  rfl

end
end ThreeSitePhosphorylation.GenericLocalAttraction
