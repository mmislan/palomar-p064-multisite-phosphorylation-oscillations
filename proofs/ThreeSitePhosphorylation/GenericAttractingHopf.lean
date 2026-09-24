import proofs.ThreeSitePhosphorylation.GenericAttractingFamily

/-! Source-level dimension-independent attracting Hopf theorem.

Inputs are exactly the actual source data consumed by the all-n induction:
the affine matrix `A0+rD`, a smooth quadratic tensor `K`, a full simple complex
eigenbasis with conjugation-fixed stable columns for injective negative roots
and a conjugate critical pair `±iω`, negative crossing, the two resolvent
equations and the negative normalized branch coefficient. The conclusion
PRODUCES the selected family: nonconstant periodic solutions of the literal
centered field `(A0+rD)z+Q_r(z)`, orbitally asymptotically stable from an open
neighborhood of the whole orbit (global forward existence, Lyapunov tubes,
convergence of the distance, forward uniqueness), on the supercritical side,
with period limit `2π/ω` and uniform shrinking to the equilibrium. -/
namespace ThreeSitePhosphorylation.GenericAttractingHopf
noncomputable section
open Filter
open scoped Topology Pointwise
open GenericReturnIFT GenericClosedPaths GenericReturnContracts GenericReturnLinearization
open GenericLocalAttraction GenericWholeOrbit GenericAttractingFamily

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
variable {A0 D : Matrix ι ι ℝ} {K : ℝ → GenericQuadraticTensor.Tensor ι}
variable {r w : ℝ} {v : ι → ℂ}

omit [Fintype σ] [DecidableEq σ] in
theorem parameters_limits (C : ClosedPathFamily A0 D (GenericQuadraticTensor.pathField K) r w v) :
    Tendsto (fun a => (C.parameters a).2.re) (𝓝 0) (𝓝 r) ∧
    Tendsto (fun a => (C.parameters a).2.im) (𝓝 0) (𝓝 (2*Real.pi/w)) := by
  have hc := C.parameters_smooth.continuousAt.snd
  have h0 : (C.parameters 0).2=(r:ℂ)+Complex.I*((2*Real.pi/w:ℝ):ℂ) := by
    rw [C.parameters_zero]
  constructor
  · have hh := (Complex.continuous_re.continuousAt.comp hc).tendsto
    simpa [Function.comp_def,h0] using hh
  · have hh := (Complex.continuous_im.continuousAt.comp hc).tendsto
    simpa [Function.comp_def,h0] using hh

omit [Fintype σ] [DecidableEq σ] in
/-- The actual rescaled velocity at the branch initial point is nonzero for
small amplitudes: at zero amplitude it is `(A0+rD)Re v=-ω Im v≠0`. -/
theorem velocity_nonzero (hK : ∀ i j k, ContDiff ℝ ⊤ (fun s => K s i j k)) (hw : 0<w)
    (he : (GenericComplexification.complexMatrix (A0+r • D)).mulVec v=(Complex.I*(w:ℂ)) • v)
    (C : ClosedPathFamily A0 D (GenericQuadraticTensor.pathField K) r w v) :
    ∀ᶠ a in 𝓝 (0:ℝ), rescaledField A0 D K a (C.parameters a).2.re (C.parameters a).1 ≠ 0 := by
  have hv : v ≠ 0 := by
    intro h
    have hh := congrArg (fun x => C.left x) h
    simp only [map_zero,C.left_normalized] at hh
    exact one_ne_zero hh
  have him : GenericComplexification.imagPart v ≠ 0 := by
    intro h
    exact hv (GenericComplexification.real_vector_imaginary_eigen_zero (A0+r • D) w
      (ne_of_gt hw) v h he)
  have h0 : rescaledField A0 D K 0 r (GenericComplexification.realPart v) ≠ 0 := by
    rw [rescaledField_eq]
    simp only [GenericQuadraticDynamics.rescaledField,zero_smul,add_zero,
      (GenericComplexification.source_eigen_real_imag (A0+r • D) w v he).1]
    intro h
    exact him ((smul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr (ne_of_gt hw)))
  have hF : Continuous (fun p : (ℝ × ℝ) × (ι → ℝ) =>
      GenericAffinePathExistence.affineField A0.mulVecLin.toContinuousLinearMap
        D.mulVecLin.toContinuousLinearMap (GenericQuadraticTensor.field K) p.1 p.2) := by
    exact (GenericAffinePathExistence.affineField_smooth A0.mulVecLin.toContinuousLinearMap
      D.mulVecLin.toContinuousLinearMap (GenericQuadraticTensor.field K)
      (GenericQuadraticTensor.field_smooth K hK)).continuous
  have hc := C.parameters_smooth.continuousAt
  have hz : ContinuousAt (fun a : ℝ => ((a,(C.parameters a).2.re),(C.parameters a).1)) 0 :=
    (continuousAt_id.prodMk (Complex.continuous_re.continuousAt.comp hc.snd)).prodMk hc.fst
  have hcomp := hF.continuousAt.comp hz
  have hval : (fun a : ℝ => rescaledField A0 D K a (C.parameters a).2.re (C.parameters a).1) 0=
      rescaledField A0 D K 0 r (GenericComplexification.realPart v) := by
    simp [C.parameters_zero]
  have ht : Tendsto (fun a : ℝ => rescaledField A0 D K a (C.parameters a).2.re (C.parameters a).1)
      (𝓝 0) (𝓝 (rescaledField A0 D K 0 r (GenericComplexification.realPart v))) := by
    rw [← hval]
    exact hcomp.tendsto
  exact ht.eventually_ne h0

omit [Fintype σ] [DecidableEq σ] in
theorem periodicOrbit_nonconstant
    (C : ClosedPathFamily A0 D (GenericQuadraticTensor.pathField K) r w v)
    (a : ℝ) (ha : a ≠ 0) (hT : 0<(C.parameters a).2.im)
    (hres : residual A0 D K (GenericShootingMap.shootingArgument (a,C.parameters a),C.paths a)=0)
    (hclosed : C.paths a ⟨1,by norm_num⟩=(C.parameters a).1)
    (hvel : rescaledField A0 D K a (C.parameters a).2.re (C.parameters a).1 ≠ 0) :
    ∃ t, periodicOrbit C a t ≠ periodicOrbit C a 0 := by
  obtain ⟨_,_,hd,h0⟩ := periodicOrbit_properties C a hT hres hclosed
  by_contra h
  push Not at h
  have hc : HasDerivAt (periodicOrbit C a) 0 0 := by
    have heq : periodicOrbit C a=(fun _ => periodicOrbit C a 0) := funext h
    rw [heq]
    exact hasDerivAt_const _ _
  have hz := (hd 0).unique hc
  rw [h0,GenericQuadraticDynamics.field_scaling,← rescaledField_eq] at hz
  exact hvel ((smul_eq_zero.mp hz).resolve_left ha)

omit [Fintype σ] [DecidableEq σ] in
/-- The physical orbits shrink uniformly to the equilibrium `z=0`. -/
theorem periodicOrbit_shrinks
    (C : ClosedPathFamily A0 D (GenericQuadraticTensor.pathField K) r w v) (hw : 0<w) :
    ∀ ε>0, ∀ᶠ a in 𝓝 (0:ℝ), ∀ t, ‖periodicOrbit C a t‖<ε := by
  intro ε hε
  have hP := C.paths_smooth.continuousAt
  have hbound : ∀ᶠ a in 𝓝 (0:ℝ), ‖C.paths a‖<‖C.paths 0‖+1 := by
    have ht := (continuous_norm.continuousAt.comp hP).tendsto
    exact ht.eventually (Iio_mem_nhds (by simp))
  have hT := (parameters_limits C).2.eventually (Ioi_mem_nhds (show (0:ℝ)<2*Real.pi/w by positivity))
  have hM : 0<‖C.paths 0‖+1 := by positivity
  have hsmall : ∀ᶠ a in 𝓝 (0:ℝ), |a| * (‖C.paths 0‖+1)<ε := by
    have ht : Tendsto (fun a : ℝ => |a| * (‖C.paths 0‖+1)) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0:ℝ)).mul_const (‖C.paths 0‖+1)
    exact ht.eventually (Iio_mem_nhds hε)
  filter_upwards [hbound,hT,hsmall,C.residual,C.closed] with a hb hTa hs hres hcl t
  obtain ⟨hr,_,_,_⟩ := periodicOrbit_properties C a hTa hres hcl
  have hm : periodicOrbit C a t ∈ a • Set.range (C.paths a) := by
    rw [← hr]
    exact Set.mem_range_self t
  obtain ⟨y,⟨s,rfl⟩,hy⟩ := hm
  rw [← hy,norm_smul,Real.norm_eq_abs]
  calc |a| * ‖C.paths a s‖ ≤ |a| * ‖C.paths a‖ :=
        mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm _ s) (abs_nonneg a)
    _ ≤ |a| * (‖C.paths 0‖+1) := mul_le_mul_of_nonneg_left hb.le (abs_nonneg a)
    _ < ε := hs

omit [Fintype σ] [DecidableEq σ] in
/-- Negative slope on the right gives the supercritical direction `r(a)<r`. -/
theorem kinetic_below_right
    (C : ClosedPathFamily A0 D (GenericQuadraticTensor.pathField K) r w v)
    (hslope : ∀ᶠ a in 𝓝[>] (0:ℝ), deriv (kineticParameter C) a<0) :
    ∀ᶠ a in 𝓝[>] (0:ℝ), kineticParameter C a<r := by
  have hR : ContDiffAt ℝ ⊤ (kineticParameter C) 0 :=
    ContDiffAt.comp (f := fun a => (C.parameters a).2) (g := Complex.reCLM) 0
      Complex.reCLM.contDiff.contDiffAt C.parameters_smooth.snd
  have hc : ∀ᶠ a in 𝓝 (0:ℝ), ContinuousAt (kineticParameter C) a :=
    ((hR.of_le (show (1:WithTop ℕ∞) ≤ ⊤ by simp)).eventually (by simp)).mono
      (fun _ ha => ha.continuousAt)
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hc
  obtain ⟨δ,hδ,hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hslope
  let m := min δ ε/2
  have hm : 0 < m := half_pos (lt_min hδ hε)
  have hmδ : m < δ := by have := min_le_left δ ε; dsimp [m]; linarith [lt_min hδ hε]
  have hmε : m < ε := by have := min_le_right δ ε; dsimp [m]; linarith [lt_min hδ hε]
  have hcont : ContinuousOn (kineticParameter C) (Set.Icc 0 m) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply hball
    rw [Real.dist_eq,sub_zero,abs_of_nonneg hx.1]
    exact lt_of_le_of_lt hx.2 hmε
  have hanti : StrictAntiOn (kineticParameter C) (Set.Icc 0 m) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 m) hcont
    intro x hx
    rw [interior_Icc] at hx
    exact hsub ⟨hx.1,lt_trans hx.2 hmδ⟩
  have h0 : kineticParameter C 0=r := by simp [kineticParameter,C.parameters_zero]
  filter_upwards [Ioo_mem_nhdsGT hm] with a ha
  have hh := hanti ⟨le_rfl,hm.le⟩ ⟨ha.1.le,ha.2.le⟩ ha.1
  rwa [h0] at hh

/-- **Dimension-independent attracting Hopf family.** -/
theorem attracting_hopf_family
    (A0 D : Matrix ι ι ℝ) (K : ℝ → GenericQuadraticTensor.Tensor ι)
    (hK : ∀ i j k, ContDiff ℝ ⊤ (fun s => K s i j k))
    (r w : ℝ) (hw : 0<w) (roots : σ → ℝ) (hinj : Function.Injective roots)
    (hn : ∀ i, roots i<0) (b : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ))
    (hreal : ∀ i : σ, GenericComplexification.conjugateVector (b (Sum.inl i))=b (Sum.inl i))
    (hpair : b (Sum.inr 1)=GenericComplexification.conjugateVector (b (Sum.inr 0)))
    (he : ∀ i, (GenericComplexification.complexMatrix (A0+r • D)).mulVec (b i)=
      GenericPeriodicKernel.spectralValues roots w i • b i)
    (hcross : (b.coord (Sum.inr 0)
      ((GenericComplexification.complexMatrix D).mulVec (b (Sum.inr 0)))).re<0)
    (hsym : ∀ i j k, K r i j k=K r i k j)
    (hA : Function.Injective (GenericComplexification.complexMatrix (A0+r • D)).mulVecLin)
    (hS : Function.Injective ((2*Complex.I*(w:ℂ)) •
      (LinearMap.id : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))-
        (GenericComplexification.complexMatrix (A0+r • D)).mulVecLin))
    (h11 h20 : ι → ℂ)
    (h11eq : (GenericComplexification.complexMatrix (A0+r • D)).mulVec h11=
      GenericTensorBilinear.complexBilinear (K r) (b (Sum.inr 0))
        (GenericComplexification.conjugateVector (b (Sum.inr 0))))
    (h20eq : (2*Complex.I*(w:ℂ)) • h20-
      (GenericComplexification.complexMatrix (A0+r • D)).mulVec h20=
        GenericTensorBilinear.complexBilinear (K r) (b (Sum.inr 0)) (b (Sum.inr 0)))
    (hG : (-2*b.coord (Sum.inr 0) (GenericTensorBilinear.complexBilinear (K r)
        (b (Sum.inr 0)) h11)+
      b.coord (Sum.inr 0) (GenericTensorBilinear.complexBilinear (K r)
        (GenericComplexification.conjugateVector (b (Sum.inr 0))) h20)).re<0) :
    ∃ C : ClosedPathFamily A0 D (GenericQuadraticTensor.pathField K) r w (b (Sum.inr 0)),
      Tendsto (fun a => (C.parameters a).2.re) (𝓝 0) (𝓝 r) ∧
      Tendsto (fun a => (C.parameters a).2.im) (𝓝 0) (𝓝 (2*Real.pi/w)) ∧
      (∀ ε>0, ∀ᶠ a in 𝓝 (0:ℝ), ∀ t, ‖periodicOrbit C a t‖<ε) ∧
      ∀ᶠ a in 𝓝[>] (0:ℝ),
        (C.parameters a).2.re<r ∧ 0<(C.parameters a).2.im ∧
        Function.Periodic (periodicOrbit C a) (C.parameters a).2.im ∧
        (∀ t, HasDerivAt (periodicOrbit C a)
          (GenericQuadraticDynamics.field A0 D K (C.parameters a).2.re (periodicOrbit C a t)) t) ∧
        (∃ t, periodicOrbit C a t ≠ periodicOrbit C a 0) ∧
        OrbitalAttraction (GenericQuadraticDynamics.field A0 D K (C.parameters a).2.re)
          (Set.range (periodicOrbit C a)) := by
  obtain ⟨C,R,_,hslope,hstrict⟩ := GenericBranchMultipliers.source_strict_return_branch A0 D K hK
    r w hw roots hinj hn b hreal hpair he hcross hsym hA hS h11 h20 h11eq h20eq hG
  have hev : (GenericComplexification.complexMatrix (A0+r • D)).mulVec (b (Sum.inr 0))=
      (Complex.I*(w:ℂ)) • b (Sum.inr 0) := by
    simpa [GenericPeriodicKernel.spectralValues] using he (Sum.inr 0)
  have hattr := closed_branch_rescaled_orbital_attraction hK hw R hstrict
  have hT := (parameters_limits C).2.eventually (Ioi_mem_nhds (show (0:ℝ)<2*Real.pi/w by positivity))
  refine ⟨C,(parameters_limits C).1,(parameters_limits C).2,periodicOrbit_shrinks C hw,?_⟩
  filter_upwards [hattr,kinetic_below_right C hslope,hT.filter_mono nhdsWithin_le_nhds,
    C.residual.filter_mono nhdsWithin_le_nhds,C.closed.filter_mono nhdsWithin_le_nhds,
    (velocity_nonzero hK hw hev C).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin]
    with a hat hbelow hTa hres hcl hvel ha
  have ha0 : a ≠ 0 := ne_of_gt ha
  obtain ⟨hrange,hper,hdyn,_⟩ := periodicOrbit_properties C a hTa hres hcl
  refine ⟨hbelow,hTa,hper,hdyn,periodicOrbit_nonconstant C a ha0 hTa hres hcl hvel,?_⟩
  rw [hrange]
  exact scale_orbital_attraction a _ ha0 _ hat

end
end ThreeSitePhosphorylation.GenericAttractingHopf
