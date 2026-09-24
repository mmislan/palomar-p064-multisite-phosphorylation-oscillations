import proofs.ThreeSitePhosphorylation.GenericReturnLinearization
import proofs.ThreeSitePhosphorylation.NearbyEigenbasis
import proofs.ThreeSitePhosphorylation.AttractingRadialMultiplier
import proofs.ThreeSitePhosphorylation.GenericClosedBranchCurvature
import proofs.ThreeSitePhosphorylation.GenericQuadraticClosedPaths

/-! Strict multiplier bounds for the derivative of the actual residual-defined
return map along the actual closed quadratic branch, for an arbitrary finite
coordinate type. No return eigenvectors, branch identities or multiplier
signs are supplied as hypotheses. -/
namespace ThreeSitePhosphorylation.GenericBranchMultipliers
noncomputable section
open scoped Topology
open GenericReturnIFT GenericClosedPaths GenericReturnContracts GenericReturnLinearization

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

omit [DecidableEq ι] [Fintype σ] in
/-- A normalized critical left eigenfunctional is the critical dual coordinate
of a full simple complex eigenbasis. -/
theorem left_eq_coord (A : Matrix ι ι ℝ) (w : ℝ) (hw : 0<w) (roots : σ → ℝ)
    (hn : ∀ i, roots i<0) (b : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ))
    (he : ∀ i, (GenericComplexification.complexMatrix A).mulVec (b i)=
      GenericPeriodicKernel.spectralValues roots w i • b i)
    (p : (ι → ℂ) →ₗ[ℂ] ℂ)
    (hleft : ∀ z, p ((GenericComplexification.complexMatrix A).mulVec z)=(Complex.I*(w:ℂ))*p z)
    (hnorm : p (b (Sum.inr 0))=1) : p=b.coord (Sum.inr 0) := by
  apply b.ext
  intro j
  by_cases hj : j=Sum.inr 0
  · subst hj
    simp [hnorm,Module.Basis.coord_apply]
  · have hne : GenericPeriodicKernel.spectralValues roots w j ≠ Complex.I*(w:ℂ) := by
      cases j with
      | inl i =>
        intro h
        have hr := congrArg Complex.re h
        simp [GenericPeriodicKernel.spectralValues] at hr
        linarith [hn i]
      | inr k =>
        fin_cases k
        · exact (hj rfl).elim
        · intro h
          have hi := congrArg Complex.im h
          simp [GenericPeriodicKernel.spectralValues] at hi
          linarith
    have hh := hleft (b j)
    rw [he j,map_smul,smul_eq_mul] at hh
    have hz : p (b j)=0 :=
      (mul_eq_zero.mp (show (GenericPeriodicKernel.spectralValues roots w j-Complex.I*(w:ℂ))*
        p (b j)=0 by linear_combination hh)).resolve_left (sub_ne_zero.mpr hne)
    rw [hz]
    simp [Module.Basis.coord_apply,hj]

theorem eventually_negative_right_of_negative_derivative (f : ℝ → ℝ) (d : ℝ)
    (hd : HasDerivAt f d 0) (hzero : f 0=0) (hneg : d<0) :
    ∀ᶠ a in 𝓝[>] (0:ℝ), f a<0 := by
  have hh := hd.tendsto_slope_zero_right.eventually (isOpen_Iio.mem_nhds hneg)
  filter_upwards [hh,self_mem_nhdsWithin] with a ha hpos
  simp only [zero_add,hzero,sub_zero,smul_eq_mul] at ha
  exact neg_of_mul_neg_right ha (inv_pos.mpr hpos).le

omit [Fintype σ] [DecidableEq σ] in
/-- Actual negative curvature and the actual vanishing first derivative give
a negative kinetic-parameter slope for small positive amplitudes. -/
theorem closed_branch_slope_negative_right (A0 D : Matrix ι ι ℝ)
    (K : ℝ → GenericQuadraticTensor.Tensor ι)
    (hK : ∀ i j k, ContDiff ℝ ⊤ (fun s => K s i j k)) (r w : ℝ) (hw : 0<w) (v : ι → ℂ)
    (hv : (GenericComplexification.complexMatrix (A0+r • D)).mulVec v=(Complex.I*(w:ℂ)) • v)
    (C : ClosedPathFamily A0 D (GenericQuadraticTensor.pathField K) r w v)
    (hcross : (C.left ((GenericComplexification.complexMatrix D).mulVec v)).re<0)
    (hcurv : deriv (deriv (fun a => (C.parameters a).2.re)) 0<0) :
    ∀ᶠ a in 𝓝[>] (0:ℝ), deriv (kineticParameter C) a<0 := by
  have hR : ContDiffAt ℝ ⊤ (fun a => (C.parameters a).2.re) 0 :=
    ContDiffAt.comp (f := fun a => (C.parameters a).2) (g := Complex.reCLM) 0
      Complex.reCLM.contDiff.contDiffAt C.parameters_smooth.snd
  have h2 : HasDerivAt (deriv (fun a => (C.parameters a).2.re))
      (deriv (deriv (fun a => (C.parameters a).2.re)) 0) 0 :=
    ((hR.derivWithin (m := 1) (by simp)).differentiableAt (by norm_num)).hasDerivAt
  have h0 := (GenericClosedBranchFirstVariation.closed_branch_parameter_derivatives A0 D K hK r w
    hw v hv C hcross).1.deriv
  exact eventually_negative_right_of_negative_derivative _ _ h2 h0 hcurv

/-- Strict multiplier bounds for the actual return derivative along the actual
closed branch. The negative slope input is supplied by
`closed_branch_slope_negative_right` in the assembled theorem below. -/
theorem closed_branch_strict_return_multipliers
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
    (C : ClosedPathFamily A0 D (GenericQuadraticTensor.pathField K) r w (b (Sum.inr 0)))
    (R : ReturnFlow C)
    (hslope : ∀ᶠ a in 𝓝[>] (0:ℝ), deriv (kineticParameter C) a<0) :
    ∀ᶠ a in 𝓝[>] (0:ℝ), ∃ c : Module.Basis (σ ⊕ Fin 2) ℝ (ι → ℝ),
      ∃ eig : σ ⊕ Fin 2 → ℝ,
        (∀ i, branchDerivative R a (c i)=eig i • c i) ∧ ∀ i, |eig i|<1 := by
  have hev : (GenericComplexification.complexMatrix (A0+r • D)).mulVec (b (Sum.inr 0))=
      (Complex.I*(w:ℂ)) • b (Sum.inr 0) := by
    simpa [GenericPeriodicKernel.spectralValues] using he (Sum.inr 0)
  have hleq := left_eq_coord (A0+r • D) w hw roots hn b he C.left C.left_eigen C.left_normalized
  obtain ⟨c,hcv,hce,hinjv⟩ := GenericReturnBaseEigenbasis.actual_return_base_eigenbasis A0 D _ r w
    hw roots hinj hn b hreal hpair he C.left C.left_eigen C.left_normalized R.ψ R.τ
    R.ψ_smooth R.τ_smooth R.τ_zero R.residual R.phase
  have hcR : c=GenericRealCriticalBasis.realBasis b hreal hpair :=
    Module.Basis.eq_of_apply_eq (fun i => by rw [hcv i,GenericRealCriticalBasis.realBasis_apply])
  have hcoord : (c.coord (Sum.inr 0)).toContinuousLinearMap=
      (2:ℝ) • Complex.reCLM.comp (GenericRealCriticalBasis.complexCoordinate b (Sum.inr 0)) := by
    rw [hcR,GenericRealCriticalBasis.realBasis_coordinate]
    rfl
  have hce0 : ∀ i, branchDerivative R 0 (c i)=
      GenericReturnBaseEigenbasis.returnValues (2*Real.pi/w) roots i • c i := by
    intro i
    rw [branchDerivative_zero]
    exact hce i
  obtain ⟨μ,vv,hμ,_,hμ0,hv0,hl,hnear⟩ :=
    NearbyEigenbasis.smooth_eigenbasis (branchDerivative R) (branchDerivative_smooth R) c
      (GenericReturnBaseEigenbasis.returnValues (2*Real.pi/w) roots) hce0 hinjv
  let i₀ : σ ⊕ Fin 2 := Sum.inr 0
  let l : ℝ → (ι → ℝ) →L[ℝ] ℝ := fun a => NearbyEigenbasis.inverseCoordinate c (vv a) i₀
  have hl0 : l 0=(c.coord i₀).toContinuousLinearMap := by
    dsimp only [l]
    rw [hv0,NearbyEigenbasis.inverseCoordinate_self]
  have hp0 : 0<l 0 (radialVector C 0) := by
    have hc0 : c i₀=GenericComplexification.realPart (b (Sum.inr 0)) := hcv i₀
    rw [hl0,radialVector_zero,← hc0]
    simp [Module.Basis.coord_apply]
  have hn0 : l 0 (parameterVector R 0)<0 := by
    have hh := R.parameter_pairing_negative hw hev (by rw [hleq]; exact hcross)
    rw [hleq] at hh
    rw [hl0,hcoord,parameterVector_zero]
    exact hh
  have hμrad : μ 0 i₀=1 := by rw [hμ0]; rfl
  have hleft : ∀ᶠ a in 𝓝 (0:ℝ), ∀ x,
      l a (branchDerivative R a x)=μ a i₀*l a x := by
    filter_upwards [hnear] with a ha
    obtain ⟨_,_,_,hh⟩ := ha.2
    exact hh i₀
  have hrad := AttractingWitness.radial_multiplier_eventually_abs_lt_one (branchDerivative R)
    (radialVector C) (parameterVector R) l (fun a => μ a i₀) (deriv (kineticParameter C))
    (radialVector_smooth C).continuousAt (parameterVector_smooth R).continuousAt
    (hl i₀) (hμ i₀).continuousAt hμrad hp0 hn0 (radial_vector_identity R hK) hleft hslope
  have hother (i : σ ⊕ Fin 2) (hi : i ≠ i₀) : |μ 0 i|<1 := by
    rw [hμ0]
    exact GenericReturnBaseEigenbasis.nonradial_value_abs_lt_one (2*Real.pi/w) (by positivity)
      roots hn i hi
  have hall := AttractingWitness.all_multipliers_eventually_abs_lt_one i₀ μ
    (fun i => (hμ i).continuousAt) hother hrad
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,hall] with a ha hbounds
  obtain ⟨ca,hca,_,_⟩ := ha.2
  refine ⟨ca,μ a,?_,hbounds⟩
  intro i
  rw [hca]
  exact (ha.1 i).1

/-- Source-level strict multipliers: from the actual quadratic tensor, full
simple source basis with real stable columns and conjugate critical pair,
negative crossing and negative normalized branch coefficient, construct the
actual closed branch and its actual return flow with strict multipliers. -/
theorem source_strict_return_branch
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
      ∃ R : ReturnFlow C,
        deriv (deriv (fun a => (C.parameters a).2.re)) 0<0 ∧
        (∀ᶠ a in 𝓝[>] (0:ℝ), deriv (kineticParameter C) a<0) ∧
        ∀ᶠ a in 𝓝[>] (0:ℝ), ∃ c : Module.Basis (σ ⊕ Fin 2) ℝ (ι → ℝ),
          ∃ eig : σ ⊕ Fin 2 → ℝ,
            (∀ i, branchDerivative R a (c i)=eig i • c i) ∧ ∀ i, |eig i|<1 := by
  have hev : (GenericComplexification.complexMatrix (A0+r • D)).mulVec (b (Sum.inr 0))=
      (Complex.I*(w:ℂ)) • b (Sum.inr 0) := by
    simpa [GenericPeriodicKernel.spectralValues] using he (Sum.inr 0)
  obtain ⟨C⟩ := GenericQuadraticClosedPaths.closed_path_family_exists A0 D K hK r w hw roots hn b
    he hcross
  obtain ⟨R⟩ := returnFlow_exists hK hw hev C
  have hleq := left_eq_coord (A0+r • D) w hw roots hn b he C.left C.left_eigen C.left_normalized
  have hcrossC : (C.left ((GenericComplexification.complexMatrix D).mulVec (b (Sum.inr 0)))).re<0 := by
    rw [hleq]
    exact hcross
  have hGC : (GenericClosedBranchCurvature.branchCoefficient C h11 h20).re<0 := by
    unfold GenericClosedBranchCurvature.branchCoefficient
    rw [hleq]
    exact hG
  have hcurv := GenericClosedBranchCurvature.closed_branch_parameter_second_derivative_negative C
    hK hw hev hcrossC hsym hA hS h11 h20 h11eq h20eq hGC
  have hslope := closed_branch_slope_negative_right A0 D K hK r w hw _ hev C hcrossC hcurv
  exact ⟨C,R,hcurv,hslope,closed_branch_strict_return_multipliers A0 D K hK r w hw roots hinj hn
    b hreal hpair he hcross C R hslope⟩

end
end ThreeSitePhosphorylation.GenericBranchMultipliers
