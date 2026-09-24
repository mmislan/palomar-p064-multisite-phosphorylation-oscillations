import proofs.ThreeSitePhosphorylation.AddedSiteZeroLoadBasis
import proofs.ThreeSitePhosphorylation.ComplexNearbyEigenbasis
import proofs.ThreeSitePhosphorylation.RealEigenpairPersistence
import proofs.ThreeSitePhosphorylation.RealEigenfunctional
import proofs.ThreeSitePhosphorylation.CriticalParameterCurve

/-! Continuation of the full spectral invariant of the actual loaded
added-site source in the two real parameters (load, kinetic parameter),
and the critical kinetic curve through the parent critical point.
The same continued branches are used throughout: stable branches remain
real, distinct and negative, the critical pair remains conjugate, and the
actual kinetic crossing stays negative. -/
namespace ThreeSitePhosphorylation.AddedSiteCriticalContinuation
noncomputable section
open Filter
open scoped Topology
open PhosphorylationSharpness MultisiteChart MultisiteSource MultisiteCoordinates
open MultisiteTensor ScaledJointSource ScaledNormalSpectrum
open GenericComplexification AddedSiteSourceMatrix CriticalSpectrum AddedSiteZeroLoadBasis
set_option maxHeartbeats 1000000

section Matrices
variable {ι : Type*} [Fintype ι]

/-- Complexified matrix action, linear in the real matrix entries. -/
def matrixOp : (ι → ι → ℝ) →ₗ[ℝ] ((ι → ℂ) →L[ℂ] (ι → ℂ)) where
  toFun m := LinearMap.toContinuousLinearMap (complexMatrix m).mulVecLin
  map_add' m m' := by
    ext v i
    simp [complexMatrix,Matrix.mulVec,dotProduct,add_mul,Finset.sum_add_distrib]
  map_smul' a m := by
    ext v i
    simp [complexMatrix,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc,Complex.real_smul]

def matrixCLM : (ι → ι → ℝ) →L[ℝ] ((ι → ℂ) →L[ℂ] (ι → ℂ)) :=
  LinearMap.toContinuousLinearMap matrixOp

theorem matrixCLM_apply (m : ι → ι → ℝ) (v : ι → ℂ) :
    matrixCLM m v = (complexMatrix m).mulVec v := rfl

/-- Entrywise product rule for the complexified matrix action. -/
theorem mulVec_hasDerivAt (J : ℝ → ι → ι → ℝ) (D : ι → ι → ℝ) (r0 : ℝ)
    (hJ : ∀ i j, HasDerivAt (fun r => J r i j) (D i j) r0)
    (g : ℝ → ι → ℂ) (g' : ι → ℂ) (hg : HasDerivAt g g' r0) :
    HasDerivAt (fun r => (complexMatrix (J r)).mulVec (g r))
      ((complexMatrix D).mulVec (g r0)+(complexMatrix (J r0)).mulVec g') r0 := by
  apply hasDerivAt_pi.2
  intro i
  have hs : HasDerivAt (fun r => ∑ j, (J r i j : ℂ)*g r j)
      (∑ j, ((D i j : ℂ)*g r0 j+(J r0 i j : ℂ)*g' j)) r0 :=
    HasDerivAt.fun_sum fun j _ => ((hJ i j).ofReal_comp).mul (hasDerivAt_pi.1 hg j)
  simpa [complexMatrix,Matrix.mulVec,dotProduct,Finset.sum_add_distrib] using hs

/-- Derivative of a continued simple eigenvalue: pairing the actual
parameter derivative with the normalized left eigenfunctional. -/
theorem eigenvalue_derivative (J : ℝ → ι → ι → ℝ) (D : ι → ι → ℝ)
    (hJ : ∀ i j, HasDerivAt (fun r => J r i j) (D i j) 0)
    (f : ℝ → ℂ) (f' : ℂ) (hf : HasDerivAt f f' 0)
    (g : ℝ → ι → ℂ) (g' : ι → ℂ) (hg : HasDerivAt g g' 0)
    (he : ∀ᶠ r in 𝓝 (0:ℝ), (complexMatrix (J r)).mulVec (g r) = f r • g r)
    (ell : (ι → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ w, ell ((complexMatrix (J 0)).mulVec w) = f 0*ell w) (hn : ell (g 0) = 1) :
    f' = ell ((complexMatrix D).mulVec (g 0)) := by
  have h1 := mulVec_hasDerivAt J D 0 hJ g g' hg
  have h2 : HasDerivAt (fun r => f r • g r) (f 0 • g'+f' • g 0) 0 := hf.smul hg
  have h3 := h2.congr_of_eventuallyEq he
  have hu := h1.unique h3
  have hh := congrArg ell hu
  rw [map_add,map_add,map_smul,map_smul,hl,hn,smul_eq_mul,smul_eq_mul] at hh
  linear_combination -hh

end Matrices

section Continuation
variable {n : ℕ} {σ : Type*} [Fintype σ] [DecidableEq σ]
variable (k : ℝ → Rates n) (x : State n)

/-- The actual complexified loaded source as a real-parameter operator family. -/
def loadedCLM (κ : ℝ) (p : ℝ × ℝ) :
    (CoordinateIndex (n+1) → ℂ) →L[ℂ] (CoordinateIndex (n+1) → ℂ) :=
  matrixCLM (fun i j => jointMatrix k x κ p i j)

theorem loadedCLM_apply (κ : ℝ) (p : ℝ × ℝ) (v : CoordinateIndex (n+1) → ℂ) :
    loadedCLM k x κ p v = (complexMatrix (jointMatrix k x κ p)).mulVec v := rfl

theorem loadedCLM_smooth (κ : ℝ) (hk : MultisiteSmoothField.RatesSmooth k) :
    ContDiff ℝ ⊤ (loadedCLM k x κ) :=
  (matrixCLM (ι := CoordinateIndex (n+1))).contDiff.comp (jointMatrix_smooth k x κ hk)

/-- The actual kinetic-parameter derivative of the loaded source matrix. -/
def kineticDerivative (κ : ℝ) (p : ℝ × ℝ) :
    Matrix (CoordinateIndex (n+1)) (CoordinateIndex (n+1)) ℝ :=
  fun i j => fderiv ℝ (fun q : ℝ × ℝ => jointMatrix k x κ q i j) p (0,1)

theorem kineticDerivative_hasDerivAt (κ : ℝ) (hk : MultisiteSmoothField.RatesSmooth k)
    (ε r0 : ℝ) (i j : CoordinateIndex (n+1)) :
    HasDerivAt (fun r => jointMatrix k x κ (ε,r0+r) i j)
      (kineticDerivative k x κ (ε,r0) i j) 0 := by
  have hf := (((jointMatrix_entry_smooth k x κ hk i j).differentiable (by simp))
    (ε,r0)).hasFDerivAt
  have hl : HasDerivAt (fun r : ℝ => ((ε,r0+r) : ℝ × ℝ)) ((0,1) : ℝ × ℝ) 0 :=
    (hasDerivAt_const (0:ℝ) ε).prodMk ((hasDerivAt_id (0:ℝ)).const_add r0)
  have h := hf.comp_hasDerivAt_of_eq (0:ℝ) hl (by simp)
  exact h

theorem kineticDerivative_continuous (κ : ℝ) (hk : MultisiteSmoothField.RatesSmooth k)
    (i j : CoordinateIndex (n+1)) :
    Continuous (fun p : ℝ × ℝ => kineticDerivative k x κ p i j) :=
  ((jointMatrix_entry_smooth k x κ hk i j).continuous_fderiv (by simp)).clm_apply
    continuous_const

/-- The zero-load face identity in complex coordinates, for every kinetic parameter. -/
theorem loaded_face (κ r : ℝ) (hx : x.F ≠ 0) (y : CoordinateIndex n → ℂ) :
    (complexMatrix (jointMatrix k x κ (0,r))).mulVec (siteEquiv ℂ n (y,0)) =
      siteEquiv ℂ n ((complexMatrix (sourceMatrix (k r) x)).mulVec y,0) := by
  have h := loadedOp_siteEquiv k x κ r (y,0)
  rw [splitOp_block k x κ r hx] at h
  have hb : UpperTriangularEigenbasis.block (parentOp k x r) (coupling k x κ r) (normalOp κ)
      (y,0) = (parentOp k x r y,0) := by
    change (parentOp k x r y+coupling k x κ r 0,normalOp κ 0) = _
    simp
  rw [hb] at h
  simpa only [loadedOp,parentOp,Matrix.mulVecLin_apply] using h

/-- Differentiating the face identity: the actual kinetic derivative of the
loaded source restricts on the face to the parent kinetic derivative. -/
theorem face_kinetic (κ : ℝ) (hk : MultisiteSmoothField.RatesSmooth k) (hx : x.F ≠ 0)
    (M1 : Matrix (CoordinateIndex n) (CoordinateIndex n) ℝ)
    (hM1 : ∀ i j, HasDerivAt (fun r => sourceMatrix (k r) x i j) (M1 i j) 0)
    (y : CoordinateIndex n → ℂ) :
    (complexMatrix (kineticDerivative k x κ (0,0))).mulVec (siteEquiv ℂ n (y,0)) =
      siteEquiv ℂ n ((complexMatrix M1).mulVec y,0) := by
  have hJ : ∀ i j, HasDerivAt (fun r => jointMatrix k x κ (0,r) i j)
      (kineticDerivative k x κ (0,0) i j) 0 := by
    intro i j
    simpa only [zero_add] using kineticDerivative_hasDerivAt k x κ hk 0 0 i j
  have hL := mulVec_hasDerivAt (fun r => fun i j => jointMatrix k x κ (0,r) i j)
    (kineticDerivative k x κ (0,0)) 0 hJ (fun _ => siteEquiv ℂ n (y,0)) 0
    (hasDerivAt_const _ _)
  have hP := mulVec_hasDerivAt (fun r => fun i j => sourceMatrix (k r) x i j) M1 0 hM1
    (fun _ => y) 0 (hasDerivAt_const _ _)
  let T : ((CoordinateIndex n → ℂ) × (Fin 3 → ℂ)) →L[ℝ] (CoordinateIndex (n+1) → ℂ) :=
    LinearMap.toContinuousLinearMap ((siteEquiv ℂ n).toLinearMap.restrictScalars ℝ)
  have hR := T.hasFDerivAt.comp_hasDerivAt (0:ℝ)
    (hP.prodMk (hasDerivAt_const (0:ℝ) (0 : Fin 3 → ℂ)))
  have heq : (fun r => (complexMatrix (fun i j => jointMatrix k x κ (0,r) i j)).mulVec
      (siteEquiv ℂ n (y,0))) =
      T ∘ (fun r => ((complexMatrix (fun i j => sourceMatrix (k r) x i j)).mulVec y,
        (0 : Fin 3 → ℂ))) := by
    funext r
    exact loaded_face k x κ r hx y
  rw [heq] at hL
  have hu := hL.unique hR
  simpa [T,Matrix.mulVec_zero] using hu

omit [DecidableEq σ] in
/-- Zero-load crossing equality: the actual loaded kinetic pairing at the
parent critical point is the parent crossing. -/
theorem zero_crossing (hk : MultisiteSmoothField.RatesSmooth k) (hx : x.F ≠ 0)
    (d : Data σ (sourceMatrix (k 0) x))
    (M1 : Matrix (CoordinateIndex n) (CoordinateIndex n) ℝ)
    (hM1 : ∀ i j, HasDerivAt (fun r => sourceMatrix (k r) x i j) (M1 i j) 0) :
    (zeroBasis k x d).coord (Sum.inr 0)
      ((complexMatrix (kineticDerivative k x (scale d) (0,0))).mulVec
        (zeroBasis k x d (Sum.inr 0))) = crossing d M1 := by
  rw [zeroBasis_critical,face_kinetic k x (scale d) hk hx M1 hM1,zeroBasis_coord_face]
  rfl

/-- Main continuation theorem for the actual added-site family. For the
separating scale chosen from the parent spectrum, there is a smooth critical
kinetic curve through the parent critical point along which, for all
sufficiently small signed loads, the actual source has the complete
strengthened spectral invariant and negative actual crossing. The selected
critical vector, normalized left functional and frequency are continuous
and restrict at zero load to the embedded parent data. -/
theorem critical_continuation (hk : MultisiteSmoothField.RatesSmooth k) (hx : x.F ≠ 0)
    (d : Data σ (sourceMatrix (k 0) x))
    (M1 : Matrix (CoordinateIndex n) (CoordinateIndex n) ℝ)
    (hM1 : ∀ i j, HasDerivAt (fun r => sourceMatrix (k r) x i j) (M1 i j) 0)
    (hcross : (crossing d M1).re < 0) :
    ∃ (R : ℝ → ℝ) (q : ℝ → CoordinateIndex (n+1) → ℂ)
      (p : ℝ → (CoordinateIndex (n+1) → ℂ) →L[ℂ] ℂ) (ω : ℝ → ℝ),
      ContDiffAt ℝ ⊤ R 0 ∧ R 0 = 0 ∧
      ContinuousAt q 0 ∧ q 0 = siteEquiv ℂ n (d.basis (Sum.inr 0),0) ∧
      ContinuousAt p 0 ∧ (∀ y, p 0 (siteEquiv ℂ n (y,0)) = d.basis.coord (Sum.inr 0) y) ∧
      ContinuousAt ω 0 ∧ ω 0 = d.freq ∧
      ∀ᶠ ε in 𝓝 (0:ℝ), ∃ dε : Data (σ ⊕ Fin 3) (jointMatrix k x (scale d) (ε,R ε)),
        dε.basis (Sum.inr 0) = q ε ∧
        (dε.basis.coord (Sum.inr 0)).toContinuousLinearMap = p ε ∧ dε.freq = ω ε ∧
        (crossing dε (kineticDerivative k x (scale d) (ε,R ε))).re < 0 := by
  classical
  set κ := scale d with hκ
  set d0 := zeroData k x d hx with hd0
  set b := zeroBasis k x d with hb
  set eig := eigenvalues d0 with heig
  set A := loadedCLM k x κ with hAdef
  have hA : ContDiffAt ℝ ⊤ A 0 := (loadedCLM_smooth k x κ hk).contDiffAt
  have he0 : ∀ i, A 0 (b i) = eig i • b i := by
    intro i
    rw [hAdef,loadedCLM_apply]
    exact CriticalSpectrum.eigen d0 i
  have hinj : Function.Injective eig := eigenvalues_injective d0
  obtain ⟨μ,v,hμ,hv,hμ0,hv0,huniq,hcoordc,hev⟩ :=
    ComplexNearbyEigenbasis.smooth_eigenbasis A hA b eig he0 hinj
  have hconjA : ∀ p u, A p (RealEigenpairPersistence.conjugate u) =
      RealEigenpairPersistence.conjugate (A p u) := by
    intro p u
    rw [hAdef,loadedCLM_apply,loadedCLM_apply]
    exact conjugate_action _ u
  have hsimple : ∀ i j, j ≠ i → eig j ≠ eig i := fun i j hji h => hji (hinj h)
  have hμi : ∀ i, μ 0 i = eig i := fun i => congrFun hμ0 i
  have hvi : ∀ i, v 0 i = b i := fun i => congrFun hv0 i
  have hunique' : ∀ i, ∀ᶠ e in 𝓝 ((0:ℝ × ℝ),(v 0 i,μ 0 i)),
      (A e.1 e.2.1 = e.2.2 • e.2.1 ∧ b.coord i e.2.1 = 1) ↔ (v e.1 i,μ e.1 i) = e.2 := by
    intro i
    rw [hvi,hμi]
    exact huniq i
  have heig_i : ∀ i, ∀ᶠ e in 𝓝 (0:ℝ × ℝ), A e (v e i) = μ e i • v e i ∧ b.coord i (v e i) = 1 :=
    fun i => hev.mono fun e he => he.1 i
  -- reality of the stable branches
  have hreal : ∀ s, ∀ᶠ e in 𝓝 (0:ℝ × ℝ), star (μ e (Sum.inl s)) = μ e (Sum.inl s) ∧
      RealEigenpairPersistence.conjugate (v e (Sum.inl s)) = v e (Sum.inl s) := by
    intro s
    have hell := RealEigenfunctional.coordinate_conjugation (A 0).toLinearMap b eig he0
      (Sum.inl s) (hsimple _) (hconjA 0) (stable_real_eigenvalue d0 s) (d0.stable_real s)
    exact RealEigenpairPersistence.eventually_real A (b.coord (Sum.inl s))
      (fun e => μ e (Sum.inl s)) (fun e => v e (Sum.inl s))
      (hμ _).continuousAt (hv _).continuousAt
      (show star (μ 0 (Sum.inl s)) = μ 0 (Sum.inl s) by
        rw [hμi]; exact stable_real_eigenvalue d0 s)
      (show RealEigenpairPersistence.conjugate (v 0 (Sum.inl s)) = v 0 (Sum.inl s) by
        rw [hvi]; exact d0.stable_real s)
      (Eventually.of_forall hconjA) hell (heig_i _) (hunique' _)
  -- the critical pair stays conjugate
  have hpair : ∀ᶠ e in 𝓝 (0:ℝ × ℝ), star (μ e (Sum.inr 0)) = μ e (Sum.inr 1) ∧
      RealEigenpairPersistence.conjugate (v e (Sum.inr 0)) = v e (Sum.inr 1) := by
    have hell := RealEigenfunctional.coordinate_pair_conjugation (A 0).toLinearMap b eig he0
      (Sum.inr 0) (Sum.inr 1) (hsimple _) (hconjA 0) (critical_conj_eigenvalue d0)
      d0.critical_pair.symm
    exact RealEigenpairPersistence.eventually_conjugate_pair A (b.coord (Sum.inr 0))
      (b.coord (Sum.inr 1)) (fun e => μ e (Sum.inr 0)) (fun e => μ e (Sum.inr 1))
      (fun e => v e (Sum.inr 0)) (fun e => v e (Sum.inr 1))
      (hμ _).continuousAt (hv _).continuousAt
      (show star (μ 0 (Sum.inr 0)) = μ 0 (Sum.inr 1) by
        rw [hμi,hμi]; exact critical_conj_eigenvalue d0)
      (show RealEigenpairPersistence.conjugate (v 0 (Sum.inr 0)) = v 0 (Sum.inr 1) by
        rw [hvi,hvi]; exact d0.critical_pair.symm)
      (Eventually.of_forall hconjA) hell (heig_i _) (hunique' _)
  -- zero-load crossing along the kinetic slice
  have hzc : b.coord (Sum.inr 0) ((complexMatrix (kineticDerivative k x κ (0,0))).mulVec
      (b (Sum.inr 0))) = crossing d M1 := zero_crossing k x hk hx d M1 hM1
  have hslice : HasDerivAt (fun r => μ (0,r) (Sum.inr 0)) (crossing d M1) 0 := by
    have hsl : Tendsto (fun r : ℝ => ((0:ℝ),r)) (𝓝 0) (𝓝 (0:ℝ × ℝ)) := by
      have hc : Continuous (fun r : ℝ => ((0:ℝ),r)) := continuous_const.prodMk continuous_id
      simpa using hc.tendsto 0
    have hfd : DifferentiableAt ℝ (fun r : ℝ => μ (0,r) (Sum.inr 0)) 0 := by
      have h1 : DifferentiableAt ℝ (fun a : ℝ × ℝ => μ a (Sum.inr 0)) ((0:ℝ),(0:ℝ)) :=
        (hμ (Sum.inr 0)).differentiableAt (by simp)
      exact h1.comp (0:ℝ) ((differentiableAt_const (0:ℝ)).prodMk differentiableAt_id)
    have hgd : DifferentiableAt ℝ (fun r : ℝ => v (0,r) (Sum.inr 0)) 0 := by
      have h1 : DifferentiableAt ℝ (fun a : ℝ × ℝ => v a (Sum.inr 0)) ((0:ℝ),(0:ℝ)) :=
        (hv (Sum.inr 0)).differentiableAt (by simp)
      exact h1.comp (0:ℝ) ((differentiableAt_const (0:ℝ)).prodMk differentiableAt_id)
    have hJ : ∀ i j, HasDerivAt (fun r => jointMatrix k x κ (0,r) i j)
        (kineticDerivative k x κ (0,0) i j) 0 := by
      intro i j
      simpa only [zero_add] using kineticDerivative_hasDerivAt k x κ hk 0 0 i j
    have hes : ∀ᶠ r in 𝓝 (0:ℝ),
        (complexMatrix (fun i j => jointMatrix k x κ (0,r) i j)).mulVec (v (0,r) (Sum.inr 0)) =
          μ (0,r) (Sum.inr 0) • v (0,r) (Sum.inr 0) := by
      filter_upwards [hsl.eventually (heig_i (Sum.inr 0))] with r hr
      rw [← loadedCLM_apply]
      exact hr.1
    have hcrit0 : μ (0,0) (Sum.inr 0) = eig (Sum.inr 0) := hμi _
    have hl : ∀ w, b.coord (Sum.inr 0)
        ((complexMatrix (fun i j => jointMatrix k x κ (0,0) i j)).mulVec w) =
        μ (0,0) (Sum.inr 0)*b.coord (Sum.inr 0) w := by
      intro w
      rw [hcrit0,← loadedCLM_apply]
      exact UpperTriangularEigenbasis.coordinate_eigen (A 0).toLinearMap b eig he0 _ w
    have hn : b.coord (Sum.inr 0) (v (0,0) (Sum.inr 0)) = 1 := by
      change b.coord (Sum.inr 0) (v 0 (Sum.inr 0)) = 1
      rw [hvi]
      simp
    have hder := eigenvalue_derivative (fun r => fun i j => jointMatrix k x κ (0,r) i j)
      (kineticDerivative k x κ (0,0)) hJ (fun r => μ (0,r) (Sum.inr 0)) _ hfd.hasDerivAt
      (fun r => v (0,r) (Sum.inr 0)) _ hgd.hasDerivAt hes (b.coord (Sum.inr 0)) hl hn
    have hv00 : v (0,0) (Sum.inr 0) = b (Sum.inr 0) := hvi _
    beta_reduce at hder
    rw [hv00,hzc] at hder
    rw [← hder]
    exact hfd.hasDerivAt
  have hre : HasDerivAt (fun r => (μ (0,r) (Sum.inr 0)).re) (crossing d M1).re 0 := by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) hslice
    simpa using h
  have hf0 : μ (0,0) (Sum.inr 0) = Complex.I*(d.freq:ℂ) := hμi _
  obtain ⟨R,hR,hR0,hcurve,-⟩ := CriticalParameterCurve.complex_curve
    (fun e => μ e (Sum.inr 0)) 0 d.freq (crossing d M1).re (hμ (Sum.inr 0)) hf0 d.freq_pos
    hre (ne_of_lt hcross)
  -- the critical curve and its limits
  let γ : ℝ → ℝ × ℝ := fun ε => (ε,R ε)
  have hγ0 : γ 0 = 0 := by simp [γ,hR0]
  have hγc : ContinuousAt γ 0 := continuousAt_id.prodMk hR.continuousAt
  have hγ : Tendsto γ (𝓝 0) (𝓝 0) := by
    have h := hγc.tendsto
    rwa [hγ0] at h
  have hμc : ∀ i, ContinuousAt (fun ε => μ (γ ε) i) 0 := fun i =>
    ContinuousAt.comp_of_eq (hμ i).continuousAt hγc hγ0
  have hvc : ∀ i, ContinuousAt (fun ε => v (γ ε) i) 0 := fun i =>
    ContinuousAt.comp_of_eq (hv i).continuousAt hγc hγ0
  have hpc : ContinuousAt (fun ε => ComplexNearbyEigenbasis.inverseCoordinate b (v (γ ε))
      (Sum.inr 0)) 0 :=
    ContinuousAt.comp_of_eq (g := fun a => ComplexNearbyEigenbasis.inverseCoordinate b (v a)
      (Sum.inr 0)) (f := γ) (hcoordc (Sum.inr 0)) hγc hγ0
  have hKc : ContinuousAt (fun ε => matrixCLM (fun i j => kineticDerivative k x κ (γ ε) i j)) 0 :=
    matrixCLM.continuous.continuousAt.comp
      (continuousAt_pi.2 fun i => continuousAt_pi.2 fun j =>
        (kineticDerivative_continuous k x κ hk i j).continuousAt.comp hγc)
  -- the actual crossing along the curve
  let cr : ℝ → ℂ := fun ε => ComplexNearbyEigenbasis.inverseCoordinate b (v (γ ε)) (Sum.inr 0)
    (matrixCLM (fun i j => kineticDerivative k x κ (γ ε) i j) (v (γ ε) (Sum.inr 0)))
  have hcrc : ContinuousAt cr 0 := hpc.clm_apply (hKc.clm_apply (hvc (Sum.inr 0)))
  have hcr0 : cr 0 = crossing d M1 := by
    change ComplexNearbyEigenbasis.inverseCoordinate b (v (γ 0)) (Sum.inr 0)
      (matrixCLM (fun i j => kineticDerivative k x κ (γ 0) i j) (v (γ 0) (Sum.inr 0))) = _
    rw [hγ0,hv0,ComplexNearbyEigenbasis.inverseCoordinate_self,matrixCLM_apply,← hzc]
    rfl
  have hcrneg : ∀ᶠ ε in 𝓝 (0:ℝ), (cr ε).re < 0 := by
    have hrc : ContinuousAt (fun ε => (cr ε).re) 0 :=
      Complex.continuous_re.continuousAt.comp hcrc
    have h0 : (cr 0).re < 0 := by rw [hcr0]; exact hcross
    exact hrc.eventually (gt_mem_nhds h0)
  -- stable branches stay negative and distinct
  have hneg : ∀ s, ∀ᶠ ε in 𝓝 (0:ℝ), (μ (γ ε) (Sum.inl s)).re < 0 := by
    intro s
    have hrc : ContinuousAt (fun ε => (μ (γ ε) (Sum.inl s)).re) 0 :=
      Complex.continuous_re.continuousAt.comp (hμc _)
    have h0 : (μ (γ 0) (Sum.inl s)).re < 0 := by
      rw [hγ0,hμi]
      simpa [heig,hd0] using d0.stable_neg s
    exact hrc.eventually (gt_mem_nhds h0)
  have hdist : ∀ s t, s ≠ t → ∀ᶠ ε in 𝓝 (0:ℝ),
      (μ (γ ε) (Sum.inl s)).re ≠ (μ (γ ε) (Sum.inl t)).re := by
    intro s t hst
    have hrc : ContinuousAt (fun ε => (μ (γ ε) (Sum.inl s)).re-(μ (γ ε) (Sum.inl t)).re) 0 :=
      (Complex.continuous_re.continuousAt.comp (hμc _)).sub
        (Complex.continuous_re.continuousAt.comp (hμc _))
    have h0 : (μ (γ 0) (Sum.inl s)).re-(μ (γ 0) (Sum.inl t)).re ≠ 0 := by
      rw [hγ0,hμi,hμi]
      simp only [heig,hd0,eigenvalues_inl,Complex.ofReal_re]
      exact sub_ne_zero.mpr (fun h => hst (d0.stable_injective h))
    filter_upwards [hrc.eventually (isOpen_ne.mem_nhds h0)] with ε hε
    exact sub_ne_zero.mp hε
  refine ⟨R,fun ε => v (γ ε) (Sum.inr 0),
    fun ε => ComplexNearbyEigenbasis.inverseCoordinate b (v (γ ε)) (Sum.inr 0),
    fun ε => (μ (γ ε) (Sum.inr 0)).im,hR,hR0,hvc _,?_,hpc,?_,
    Complex.continuous_im.continuousAt.comp (hμc _),?_,?_⟩
  · change v (γ 0) (Sum.inr 0) = _
    rw [hγ0,hvi,hb]
    exact zeroBasis_critical k x d
  · intro y
    change ComplexNearbyEigenbasis.inverseCoordinate b (v (γ 0)) (Sum.inr 0) _ = _
    have hv0' : v (γ 0) = b := by rw [hγ0]; exact hv0
    rw [hv0',ComplexNearbyEigenbasis.inverseCoordinate_self]
    exact zeroBasis_coord_face k x d y
  · change (μ (γ 0) (Sum.inr 0)).im = d.freq
    rw [hγ0,hμi]
    simp [heig,hd0,zeroData]
  · have hall_real : ∀ᶠ ε in 𝓝 (0:ℝ), ∀ s, star (μ (γ ε) (Sum.inl s)) = μ (γ ε) (Sum.inl s) ∧
        RealEigenpairPersistence.conjugate (v (γ ε) (Sum.inl s)) = v (γ ε) (Sum.inl s) :=
      eventually_all.2 fun s => hγ.eventually (hreal s)
    have hall_neg : ∀ᶠ ε in 𝓝 (0:ℝ), ∀ s, (μ (γ ε) (Sum.inl s)).re < 0 :=
      eventually_all.2 hneg
    have hall_dist : ∀ᶠ ε in 𝓝 (0:ℝ), ∀ s t, s ≠ t →
        (μ (γ ε) (Sum.inl s)).re ≠ (μ (γ ε) (Sum.inl t)).re :=
      eventually_all.2 fun s => eventually_all.2 fun t => by
        by_cases hst : s = t
        · exact Eventually.of_forall fun _ h => absurd hst h
        · exact (hdist s t hst).mono fun _ h _ => h
    filter_upwards [hγ.eventually hev,hγ.eventually hpair,hcurve,hall_real,hall_neg,
      hall_dist,hcrneg] with ε hevε hpε hcε hrε hnε hdε hcrε
    obtain ⟨heqε,c,hc,hcc,-⟩ := hevε
    have hμreal : ∀ s, μ (γ ε) (Sum.inl s) = ((μ (γ ε) (Sum.inl s)).re : ℂ) := by
      intro s
      apply Complex.ext
      · simp
      · simpa using (Complex.conj_eq_iff_im.mp (hrε s).1)
    have hμcrit : μ (γ ε) (Sum.inr 0) = Complex.I*((μ (γ ε) (Sum.inr 0)).im : ℂ) := by
      apply Complex.ext
      · simpa using hcε.1
      · simp
    let dε : Data (σ ⊕ Fin 3) (jointMatrix k x κ (ε,R ε)) :=
      { basis := c
        stable := fun s => (μ (γ ε) (Sum.inl s)).re
        freq := (μ (γ ε) (Sum.inr 0)).im
        freq_pos := hcε.2
        stable_neg := hnε
        stable_injective := by
          intro s t hst
          by_contra h
          exact hdε s t h hst
        stable_eigen := by
          intro s
          rw [hc,← loadedCLM_apply,← hμreal]
          exact (heqε (Sum.inl s)).1
        critical_eigen := by
          rw [hc,← loadedCLM_apply,← hμcrit]
          exact (heqε (Sum.inr 0)).1
        stable_real := by
          intro s
          rw [hc]
          exact (hrε s).2
        critical_pair := by
          rw [hc,hc]
          exact hpε.2.symm }
    refine ⟨dε,hc _,hcc _,rfl,?_⟩
    have hx : crossing dε (kineticDerivative k x κ (ε,R ε)) = cr ε := by
      change c.coord (Sum.inr 0) ((complexMatrix (kineticDerivative k x κ (ε,R ε))).mulVec
        (c (Sum.inr 0))) = _
      rw [hc]
      have h := congrArg (fun L : (CoordinateIndex (n+1) → ℂ) →L[ℂ] ℂ =>
        L ((complexMatrix (kineticDerivative k x κ (ε,R ε))).mulVec (v (γ ε) (Sum.inr 0))))
        (hcc (Sum.inr 0))
      exact h
    rw [hx]
    exact hcrε

end Continuation

end
end ThreeSitePhosphorylation.AddedSiteCriticalContinuation
