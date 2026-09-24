import proofs.ThreeSitePhosphorylation.AddedSiteHessianTransport
import proofs.ThreeSitePhosphorylation.AddedSiteCoefficientContinuity

/-! Actual chemical docking of the added-site coefficient and crossing transport.

* Zero load: for the actual affine parent source and the actual scaled child
  source at zero load, the normalized coefficient `G` and the kinetic crossing
  pairing are exactly equal (with genuine child resolvents and the genuine
  normalized child left functional; no zero extension is assumed).
* Positive load: the literal child source matrix and tensor are continuous in
  the load. Along ANY continuous critical data (curve `R`, vector `q`, left
  functional `p`, frequency `w`) that start from the zero-load critical data,
  both resolvent operators stay genuinely invertible and `Re G<0` and the
  crossing stays negative for all sufficiently small positive loads.

The continued critical data themselves (B's selected critical curve and its
eigenvector/left-functional branches) are explicit inputs here. -/
namespace ThreeSitePhosphorylation.AddedSiteCrossingTransport
noncomputable section
open scoped Topology BigOperators
open Filter PhosphorylationSharpness MultisiteChart MultisiteSource MultisiteCenteredFace
open MultisiteCoordinates MultisiteTaylor MultisiteTensor ScaledMultisiteSource
open ScaledAffineFamily AddedSiteHessianTransport GenericComplexification GenericTensorBilinear
open GenericPeriodicKernel AddedSiteCoefficientTransport AddedSiteCoefficientContinuity

variable {X : Type*} [TopologicalSpace X]

/-! ### Continuity of the literal source coefficients -/

/-- Componentwise continuity of a rate family. -/
def RatesContinuousAt {n : ℕ} (k : X → Rates n) (x0 : X) : Prop :=
  ∀ i, ContinuousAt (fun a => (k a).a i) x0 ∧ ContinuousAt (fun a => (k a).b i) x0 ∧
    ContinuousAt (fun a => (k a).c i) x0 ∧ ContinuousAt (fun a => (k a).alpha i) x0 ∧
    ContinuousAt (fun a => (k a).beta i) x0 ∧ ContinuousAt (fun a => (k a).gamma i) x0

/-- Componentwise continuity of a full-state family. -/
def StateContinuousAt {n : ℕ} (s : X → PhosphorylationSharpness.State n) (x0 : X) : Prop :=
  (∀ i, ContinuousAt (fun a => (s a).S i) x0) ∧ ContinuousAt (fun a => (s a).E) x0 ∧
    ContinuousAt (fun a => (s a).F) x0 ∧ (∀ i, ContinuousAt (fun a => (s a).C i) x0) ∧
    (∀ i, ContinuousAt (fun a => (s a).D i) x0)

theorem sourceRow_continuousAt {n : ℕ} (i j : Fin n) {A B C D : X → ℝ} {x0 : X}
    (hA : ContinuousAt A x0) (hB : ContinuousAt B x0) (hC : ContinuousAt C x0)
    (hD : ContinuousAt D x0) :
    ContinuousAt (fun a => sourceRow i j (A a) (B a) (C a) (D a)) x0 := by
  unfold sourceRow
  by_cases h1 : i.castSucc=j.succ <;> by_cases h2 : i.succ=j.succ <;>
    simp only [h1,h2,if_true,if_false,add_zero,zero_add]
  · exact (hA.neg.add hD).add (hC.sub hB)
  · exact hA.neg.add hD
  · exact hC.sub hB
  · exact continuousAt_const

theorem assemble_continuousAt {n : ℕ} {A B C D : X → Fin n → ℝ} {x0 : X}
    (hA : ∀ i, ContinuousAt (fun a => A a i) x0) (hB : ∀ i, ContinuousAt (fun a => B a i) x0)
    (hC : ∀ i, ContinuousAt (fun a => C a i) x0) (hD : ∀ i, ContinuousAt (fun a => D a i) x0) :
    ContinuousAt (fun a => assemble (A a) (B a) (C a) (D a)) x0 := by
  unfold assemble
  refine ContinuousAt.prodMk ?_ (ContinuousAt.prodMk ?_ ?_)
  · apply continuousAt_pi.2
    intro j
    apply continuousAt_sum
    intro i _
    exact sourceRow_continuousAt i j (hA i) (hB i) (hC i) (hD i)
  · exact continuousAt_pi.2 fun i => (hA i).sub (hC i)
  · exact continuousAt_pi.2 fun i => (hB i).sub (hD i)

theorem linearTerm_continuousAt {n : ℕ} {k : X → Rates n}
    {s : X → PhosphorylationSharpness.State n} {x0 : X}
    (hk : RatesContinuousAt k x0) (hs : StateContinuousAt s x0) (y : ReducedState n) :
    ContinuousAt (fun a => linearTerm (k a) (s a) y) x0 := by
  obtain ⟨hS,hE,hF,-,-⟩ := hs
  unfold linearTerm
  apply assemble_continuousAt
  · intro i
    unfold linearKinase
    exact ((hk i).1.mul ((continuousAt_const.mul hE).add ((hS _).mul continuousAt_const))).sub
      ((hk i).2.1.mul continuousAt_const)
  · intro i
    unfold linearPhosphatase
    exact ((hk i).2.2.2.1.mul ((continuousAt_const.mul hF).add ((hS _).mul continuousAt_const))).sub
      ((hk i).2.2.2.2.1.mul continuousAt_const)
  · intro i
    exact (hk i).2.2.1.mul continuousAt_const
  · intro i
    exact (hk i).2.2.2.2.2.mul continuousAt_const

theorem bilinearTerm_continuousAt {n : ℕ} {k : X → Rates n} {x0 : X}
    (hk : RatesContinuousAt k x0) (u v : ReducedState n) :
    ContinuousAt (fun a => bilinearTerm (k a) u v) x0 := by
  unfold bilinearTerm
  apply assemble_continuousAt
  · intro i
    exact (hk i).1.mul continuousAt_const
  · intro i
    exact (hk i).2.2.2.1.mul continuousAt_const
  · intro i
    exact continuousAt_const
  · intro i
    exact continuousAt_const

theorem sourceMatrix_continuousAt {n : ℕ} {k : X → Rates n}
    {s : X → PhosphorylationSharpness.State n} {x0 : X}
    (hk : RatesContinuousAt k x0) (hs : StateContinuousAt s x0) :
    ContinuousAt (fun a => sourceMatrix (k a) (s a)) x0 := by
  apply continuousAt_pi.2
  intro i
  apply continuousAt_pi.2
  intro j
  simp only [sourceMatrix,LinearMap.toMatrix'_apply,coordinateLinear_apply]
  exact (continuous_apply i).continuousAt.comp
    ((toCoordinates n).continuous.continuousAt.comp (linearTerm_continuousAt hk hs _))

theorem sourceTensor_continuousAt {n : ℕ} {k : X → Rates n} {x0 : X}
    (hk : RatesContinuousAt k x0) :
    ContinuousAt (fun a => sourceTensor (k a)) x0 := by
  apply continuousAt_pi.2
  intro i
  apply continuousAt_pi.2
  intro j
  apply continuousAt_pi.2
  intro l
  simp only [sourceTensor,coordinateBilinear_apply]
  exact (continuous_apply i).continuousAt.comp
    ((toCoordinates n).continuous.continuousAt.comp (bilinearTerm_continuousAt hk _ _))

/-! ### The actual load path -/

/-- The new kinase binding rate of the scaled construction at load `ε`. -/
def loadRate {n : ℕ} (x : PhosphorylationSharpness.State n) (κ ε : ℝ) : ℝ :=
  2*κ*ε/(x.S (Fin.last n)*x.E)

/-- Offset rates of the actual child family at load `ε`. -/
def childOffset {n : ℕ} (offset : Rates n) (x : PhosphorylationSharpness.State n)
    (κ ε : ℝ) : Rates (n+1) :=
  appendScaledRates offset κ (loadRate x κ ε) (κ/x.F)

/-- Slope rates of the actual child family (independent of the load). -/
def childSlope {n : ℕ} (slope : Rates n) : Rates (n+1) := appendScaledRates slope 0 0 0

/-- The actual appended equilibrium at load `ε`. -/
def childState {n : ℕ} (x : PhosphorylationSharpness.State n) (ε : ℝ) :
    PhosphorylationSharpness.State (n+1) :=
  appendState x ε (2*ε) ε

/-- The child family is exactly the actual extended affine family. -/
theorem extendedFamily_eq {n : ℕ} (offset slope : Rates n)
    (x : PhosphorylationSharpness.State n) (κ ε r : ℝ) :
    extendedFamily (affineRates offset slope) x κ ε r=
      affineRates (childOffset offset x κ ε) (childSlope slope) r :=
  append_affineRates offset slope κ _ _ r

theorem childOffset_zero {n : ℕ} (offset : Rates n) (x : PhosphorylationSharpness.State n)
    (κ : ℝ) : childOffset offset x κ 0=zeroRates offset κ (κ/x.F) := by
  simp [childOffset,loadRate,zeroRates]

theorem childState_zero {n : ℕ} (x : PhosphorylationSharpness.State n) :
    childState x 0=zeroState x := by
  simp [childState,zeroState]

theorem childSlope_eq {n : ℕ} (slope : Rates n) : childSlope slope=zeroRates slope 0 0 := rfl

theorem childOffset_continuous {n : ℕ} (offset : Rates n)
    (x : PhosphorylationSharpness.State n) (κ ε0 : ℝ) :
    RatesContinuousAt (fun ε => childOffset offset x κ ε) ε0 := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [childOffset,appendScaledRates,Fin.lastCases_last,loadRate]
    exact ⟨((continuousAt_const.mul continuousAt_id).div_const _),continuousAt_const,
      continuousAt_const,continuousAt_const,continuousAt_const,continuousAt_const⟩
  · simp only [childOffset,appendScaledRates,Fin.lastCases_castSucc]
    exact ⟨continuousAt_const,continuousAt_const,continuousAt_const,continuousAt_const,
      continuousAt_const,continuousAt_const⟩

theorem const_rates_continuous {n : ℕ} (k : Rates n) (ε0 : ℝ) :
    RatesContinuousAt (fun _ : ℝ => k) ε0 := fun _ =>
  ⟨continuousAt_const,continuousAt_const,continuousAt_const,continuousAt_const,
    continuousAt_const,continuousAt_const⟩

theorem childState_continuous {n : ℕ} (x : PhosphorylationSharpness.State n) (ε0 : ℝ) :
    StateContinuousAt (fun ε => childState x ε) ε0 := by
  refine ⟨?_,continuousAt_const,continuousAt_const,?_,?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [childState,appendState,Fin.lastCases_last]
      exact continuousAt_const.mul continuousAt_id
    · simp only [childState,appendState,Fin.lastCases_castSucc]
      exact continuousAt_const
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [childState,appendState,Fin.lastCases_last]
      exact continuousAt_id
    · simp only [childState,appendState,Fin.lastCases_castSucc]
      exact continuousAt_const
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [childState,appendState,Fin.lastCases_last]
      exact continuousAt_id
    · simp only [childState,appendState,Fin.lastCases_castSucc]
      exact continuousAt_const

/-- Actual child operator `A0(ε)+R(ε) D(ε)` in the flat coordinate chart. -/
def childOperator {n : ℕ} (offset slope : Rates n) (x : PhosphorylationSharpness.State n)
    (κ ε r : ℝ) : Matrix (CoordinateIndex (n+1)) (CoordinateIndex (n+1)) ℝ :=
  sourceMatrix (childOffset offset x κ ε) (childState x ε)+
    r • sourceMatrix (childSlope slope) (childState x ε)

/-- Actual child kinetic derivative `D(ε)`. -/
def childDerivative {n : ℕ} (slope : Rates n) (x : PhosphorylationSharpness.State n)
    (ε : ℝ) : Matrix (CoordinateIndex (n+1)) (CoordinateIndex (n+1)) ℝ :=
  sourceMatrix (childSlope slope) (childState x ε)

/-- Actual child Hessian tensor at kinetic parameter `r`. -/
def childTensor {n : ℕ} (offset slope : Rates n) (x : PhosphorylationSharpness.State n)
    (κ ε r : ℝ) : GenericQuadraticTensor.Tensor (CoordinateIndex (n+1)) :=
  sourceTensor (childOffset offset x κ ε)+r • sourceTensor (childSlope slope)

/-- The literal child source is the affine quadratic field consumed by the
generic Hopf modules, at every load. -/
theorem childField_exact {n : ℕ} (offset slope : Rates n)
    (x : PhosphorylationSharpness.State n) (κ ε r : ℝ)
    (heq : ∀ s, Equilibrium (extendedFamily (affineRates offset slope) x κ ε s) (childState x ε))
    (y : CoordinateState (n+1)) :
    coordinateField (extendedFamily (affineRates offset slope) x κ ε r) (childState x ε) y=
      (childOperator offset slope x κ ε r).mulVec y+
        GenericQuadraticTensor.field (fun s => childTensor offset slope x κ ε s) r y := by
  have h := affine_coordinateField (childOffset offset x κ ε) (childSlope slope) (childState x ε)
    (fun s => by rw [← extendedFamily_eq]; exact heq s) r y
  rw [extendedFamily_eq]
  exact h

theorem childOperator_continuousAt {n : ℕ} (offset slope : Rates n)
    (x : PhosphorylationSharpness.State n) (κ : ℝ) {R : ℝ → ℝ} (hR : ContinuousAt R 0) :
    ContinuousAt (fun ε => childOperator offset slope x κ ε (R ε)) 0 := by
  unfold childOperator
  exact (sourceMatrix_continuousAt (childOffset_continuous offset x κ 0)
      (childState_continuous x 0)).add
    (hR.smul (sourceMatrix_continuousAt (const_rates_continuous _ 0) (childState_continuous x 0)))

theorem childDerivative_continuousAt {n : ℕ} (slope : Rates n)
    (x : PhosphorylationSharpness.State n) :
    ContinuousAt (fun ε => childDerivative slope x ε) 0 :=
  sourceMatrix_continuousAt (const_rates_continuous _ 0) (childState_continuous x 0)

theorem childTensor_continuousAt {n : ℕ} (offset slope : Rates n)
    (x : PhosphorylationSharpness.State n) (κ : ℝ) {R : ℝ → ℝ} (hR : ContinuousAt R 0) :
    ContinuousAt (fun ε => childTensor offset slope x κ ε (R ε)) 0 := by
  unfold childTensor
  exact (sourceTensor_continuousAt (childOffset_continuous offset x κ 0)).add
    (hR.smul continuousAt_const)

/-! ### Zero-load docking -/

theorem zero_load_face {n : ℕ} (offset slope : Rates n)
    (x : PhosphorylationSharpness.State n) (κ r : ℝ) :
    childOperator offset slope x κ 0 r*faceMatrix n=
      faceMatrix n*(sourceMatrix offset x+r • sourceMatrix slope x) ∧
    childDerivative slope x 0*faceMatrix n=faceMatrix n*sourceMatrix slope x ∧
    ∀ u v : CoordinateState n,
      realBilinear (childTensor offset slope x κ 0 r) ((faceMatrix n).mulVec u)
        ((faceMatrix n).mulVec v)=
      (faceMatrix n).mulVec (realBilinear (sourceTensor offset+r • sourceTensor slope) u v) := by
  unfold childOperator childDerivative childTensor
  rw [childOffset_zero,childState_zero,childSlope_eq]
  exact affine_face offset slope x κ (κ/x.F) r

/-- Exact zero-load equality of the genuine-resolvent coefficient and of the
kinetic crossing pairing for the actual chemical parent and child (step 4). -/
theorem zero_load_coefficient {n : ℕ} {σ : Type*} [DecidableEq σ]
    (offset slope : Rates n) (x : PhosphorylationSharpness.State n) (κ r w : ℝ) (hw : 0<w)
    (roots : σ → ℝ) (hn : ∀ i, roots i<0)
    (b : Module.Basis (σ ⊕ Fin 2) ℂ (CoordinateIndex n → ℂ))
    (he : ∀ i, (complexMatrix (sourceMatrix offset x+r • sourceMatrix slope x)).mulVec (b i)=
      spectralValues roots w i • b i)
    (h11 h20 : CoordinateIndex n → ℂ)
    (h11eq : (complexMatrix (sourceMatrix offset x+r • sourceMatrix slope x)).mulVec h11=
      complexBilinear (sourceTensor offset+r • sourceTensor slope) (b (Sum.inr 0))
        (conjugateVector (b (Sum.inr 0))))
    (h20eq : (2*Complex.I*(w:ℂ)) • h20-
      (complexMatrix (sourceMatrix offset x+r • sourceMatrix slope x)).mulVec h20=
      complexBilinear (sourceTensor offset+r • sourceTensor slope) (b (Sum.inr 0)) (b (Sum.inr 0)))
    (p : (CoordinateIndex (n+1) → ℂ) →L[ℂ] ℂ)
    (hp : ∀ y, p ((complexMatrix (childOperator offset slope x κ 0 r)).mulVec y)=
      (Complex.I*(w:ℂ))*p y)
    (hpv : p ((complexRect (faceMatrix n)).mulVec (b (Sum.inr 0)))=1)
    (hA' : Function.Injective (complexMatrix (childOperator offset slope x κ 0 r)).mulVecLin)
    (hS' : Function.Injective ((2*Complex.I*(w:ℂ)) •
      (LinearMap.id : (CoordinateIndex (n+1) → ℂ) →ₗ[ℂ] (CoordinateIndex (n+1) → ℂ))-
        (complexMatrix (childOperator offset slope x κ 0 r)).mulVecLin)) :
    resolventCoefficient p (childOperator offset slope x κ 0 r) (childTensor offset slope x κ 0 r)
        ((complexRect (faceMatrix n)).mulVec (b (Sum.inr 0))) w=
      coefficient (b.coord (Sum.inr 0)) (sourceTensor offset+r • sourceTensor slope)
        (b (Sum.inr 0)) h11 h20 ∧
    p ((complexMatrix (childDerivative slope x 0)).mulVec
        ((complexRect (faceMatrix n)).mulVec (b (Sum.inr 0))))=
      b.coord (Sum.inr 0) ((complexMatrix (sourceMatrix slope x)).mulVec (b (Sum.inr 0))) := by
  obtain ⟨hA,hD,hT⟩ := zero_load_face offset slope x κ r
  have hcoord : ∀ y, b.coord (Sum.inr 0)
      ((complexMatrix (sourceMatrix offset x+r • sourceMatrix slope x)).mulVec y)=
      (Complex.I*(w:ℂ))*b.coord (Sum.inr 0) y := by
    intro y
    have := basis_coord_eigen b _ (spectralValues roots w) he (Sum.inr 0) y
    simpa [spectralValues] using this
  have hres (y : CoordinateIndex n → ℂ) :
      p.toLinearMap ((complexRect (faceMatrix n)).mulVec y)=b.coord (Sum.inr 0) y :=
    left_restriction _ _ (faceMatrix n) hA w hw roots hn b he (b.coord (Sum.inr 0)) hcoord
      (by simp [Module.Basis.coord_apply]) p.toLinearMap hp hpv y
  obtain ⟨e11,e20⟩ := resolvent_equations_transport _ _ (faceMatrix n) hA _ _ hT w _ h11 h20
    h11eq h20eq
  refine ⟨?_,?_⟩
  · rw [← coefficient_eq_resolventCoefficient p _ _ _ w
      (det_ne_zero_of_injective _ hA') (secondShift_det_ne_zero_of_injective _ w hS') _ _ e11 e20]
    exact coefficient_transport _ _ (faceMatrix n) hT _ _ hres _ _ _
  · rw [complex_intertwining _ _ (faceMatrix n) hD]
    exact hres _

/-! ### Small positive load -/

/-- Along any continuous critical data starting from the actual zero-load data,
the actual child source has genuinely invertible zero and second-harmonic
operators, negative `Re G` and negative crossing for all small positive loads
(step 5/6). The continued data are explicit inputs (B's supplier). -/
theorem eventual_strict_signs {n : ℕ} {σ : Type*} [DecidableEq σ]
    (offset slope : Rates n) (x : PhosphorylationSharpness.State n) (κ r w : ℝ) (hw : 0<w)
    (roots : σ → ℝ) (hn : ∀ i, roots i<0)
    (b : Module.Basis (σ ⊕ Fin 2) ℂ (CoordinateIndex n → ℂ))
    (he : ∀ i, (complexMatrix (sourceMatrix offset x+r • sourceMatrix slope x)).mulVec (b i)=
      spectralValues roots w i • b i)
    (h11 h20 : CoordinateIndex n → ℂ)
    (h11eq : (complexMatrix (sourceMatrix offset x+r • sourceMatrix slope x)).mulVec h11=
      complexBilinear (sourceTensor offset+r • sourceTensor slope) (b (Sum.inr 0))
        (conjugateVector (b (Sum.inr 0))))
    (h20eq : (2*Complex.I*(w:ℂ)) • h20-
      (complexMatrix (sourceMatrix offset x+r • sourceMatrix slope x)).mulVec h20=
      complexBilinear (sourceTensor offset+r • sourceTensor slope) (b (Sum.inr 0)) (b (Sum.inr 0)))
    (hG : (coefficient (b.coord (Sum.inr 0)) (sourceTensor offset+r • sourceTensor slope)
      (b (Sum.inr 0)) h11 h20).re<0)
    (hcross : (b.coord (Sum.inr 0)
      ((complexMatrix (sourceMatrix slope x)).mulVec (b (Sum.inr 0)))).re<0)
    (R : ℝ → ℝ) (q : ℝ → CoordinateIndex (n+1) → ℂ)
    (p : ℝ → (CoordinateIndex (n+1) → ℂ) →L[ℂ] ℂ) (ω : ℝ → ℝ)
    (hR : ContinuousAt R 0) (hq : ContinuousAt q 0) (hpc : ContinuousAt p 0)
    (hω : ContinuousAt ω 0) (hR0 : R 0=r)
    (hq0 : q 0=(complexRect (faceMatrix n)).mulVec (b (Sum.inr 0))) (hω0 : ω 0=w)
    (hp : ∀ y, p 0 ((complexMatrix (childOperator offset slope x κ 0 r)).mulVec y)=
      (Complex.I*(w:ℂ))*p 0 y)
    (hpv : p 0 ((complexRect (faceMatrix n)).mulVec (b (Sum.inr 0)))=1)
    (hA' : Function.Injective (complexMatrix (childOperator offset slope x κ 0 r)).mulVecLin)
    (hS' : Function.Injective ((2*Complex.I*(w:ℂ)) •
      (LinearMap.id : (CoordinateIndex (n+1) → ℂ) →ₗ[ℂ] (CoordinateIndex (n+1) → ℂ))-
        (complexMatrix (childOperator offset slope x κ 0 r)).mulVecLin)) :
    ∃ δ>0, ∀ ε, 0<ε → ε<δ →
      (complexMatrix (childOperator offset slope x κ ε (R ε))).det ≠ 0 ∧
      (secondShift (childOperator offset slope x κ ε (R ε)) (ω ε)).det ≠ 0 ∧
      (resolventCoefficient (p ε) (childOperator offset slope x κ ε (R ε))
        (childTensor offset slope x κ ε (R ε)) (q ε) (ω ε)).re<0 ∧
      (p ε ((complexMatrix (childDerivative slope x ε)).mulVec (q ε))).re<0 := by
  obtain ⟨hGeq,hCeq⟩ := zero_load_coefficient offset slope x κ r w hw roots hn b he h11 h20
    h11eq h20eq (p 0) hp hpv hA' hS'
  have hM := childOperator_continuousAt offset slope x κ hR
  have hT := childTensor_continuousAt offset slope x κ hR
  have hD := childDerivative_continuousAt slope x
  have hM0 : childOperator offset slope x κ 0 (R 0)=childOperator offset slope x κ 0 r := by
    rw [hR0]
  have hT0 : childTensor offset slope x κ 0 (R 0)=childTensor offset slope x κ 0 r := by
    rw [hR0]
  have h0 : (complexMatrix (childOperator offset slope x κ 0 (R 0))).det ≠ 0 := by
    rw [hM0]; exact det_ne_zero_of_injective _ hA'
  have h2 : (secondShift (childOperator offset slope x κ 0 (R 0)) (ω 0)).det ≠ 0 := by
    rw [hM0,hω0]; exact secondShift_det_ne_zero_of_injective _ w hS'
  have hG0 : (resolventCoefficient (p 0) (childOperator offset slope x κ 0 (R 0))
      (childTensor offset slope x κ 0 (R 0)) (q 0) (ω 0)).re<0 := by
    rw [hM0,hT0,hq0,hω0,hGeq]; exact hG
  have hC0 : (p 0 ((complexMatrix (childDerivative slope x 0)).mulVec (q 0))).re<0 := by
    rw [hq0,hCeq]; exact hcross
  have hev := (eventually_invertible hM hω h0 h2).and
    ((eventually_coefficient_negative hpc hM hT hq hω h0 h2 hG0).and
      (eventually_crossing_negative hpc hD hq hC0))
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ,hδ,fun ε hε hεδ => ?_⟩
  have hd : dist ε 0<δ := by
    rw [Real.dist_eq,sub_zero,abs_of_pos hε]
    exact hεδ
  obtain ⟨⟨a1,a2⟩,a3,a4⟩ := hball hd
  exact ⟨a1,a2,a3,a4⟩

/-! ### Genuine zero-load child invertibility from the actual block structure

The three new rows of the actual zero-load child Jacobian are computed from
the literal linear term: they are exactly `κK` in the new coordinates, with no
dependence on the old coordinates (the upper-right coupling `U` is untouched).
Together with the parent resolvents this proves genuine injectivity of the
child zero and second-harmonic operators, without any child eigenbasis. -/

/-- The appended coordinates: new substrate, new kinase and phosphatase complexes. -/
abbrev sNew (n : ℕ) : CoordinateIndex (n+1) := Sum.inl (Fin.last n)
abbrev cNew (n : ℕ) : CoordinateIndex (n+1) := Sum.inr (Sum.inl (Fin.last n))
abbrev dNew (n : ℕ) : CoordinateIndex (n+1) := Sum.inr (Sum.inr (Fin.last n))

/-- The face embedding of coordinate indices. -/
def faceIndex (n : ℕ) : CoordinateIndex n → CoordinateIndex (n+1) :=
  Sum.map Fin.castSucc (Sum.map Fin.castSucc Fin.castSucc)

theorem faceIndex_injective (n : ℕ) : Function.Injective (faceIndex n) :=
  Sum.map_injective.mpr ⟨Fin.castSucc_injective n,
    Sum.map_injective.mpr ⟨Fin.castSucc_injective n,Fin.castSucc_injective n⟩⟩

theorem last_ne_castSucc {n : ℕ} (j : Fin n) : Fin.last n ≠ Fin.castSucc j :=
  fun h => Fin.castSucc_ne_last j h.symm

theorem faceMatrix_apply {n : ℕ} (i : CoordinateIndex (n+1)) (j : CoordinateIndex n) :
    faceMatrix n i j=if i=faceIndex n j then 1 else 0 := by
  rw [faceMatrix,LinearMap.toMatrix'_apply,coordinateFace_apply]
  rcases i with i | (i | i) <;> refine Fin.lastCases ?_ (fun i => ?_) i <;>
    rcases j with j | (j | j) <;>
    simp [faceInclusion,appendReduced,faceIndex,last_ne_castSucc,Fin.castSucc_inj,Pi.single_apply]

theorem face_mulVec_index {n : ℕ} (u : CoordinateIndex n → ℂ) (j : CoordinateIndex n) :
    (complexRect (faceMatrix n)).mulVec u (faceIndex n j)=u j := by
  simp only [Matrix.mulVec,dotProduct,complexRect,faceMatrix_apply,
    (faceIndex_injective n).eq_iff]
  rw [Finset.sum_eq_single j]
  · simp
  · intro c _ hc
    have hjc : ¬j=c := fun h => hc h.symm
    simp [hjc]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem face_mulVec_normal {n : ℕ} (u : CoordinateIndex n → ℂ) (i : CoordinateIndex (n+1))
    (hi : ∀ j, i ≠ faceIndex n j) : (complexRect (faceMatrix n)).mulVec u i=0 := by
  simp [Matrix.mulVec,dotProduct,complexRect,faceMatrix_apply,hi]

/-- A child vector with vanishing new coordinates is the embedded restriction. -/
theorem face_of_normal_zero {n : ℕ} (z : CoordinateIndex (n+1) → ℂ)
    (hs : z (sNew n)=0) (hc : z (cNew n)=0) (hd : z (dNew n)=0) :
    z=(complexRect (faceMatrix n)).mulVec (fun j => z (faceIndex n j)) := by
  funext i
  rcases i with i | (i | i) <;> refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [face_mulVec_normal _ _ (by rintro (j | j | j) <;> simp [faceIndex,last_ne_castSucc])]
    exact hs
  · exact (face_mulVec_index (fun j => z (faceIndex n j)) (Sum.inl i)).symm
  · rw [face_mulVec_normal _ _ (by rintro (j | j | j) <;> simp [faceIndex,last_ne_castSucc])]
    exact hc
  · exact (face_mulVec_index (fun j => z (faceIndex n j)) (Sum.inr (Sum.inl i))).symm
  · rw [face_mulVec_normal _ _ (by rintro (j | j | j) <;> simp [faceIndex,last_ne_castSucc])]
    exact hd
  · exact (face_mulVec_index (fun j => z (faceIndex n j)) (Sum.inr (Sum.inr i))).symm

/-- The three new rows of the literal zero-load linear term. -/
theorem normal_linear_rows {n : ℕ} (k : Rates n) (κ α : ℝ)
    (x : PhosphorylationSharpness.State n) (y : ReducedState (n+1)) :
    (linearTerm (zeroRates k κ α) (zeroState x) y).2.1 (Fin.last n)=-(2*κ)*y.2.1 (Fin.last n) ∧
    (linearTerm (zeroRates k κ α) (zeroState x) y).1 (Fin.last n)=
      κ*y.2.1 (Fin.last n)-α*x.F*y.1 (Fin.last n)+κ*y.2.2 (Fin.last n) ∧
    (linearTerm (zeroRates k κ α) (zeroState x) y).2.2 (Fin.last n)=
      α*x.F*y.1 (Fin.last n)-2*κ*y.2.2 (Fin.last n) := by
  have hS : (zeroState x).S (Fin.last n).succ=0 := by
    simp [zeroState,appendState,Fin.succ_last]
  have hT : (tangent y).S (Fin.last n).succ=y.1 (Fin.last n) := by
    simp [tangent,chart]
  refine ⟨?_,?_,?_⟩
  · simp [linearTerm,assemble,linearKinase,zeroRates,appendScaledRates,tangent,chart]
    ring
  · simp only [linearTerm,assemble]
    rw [Finset.sum_eq_single (Fin.last n)]
    · have h1 : (Fin.last n).castSucc ≠ (Fin.last n).succ := by
        rw [Fin.succ_last]; exact Fin.castSucc_ne_last _
      simp only [sourceRow,if_neg h1,zero_add,linearPhosphatase,hS,hT]
      simp [zeroRates,appendScaledRates,zeroState,appendState,tangent,chart]
      ring
    · intro i _ hi
      have h1 : i.castSucc ≠ (Fin.last n).succ := by
        rw [Fin.succ_last]; exact Fin.castSucc_ne_last _
      have h2 : i.succ ≠ (Fin.last n).succ := fun h => hi (Fin.succ_inj.mp h)
      simp only [sourceRow,if_neg h1,if_neg h2,add_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [linearTerm,assemble,linearPhosphatase,hS,hT]
    simp [zeroRates,appendScaledRates,zeroState,appendState,tangent,chart]
    ring

theorem coordinate_normal_rows {n : ℕ} (k : Rates n) (κ α : ℝ)
    (x : PhosphorylationSharpness.State n) (y : CoordinateState (n+1)) :
    (sourceMatrix (zeroRates k κ α) (zeroState x)).mulVec y (cNew n)=-(2*κ)*y (cNew n) ∧
    (sourceMatrix (zeroRates k κ α) (zeroState x)).mulVec y (sNew n)=
      κ*y (cNew n)-α*x.F*y (sNew n)+κ*y (dNew n) ∧
    (sourceMatrix (zeroRates k κ α) (zeroState x)).mulVec y (dNew n)=
      α*x.F*y (sNew n)-2*κ*y (dNew n) := by
  obtain ⟨h1,h2,h3⟩ := normal_linear_rows k κ α x (fromCoordinates (n+1) y)
  simp only [sourceMatrix_action,coordinateLinear_apply,toCoordinates_apply,
    coordinateEquiv_apply_s,coordinateEquiv_apply_c,coordinateEquiv_apply_d]
  refine ⟨?_,?_,?_⟩
  · rw [h1]; simp
  · rw [h2]; simp
  · rw [h3]; simp

/-- The actual zero-load child operator has new rows exactly `κK`, for every
kinetic parameter (the slope contributes nothing to the new rows). -/
theorem childOperator_normal_rows {n : ℕ} (offset slope : Rates n)
    (x : PhosphorylationSharpness.State n) (κ r : ℝ) (hF : x.F ≠ 0)
    (y : CoordinateState (n+1)) :
    (childOperator offset slope x κ 0 r).mulVec y (cNew n)=-(2*κ)*y (cNew n) ∧
    (childOperator offset slope x κ 0 r).mulVec y (sNew n)=
      κ*y (cNew n)-κ*y (sNew n)+κ*y (dNew n) ∧
    (childOperator offset slope x κ 0 r).mulVec y (dNew n)=
      κ*y (sNew n)-2*κ*y (dNew n) := by
  unfold childOperator
  rw [childOffset_zero,childState_zero,childSlope_eq]
  obtain ⟨a1,a2,a3⟩ := coordinate_normal_rows offset κ (κ/x.F) x y
  obtain ⟨b1,b2,b3⟩ := coordinate_normal_rows slope 0 0 x y
  have hk : κ/x.F*x.F=κ := div_mul_cancel₀ κ hF
  simp only [Matrix.add_mulVec,Matrix.smul_mulVec,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    a1,a2,a3,b1,b2,b3,hk]
  refine ⟨?_,?_,?_⟩ <;> ring

theorem complex_decompose {ι : Type*} (z : ι → ℂ) :
    z=complexify (GenericComplexification.realPart z)+Complex.I • complexify (GenericComplexification.imagPart z) := by
  funext i
  simp only [Pi.add_apply,Pi.smul_apply,complexify_apply,GenericComplexification.realPart,GenericComplexification.imagPart,smul_eq_mul]
  rw [mul_comm]
  exact (Complex.re_add_im (z i)).symm

theorem complex_childOperator_normal_rows {n : ℕ} (offset slope : Rates n)
    (x : PhosphorylationSharpness.State n) (κ r : ℝ) (hF : x.F ≠ 0)
    (z : CoordinateIndex (n+1) → ℂ) :
    (complexMatrix (childOperator offset slope x κ 0 r)).mulVec z (cNew n)=
      -(2*(κ:ℂ))*z (cNew n) ∧
    (complexMatrix (childOperator offset slope x κ 0 r)).mulVec z (sNew n)=
      (κ:ℂ)*z (cNew n)-(κ:ℂ)*z (sNew n)+(κ:ℂ)*z (dNew n) ∧
    (complexMatrix (childOperator offset slope x κ 0 r)).mulVec z (dNew n)=
      (κ:ℂ)*z (sNew n)-2*(κ:ℂ)*z (dNew n) := by
  obtain ⟨a1,a2,a3⟩ := childOperator_normal_rows offset slope x κ r hF (GenericComplexification.realPart z)
  obtain ⟨b1,b2,b3⟩ := childOperator_normal_rows offset slope x κ r hF (GenericComplexification.imagPart z)
  have hz := complex_decompose z
  have hM : (complexMatrix (childOperator offset slope x κ 0 r)).mulVec z=
      complexify ((childOperator offset slope x κ 0 r).mulVec (GenericComplexification.realPart z))+
        Complex.I • complexify ((childOperator offset slope x κ 0 r).mulVec (GenericComplexification.imagPart z)) := by
    conv_lhs => rw [hz]
    rw [Matrix.mulVec_add,Matrix.mulVec_smul,← complexify_action,← complexify_action]
  have hzi (i : CoordinateIndex (n+1)) :
      z i=((GenericComplexification.realPart z i:ℝ):ℂ)+Complex.I*((GenericComplexification.imagPart z i:ℝ):ℂ) :=
    congrFun hz i
  rw [hM,hzi (cNew n),hzi (sNew n),hzi (dNew n)]
  simp only [Pi.add_apply,Pi.smul_apply,complexify_apply,smul_eq_mul,a1,a2,a3,b1,b2,b3]
  push_cast
  refine ⟨?_,?_,?_⟩ <;> ring

/-- Genuine injectivity of `λ-A'` for the actual zero-load child operator
from injectivity of the parent `λ-A` and nonresonance of `λ` with `κK`. -/
theorem child_shift_injective {n : ℕ} (offset slope : Rates n)
    (x : PhosphorylationSharpness.State n) (κ r : ℝ) (hF : x.F ≠ 0) (lam : ℂ)
    (h1 : lam+2*(κ:ℂ) ≠ 0) (h2 : lam^2+3*(κ:ℂ)*lam+(κ:ℂ)^2 ≠ 0)
    (hpar : ∀ u, lam • u-(complexMatrix (sourceMatrix offset x+r • sourceMatrix slope x)).mulVec u=0 →
      u=0)
    (z : CoordinateIndex (n+1) → ℂ)
    (hz : lam • z-(complexMatrix (childOperator offset slope x κ 0 r)).mulVec z=0) : z=0 := by
  obtain ⟨r1,r2,r3⟩ := complex_childOperator_normal_rows offset slope x κ r hF z
  have e1 := congrFun hz (cNew n)
  have e2 := congrFun hz (sNew n)
  have e3 := congrFun hz (dNew n)
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,r1,r2,r3] at e1 e2 e3
  have hc : z (cNew n)=0 := by
    have : (lam+2*(κ:ℂ))*z (cNew n)=0 := by linear_combination e1
    exact (mul_eq_zero.mp this).resolve_left h1
  rw [hc] at e2
  have hs : z (sNew n)=0 := by
    have : (lam^2+3*(κ:ℂ)*lam+(κ:ℂ)^2)*z (sNew n)=0 := by
      linear_combination (lam+2*(κ:ℂ))*e2+(κ:ℂ)*e3
    exact (mul_eq_zero.mp this).resolve_left h2
  have hd : z (dNew n)=0 := by
    have : (lam^2+3*(κ:ℂ)*lam+(κ:ℂ)^2)*z (dNew n)=0 := by
      linear_combination (κ:ℂ)*e2+(lam+(κ:ℂ))*e3
    exact (mul_eq_zero.mp this).resolve_left h2
  have hface := face_of_normal_zero z hs hc hd
  set u := fun j => z (faceIndex n j)
  obtain ⟨hA,-,-⟩ := zero_load_face offset slope x κ r
  have hPu : (complexRect (faceMatrix n)).mulVec
      (lam • u-(complexMatrix (sourceMatrix offset x+r • sourceMatrix slope x)).mulVec u)=0 := by
    rw [Matrix.mulVec_sub,Matrix.mulVec_smul,← complex_intertwining _ _ (faceMatrix n) hA,← hface]
    exact hz
  have hw : lam • u-(complexMatrix (sourceMatrix offset x+r • sourceMatrix slope x)).mulVec u=0 := by
    funext j
    have := congrFun hPu (faceIndex n j)
    rw [face_mulVec_index] at this
    exact this
  have hu : u=0 := hpar u hw
  rw [hface,hu,Matrix.mulVec_zero]

/-- Genuine zero-load child invertibility (step 2), from the parent spectral
basis and the actual new rows. No child basis or assumed inverse is used. -/
theorem zero_load_child_injective {n : ℕ} {σ : Type*} [Fintype σ]
    (offset slope : Rates n) (x : PhosphorylationSharpness.State n) (κ r w : ℝ)
    (hκ : 0<κ) (hw : 0<w) (hF : x.F ≠ 0)
    (roots : σ → ℝ) (hn : ∀ i, roots i<0)
    (b : Module.Basis (σ ⊕ Fin 2) ℂ (CoordinateIndex n → ℂ))
    (he : ∀ i, (complexMatrix (sourceMatrix offset x+r • sourceMatrix slope x)).mulVec (b i)=
      spectralValues roots w i • b i) :
    Function.Injective (complexMatrix (childOperator offset slope x κ 0 r)).mulVecLin ∧
    Function.Injective ((2*Complex.I*(w:ℂ)) •
      (LinearMap.id : (CoordinateIndex (n+1) → ℂ) →ₗ[ℂ] (CoordinateIndex (n+1) → ℂ))-
        (complexMatrix (childOperator offset slope x κ 0 r)).mulVecLin) := by
  obtain ⟨hB0,hB2⟩ := GenericResolvents.resolvents_bijective
    (complexMatrix (sourceMatrix offset x+r • sourceMatrix slope x)).mulVecLin w roots b hn hw he
  have hκc : (κ:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hκ
  constructor
  · rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
    intro z hz
    apply child_shift_injective offset slope x κ r hF 0
    · simpa using mul_ne_zero two_ne_zero hκc
    · simpa using pow_ne_zero 2 hκc
    · intro u hu
      apply hB0.1
      simp only [Matrix.mulVecLin_apply,map_zero]
      simpa using hu
    · simpa using hz
  · rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']
    intro z hz
    apply child_shift_injective offset slope x κ r hF (2*Complex.I*(w:ℂ))
    · intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith
    · intro h0
      have h' : (((κ^2-4*w^2:ℝ)):ℂ)+((6*κ*w:ℝ):ℂ)*Complex.I=0 := by
        push_cast
        linear_combination h0-4*(w:ℂ)^2*Complex.I_sq
      have := congrArg Complex.im h'
      simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
        Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_add,Complex.zero_im] at this
      nlinarith [mul_pos hκ hw]
    · intro u hu
      apply hB2.1
      simp only [GenericResolvents.secondHarmonic,LinearMap.sub_apply,LinearMap.smul_apply,
        LinearMap.id_apply,Matrix.mulVecLin_apply,map_zero]
      exact hu
    · simpa only [LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,
        Matrix.mulVecLin_apply] using hz

/-- Final actual-source export: zero-load child invertibility is now proved,
and only the continued critical data (B's supplier) remain as inputs. -/
theorem eventual_strict_signs_actual {n : ℕ} {σ : Type*} [Fintype σ] [DecidableEq σ]
    (offset slope : Rates n) (x : PhosphorylationSharpness.State n) (κ r w : ℝ)
    (hκ : 0<κ) (hw : 0<w) (hF : x.F ≠ 0)
    (roots : σ → ℝ) (hn : ∀ i, roots i<0)
    (b : Module.Basis (σ ⊕ Fin 2) ℂ (CoordinateIndex n → ℂ))
    (he : ∀ i, (complexMatrix (sourceMatrix offset x+r • sourceMatrix slope x)).mulVec (b i)=
      spectralValues roots w i • b i)
    (h11 h20 : CoordinateIndex n → ℂ)
    (h11eq : (complexMatrix (sourceMatrix offset x+r • sourceMatrix slope x)).mulVec h11=
      complexBilinear (sourceTensor offset+r • sourceTensor slope) (b (Sum.inr 0))
        (conjugateVector (b (Sum.inr 0))))
    (h20eq : (2*Complex.I*(w:ℂ)) • h20-
      (complexMatrix (sourceMatrix offset x+r • sourceMatrix slope x)).mulVec h20=
      complexBilinear (sourceTensor offset+r • sourceTensor slope) (b (Sum.inr 0)) (b (Sum.inr 0)))
    (hG : (coefficient (b.coord (Sum.inr 0)) (sourceTensor offset+r • sourceTensor slope)
      (b (Sum.inr 0)) h11 h20).re<0)
    (hcross : (b.coord (Sum.inr 0)
      ((complexMatrix (sourceMatrix slope x)).mulVec (b (Sum.inr 0)))).re<0)
    (R : ℝ → ℝ) (q : ℝ → CoordinateIndex (n+1) → ℂ)
    (p : ℝ → (CoordinateIndex (n+1) → ℂ) →L[ℂ] ℂ) (ω : ℝ → ℝ)
    (hR : ContinuousAt R 0) (hq : ContinuousAt q 0) (hpc : ContinuousAt p 0)
    (hω : ContinuousAt ω 0) (hR0 : R 0=r)
    (hq0 : q 0=(complexRect (faceMatrix n)).mulVec (b (Sum.inr 0))) (hω0 : ω 0=w)
    (hp : ∀ y, p 0 ((complexMatrix (childOperator offset slope x κ 0 r)).mulVec y)=
      (Complex.I*(w:ℂ))*p 0 y)
    (hpv : p 0 ((complexRect (faceMatrix n)).mulVec (b (Sum.inr 0)))=1) :
    ∃ δ>0, ∀ ε, 0<ε → ε<δ →
      (complexMatrix (childOperator offset slope x κ ε (R ε))).det ≠ 0 ∧
      (secondShift (childOperator offset slope x κ ε (R ε)) (ω ε)).det ≠ 0 ∧
      (resolventCoefficient (p ε) (childOperator offset slope x κ ε (R ε))
        (childTensor offset slope x κ ε (R ε)) (q ε) (ω ε)).re<0 ∧
      (p ε ((complexMatrix (childDerivative slope x ε)).mulVec (q ε))).re<0 := by
  obtain ⟨hA',hS'⟩ := zero_load_child_injective offset slope x κ r w hκ hw hF roots hn b he
  exact eventual_strict_signs offset slope x κ r w hw roots hn b he h11 h20 h11eq h20eq hG hcross
    R q p ω hR hq hpc hω hR0 hq0 hω0 hp hpv hA' hS'

/-- The positive-load output in the exact form consumed by
`GenericClosedBranchCurvature.closed_branch_parameter_second_derivative_negative`:
for every small positive load, every actual child closed family on the continued
critical data whose left functional is the continued `p` has genuinely injective
zero/second-harmonic operators, negative crossing, and negative `Re G` for ANY
genuine resolvent solutions. -/
theorem curvature_inputs_actual {n : ℕ} {σ : Type*} [Fintype σ] [DecidableEq σ]
    (offset slope : Rates n) (x : PhosphorylationSharpness.State n) (κ r w : ℝ)
    (hκ : 0<κ) (hw : 0<w) (hF : x.F ≠ 0)
    (roots : σ → ℝ) (hn : ∀ i, roots i<0)
    (b : Module.Basis (σ ⊕ Fin 2) ℂ (CoordinateIndex n → ℂ))
    (he : ∀ i, (complexMatrix (sourceMatrix offset x+r • sourceMatrix slope x)).mulVec (b i)=
      spectralValues roots w i • b i)
    (h11 h20 : CoordinateIndex n → ℂ)
    (h11eq : (complexMatrix (sourceMatrix offset x+r • sourceMatrix slope x)).mulVec h11=
      complexBilinear (sourceTensor offset+r • sourceTensor slope) (b (Sum.inr 0))
        (conjugateVector (b (Sum.inr 0))))
    (h20eq : (2*Complex.I*(w:ℂ)) • h20-
      (complexMatrix (sourceMatrix offset x+r • sourceMatrix slope x)).mulVec h20=
      complexBilinear (sourceTensor offset+r • sourceTensor slope) (b (Sum.inr 0)) (b (Sum.inr 0)))
    (hG : (coefficient (b.coord (Sum.inr 0)) (sourceTensor offset+r • sourceTensor slope)
      (b (Sum.inr 0)) h11 h20).re<0)
    (hcross : (b.coord (Sum.inr 0)
      ((complexMatrix (sourceMatrix slope x)).mulVec (b (Sum.inr 0)))).re<0)
    (R : ℝ → ℝ) (q : ℝ → CoordinateIndex (n+1) → ℂ)
    (p : ℝ → (CoordinateIndex (n+1) → ℂ) →L[ℂ] ℂ) (ω : ℝ → ℝ)
    (hR : ContinuousAt R 0) (hq : ContinuousAt q 0) (hpc : ContinuousAt p 0)
    (hω : ContinuousAt ω 0) (hR0 : R 0=r)
    (hq0 : q 0=(complexRect (faceMatrix n)).mulVec (b (Sum.inr 0))) (hω0 : ω 0=w)
    (hp : ∀ y, p 0 ((complexMatrix (childOperator offset slope x κ 0 r)).mulVec y)=
      (Complex.I*(w:ℂ))*p 0 y)
    (hpv : p 0 ((complexRect (faceMatrix n)).mulVec (b (Sum.inr 0)))=1) :
    ∃ δ>0, ∀ ε, 0<ε → ε<δ →
      ∀ C : GenericClosedPaths.ClosedPathFamily
        (sourceMatrix (childOffset offset x κ ε) (childState x ε)) (childDerivative slope x ε)
        (GenericQuadraticTensor.pathField (fun s => childTensor offset slope x κ ε s))
        (R ε) (ω ε) (q ε),
      C.left=(p ε).toLinearMap →
      Function.Injective (complexMatrix (childOperator offset slope x κ ε (R ε))).mulVecLin ∧
      Function.Injective ((2*Complex.I*(ω ε:ℂ)) •
        (LinearMap.id : (CoordinateIndex (n+1) → ℂ) →ₗ[ℂ] (CoordinateIndex (n+1) → ℂ))-
          (complexMatrix (childOperator offset slope x κ ε (R ε))).mulVecLin) ∧
      (C.left ((complexMatrix (childDerivative slope x ε)).mulVec (q ε))).re<0 ∧
      ∀ k11 k20 : CoordinateIndex (n+1) → ℂ,
        (complexMatrix (childOperator offset slope x κ ε (R ε))).mulVec k11=
          complexBilinear (childTensor offset slope x κ ε (R ε)) (q ε) (conjugateVector (q ε)) →
        (2*Complex.I*(ω ε:ℂ)) • k20-(complexMatrix (childOperator offset slope x κ ε (R ε))).mulVec k20=
          complexBilinear (childTensor offset slope x κ ε (R ε)) (q ε) (q ε) →
        (GenericClosedBranchCurvature.branchCoefficient C k11 k20).re<0 := by
  obtain ⟨δ,hδ,hsign⟩ := eventual_strict_signs_actual offset slope x κ r w hκ hw hF roots hn b he
    h11 h20 h11eq h20eq hG hcross R q p ω hR hq hpc hω hR0 hq0 hω0 hp hpv
  refine ⟨δ,hδ,fun ε hε hεδ C hC => ?_⟩
  obtain ⟨d0,d2,hGε,hCε⟩ := hsign ε hε hεδ
  have i0 : Function.Injective (complexMatrix (childOperator offset slope x κ ε (R ε))).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr d0))
  have i2 : Function.Injective (secondShift (childOperator offset slope x κ ε (R ε)) (ω ε)).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr d2))
  refine ⟨i0,?_,?_,?_⟩
  · intro a c hac
    apply i2
    simp only [LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,
      Matrix.mulVecLin_apply] at hac
    rw [secondShift_mulVec,secondShift_mulVec]
    exact hac
  · rw [hC]
    exact hCε
  · intro k11 k20 k11eq k20eq
    have hb : GenericClosedBranchCurvature.branchCoefficient C k11 k20=
        coefficient (p ε).toLinearMap (childTensor offset slope x κ ε (R ε)) (q ε) k11 k20 := by
      rw [branchCoefficient_eq,hC]
    rw [hb,coefficient_eq_resolventCoefficient (p ε) _ _ (q ε) (ω ε) d0 d2 k11 k20 k11eq k20eq]
    exact hGε

end
end ThreeSitePhosphorylation.AddedSiteCrossingTransport
