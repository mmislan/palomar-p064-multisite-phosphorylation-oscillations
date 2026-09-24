import proofs.ThreeSitePhosphorylation.MultisiteTensor
import proofs.ThreeSitePhosphorylation.GenericTensorDerivative
import proofs.ThreeSitePhosphorylation.ScaledJacobianBlock
import proofs.ThreeSitePhosphorylation.ScaledJointSource

/-! The actual source matrix of the loaded added-site family, its joint
smoothness in (load, kinetic parameter), and its zero-load block form.
The matrix is identified with the Frechet derivative of the literal
centered chemical field; the upper-right coupling is retained. -/
namespace ThreeSitePhosphorylation.AddedSiteSourceMatrix
noncomputable section
open PhosphorylationSharpness MultisiteChart MultisiteSource MultisiteCenteredFace
open ScaledMultisiteSource MultisiteSplit MultisiteCoordinates MultisiteTensor
open MultisiteNormalDerivative ScaledNormalJacobian ScaledJacobianBlock ScaledJointSource
set_option maxHeartbeats 800000

/-- The literal centered coordinate field has the source matrix as its
derivative at the equilibrium chart point. No equilibrium is assumed. -/
theorem coordinateField_hasFDerivAt {n : ℕ} (k : Rates n) (x : State n) :
    HasFDerivAt (coordinateField k x)
      (Matrix.toLin' (sourceMatrix k x)).toContinuousLinearMap 0 := by
  let L := (Matrix.toLin' (sourceMatrix k x)).toContinuousLinearMap
  have hq := GenericTensorDerivative.field_hasFDerivAt (fun _ : ℝ => sourceTensor k) 0
    (fun i j l => sourceTensor_symmetric k i j l) 0
  have hsum := ((hasFDerivAt_const (toCoordinates n (project (field k x)))
    (0 : CoordinateState n)).add L.hasFDerivAt).add hq
  have hfun : coordinateField k x = fun y => toCoordinates n (project (field k x)) +
      L y + GenericQuadraticTensor.field (fun _ : ℝ => sourceTensor k) 0 y := by
    funext y
    rw [coordinateField_exact,GenericTensorBilinear.field_eq_half_bilinear]
    simp [L,Matrix.toLin'_apply]
  have h0 : (0 : CoordinateState n →L[ℝ] CoordinateState n)+L+
      GenericTensorDerivative.realContinuousBilinear (sourceTensor k) 0=L := by simp
  rw [h0] at hsum
  rw [hfun]
  exact hsum

/-- The same identification on the actual reduced state space. -/
theorem centeredJacobian_eq {n : ℕ} (k : Rates n) (x : State n) :
    centeredJacobian (totalE x) (totalF x) (totalS x) k (project x) =
      (fromCoordinates n).comp
        ((Matrix.toLin' (sourceMatrix k x)).toContinuousLinearMap.comp (toCoordinates n)) := by
  have hc : HasFDerivAt (coordinateField k x)
      (Matrix.toLin' (sourceMatrix k x)).toContinuousLinearMap (toCoordinates n 0) := by
    simpa only [map_zero] using coordinateField_hasFDerivAt k x
  have h := (fromCoordinates n).hasFDerivAt.comp (0 : ReducedState n)
    (hc.comp (0 : ReducedState n) (toCoordinates n).hasFDerivAt)
  have he : centeredField (totalE x) (totalF x) (totalS x) k (project x) =
      (fromCoordinates n) ∘ coordinateField k x ∘ (toCoordinates n) := by
    funext y
    simp [coordinateField]
  unfold centeredJacobian
  rw [he]
  exact h.fderiv

theorem sourceMatrix_mulVec {n : ℕ} (k : Rates n) (x : State n) (u : CoordinateState n) :
    (sourceMatrix k x).mulVec u =
      toCoordinates n (centeredJacobian (totalE x) (totalF x) (totalS x) k (project x)
        (fromCoordinates n u)) := by
  rw [centeredJacobian_eq]
  simp [Matrix.toLin'_apply]

/-- Source matrix of the loaded added-site family at (load, kinetic parameter). -/
def jointMatrix {n : ℕ} (k : ℝ → Rates n) (x : State n) (κ : ℝ) (p : ℝ × ℝ) :
    Matrix (CoordinateIndex (n+1)) (CoordinateIndex (n+1)) ℝ :=
  sourceMatrix (jointRates k x κ p) (appendState x p.1 (2*p.1) p.1)

theorem coordinateField_joint {n : ℕ} (k : ℝ → Rates n) (x : State n) (κ : ℝ)
    (p : ℝ × ℝ) (y : CoordinateState (n+1)) :
    coordinateField (jointRates k x κ p) (appendState x p.1 (2*p.1) p.1) y =
      toCoordinates (n+1) (jointField k x κ p (fromCoordinates (n+1) y)) := by
  obtain ⟨hE,hF,hS⟩ := append_totals x p.1 (2*p.1) p.1
  have hS' : totalS (appendState x p.1 (2*p.1) p.1)=totalS x+4*p.1 := by
    rw [hS]
    ring
  unfold coordinateField jointField
  rw [hE,hF,hS',project_appendState]
  rfl

theorem jointCoordinateField_smooth {n : ℕ} (k : ℝ → Rates n) (x : State n) (κ : ℝ)
    (hk : MultisiteSmoothField.RatesSmooth k) :
    ContDiff ℝ ⊤ (Function.uncurry (fun (p : ℝ × ℝ) (y : CoordinateState (n+1)) =>
      coordinateField (jointRates k x κ p) (appendState x p.1 (2*p.1) p.1) y)) := by
  have h := jointField_smooth k x κ hk
  have h2 := (toCoordinates (n+1)).contDiff.comp
    (h.comp (contDiff_fst.prodMk ((fromCoordinates (n+1)).contDiff.comp contDiff_snd)))
  convert h2 using 1
  funext q
  exact coordinateField_joint k x κ q.1 q.2

theorem jointMatrix_mulVec_fderiv {n : ℕ} (k : ℝ → Rates n) (x : State n) (κ : ℝ)
    (p : ℝ × ℝ) (y : CoordinateState (n+1)) :
    (jointMatrix k x κ p).mulVec y =
      fderiv ℝ (coordinateField (jointRates k x κ p) (appendState x p.1 (2*p.1) p.1)) 0 y := by
  rw [(coordinateField_hasFDerivAt _ _).fderiv]
  simp [jointMatrix,Matrix.toLin'_apply]

/-- Every entry of the actual loaded source matrix is smooth jointly in load
and kinetic parameter. Smoothness is derived from the chemical field. -/
theorem jointMatrix_entry_smooth {n : ℕ} (k : ℝ → Rates n) (x : State n) (κ : ℝ)
    (hk : MultisiteSmoothField.RatesSmooth k) (i j : CoordinateIndex (n+1)) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => jointMatrix k x κ p i j) := by
  have hd : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => fderiv ℝ (coordinateField (jointRates k x κ p)
      (appendState x p.1 (2*p.1) p.1)) 0 (Pi.single j (1:ℝ))) :=
    ContDiff.fderiv_apply (f := fun (p : ℝ × ℝ) (y : CoordinateState (n+1)) =>
      coordinateField (jointRates k x κ p) (appendState x p.1 (2*p.1) p.1) y)
      (jointCoordinateField_smooth k x κ hk) contDiff_const contDiff_const le_top
  have he : (fun p : ℝ × ℝ => jointMatrix k x κ p i j) =
      fun p => fderiv ℝ (coordinateField (jointRates k x κ p)
        (appendState x p.1 (2*p.1) p.1)) 0 (Pi.single j 1) i := by
    funext p
    rw [← jointMatrix_mulVec_fderiv,Matrix.mulVec_single_one]
    rfl
  rw [he]
  exact contDiff_pi.mp hd i

theorem jointMatrix_smooth {n : ℕ} (k : ℝ → Rates n) (x : State n) (κ : ℝ)
    (hk : MultisiteSmoothField.RatesSmooth k) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => fun i j => jointMatrix k x κ p i j) :=
  contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => jointMatrix_entry_smooth k x κ hk i j

/-- Coordinates of the added site in the order used by `splitContinuous`,
over an arbitrary scalar ring. Normal coordinates are ordered C,S,D. -/
def siteEmbedFun {R : Type*} (n : ℕ) (w : (CoordinateIndex n → R) × (Fin 3 → R)) :
    CoordinateIndex (n+1) → R :=
  Sum.elim (Fin.lastCases (w.2 1) (fun i => w.1 (Sum.inl i)))
    (Sum.elim (Fin.lastCases (w.2 0) (fun i => w.1 (Sum.inr (Sum.inl i))))
      (Fin.lastCases (w.2 2) (fun i => w.1 (Sum.inr (Sum.inr i)))))

def siteRestrictFun {R : Type*} (n : ℕ) (v : CoordinateIndex (n+1) → R) :
    (CoordinateIndex n → R) × (Fin 3 → R) :=
  (Sum.elim (fun i => v (Sum.inl i.castSucc))
    (Sum.elim (fun i => v (Sum.inr (Sum.inl i.castSucc)))
      (fun i => v (Sum.inr (Sum.inr i.castSucc)))),
    ![v (Sum.inr (Sum.inl (Fin.last n))),v (Sum.inl (Fin.last n)),
      v (Sum.inr (Sum.inr (Fin.last n)))])

/-- The added-site coordinate split as a linear equivalence. -/
def siteEquiv (R : Type*) [CommSemiring R] (n : ℕ) :
    ((CoordinateIndex n → R) × (Fin 3 → R)) ≃ₗ[R] (CoordinateIndex (n+1) → R) where
  toFun := siteEmbedFun n
  invFun := siteRestrictFun n
  left_inv w := by
    rcases w with ⟨u,z⟩
    apply Prod.ext
    · funext i
      rcases i with i | i | i <;> simp [siteEmbedFun,siteRestrictFun]
    · funext j
      fin_cases j <;> simp [siteEmbedFun,siteRestrictFun]
  right_inv v := by
    funext i
    rcases i with i | i | i <;> refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [siteEmbedFun,siteRestrictFun]
  map_add' w w' := by
    funext i
    rcases i with i | i | i <;> refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [siteEmbedFun]
  map_smul' a w := by
    funext i
    rcases i with i | i | i <;> refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [siteEmbedFun]

@[simp] theorem siteEquiv_apply {R : Type*} [CommSemiring R] (n : ℕ)
    (w : (CoordinateIndex n → R) × (Fin 3 → R)) : siteEquiv R n w = siteEmbedFun n w := rfl

/-- The real split coordinates are the literal chart split. -/
theorem siteEquiv_real {n : ℕ} (u : CoordinateState n) (z : Fin 3 → ℝ) :
    siteEquiv ℝ n (u,z) = toCoordinates (n+1) (splitContinuous n (fromCoordinates n u,z)) := by
  funext i
  rcases i with i | i | i <;> rfl

/-- The upper-right coupling of the actual zero-load source, in coordinates. -/
def upperCouplingCoordinates {n : ℕ} (k : ℝ → Rates n) (x : State n) (κ r : ℝ) :
    (Fin 3 → ℝ) →L[ℝ] CoordinateState n :=
  (toCoordinates n).comp (upperCoupling (totalE x) (totalF x) (totalS x) (k r) κ (project x))

theorem referenceF_project {n : ℕ} (x : State n) :
    referenceF (totalF x) (project x) = x.F :=
  congrArg PhosphorylationSharpness.State.F (chart_project x)

/-- Zero-load actual block form of the loaded source matrix, for every kinetic
parameter: the face is invariant with the parent matrix, the normal block is
kappa*K, and the upper-right coupling is the actual derived coupling. -/
theorem jointMatrix_zero_block {n : ℕ} (k : ℝ → Rates n) (x : State n) (κ r : ℝ)
    (hx : x.F ≠ 0) (u : CoordinateState n) (z : Fin 3 → ℝ) :
    (jointMatrix k x κ (0,r)).mulVec (siteEquiv ℝ n (u,z)) =
      siteEquiv ℝ n ((sourceMatrix (k r) x).mulVec u +
        upperCouplingCoordinates k x κ r z,κ • normalBlock z) := by
  have hf : referenceF (totalF x) (project x) ≠ 0 := by rw [referenceF_project]; exact hx
  have hrates : jointRates k x κ (0,r) =
      appendScaledRates (k r) κ 0 (κ/referenceF (totalF x) (project x)) := by
    rw [referenceF_project]
    simp [jointRates]
  have hstate : appendState x ((0,r) : ℝ × ℝ).1 (2*((0,r) : ℝ × ℝ).1) ((0,r) : ℝ × ℝ).1 =
      appendState x 0 0 0 := by simp
  obtain ⟨hE,hF,hS⟩ := append_totals x 0 0 0
  have hsplit := jacobian_split_apply (totalE x) (totalF x) (totalS x) (k r) κ (project x) hf
    (fromCoordinates n u) z
  let J := centeredJacobian (totalE x) (totalF x) (totalS x)
    (appendScaledRates (k r) κ 0 (κ/referenceF (totalF x) (project x)))
    (faceInclusion n (project x))
  have hJ : (jointMatrix k x κ (0,r)).mulVec (siteEquiv ℝ n (u,z)) =
      toCoordinates (n+1) (J (splitContinuous n (fromCoordinates n u,z))) := by
    unfold jointMatrix
    rw [sourceMatrix_mulVec,hrates,hstate,hE,hF,hS,siteEquiv_real]
    simp only [add_zero,project_appendState,
      ContinuousLinearEquiv.symm_apply_apply,fromCoordinates_apply,toCoordinates_apply]
    rfl
  rw [hJ]
  have hJ' : J (splitContinuous n (fromCoordinates n u,z)) =
      splitContinuous n (centeredJacobian (totalE x) (totalF x) (totalS x) (k r) (project x)
        (fromCoordinates n u) +
        upperCoupling (totalE x) (totalF x) (totalS x) (k r) κ (project x) z,κ • normalBlock z) := by
    have h2 := congrArg (splitContinuous n) hsplit
    rw [ContinuousLinearEquiv.apply_symm_apply] at h2
    exact h2
  rw [hJ',siteEquiv_real,sourceMatrix_mulVec]
  simp [upperCouplingCoordinates]

/-- Face invariance for every kinetic parameter. -/
theorem jointMatrix_zero_face {n : ℕ} (k : ℝ → Rates n) (x : State n) (κ r : ℝ)
    (hx : x.F ≠ 0) (u : CoordinateState n) :
    (jointMatrix k x κ (0,r)).mulVec (siteEquiv ℝ n (u,0)) =
      siteEquiv ℝ n ((sourceMatrix (k r) x).mulVec u,0) := by
  rw [jointMatrix_zero_block k x κ r hx u 0]
  simp

/-- The normal component of the actual zero-load matrix is kappa*K. -/
theorem jointMatrix_zero_normal {n : ℕ} (k : ℝ → Rates n) (x : State n) (κ r : ℝ)
    (hx : x.F ≠ 0) (u : CoordinateState n) (z : Fin 3 → ℝ) :
    ((siteEquiv ℝ n).symm ((jointMatrix k x κ (0,r)).mulVec (siteEquiv ℝ n (u,z)))).2 =
      κ • normalBlock z := by
  rw [jointMatrix_zero_block k x κ r hx u z,LinearEquiv.symm_apply_apply]

end
end ThreeSitePhosphorylation.AddedSiteSourceMatrix
