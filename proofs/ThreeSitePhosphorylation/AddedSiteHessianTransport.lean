import proofs.ThreeSitePhosphorylation.MultisiteTensor

/-! Zero-load invariant-face identities for the actual scaled site addition.
The Jacobian, the symmetric Hessian and the kinetic-parameter derivative of
the literal centered chemical field are shown to intertwine with the parent
quantities through the face inclusion, in the verified coordinate chart.
All fixed-total S0/E/F corrections are retained because the identities are
extracted from the exact reduced field; the normal-to-old cross terms are
neither computed nor asserted to vanish. -/
namespace ThreeSitePhosphorylation.AddedSiteHessianTransport
noncomputable section
open PhosphorylationSharpness MultisiteChart MultisiteSource MultisiteCenteredFace
open MultisiteCoordinates MultisiteTaylor MultisiteTensor ScaledMultisiteSource
open ScaledAffineFamily
open scoped BigOperators
set_option maxHeartbeats 700000

/-- Coefficients of a real quadratic polynomial identity in a module. -/
theorem quadratic_coefficients {V : Type*} [AddCommGroup V] [Module ℝ V]
    (a b c a' b' c' : V)
    (h : ∀ t : ℝ, a+t • b+(t*t) • c=a'+t • b'+(t*t) • c') : b=b' ∧ c=c' := by
  have h0 : a=a' := by simpa using h 0
  have hH (t : ℝ) : t • (b-b')+(t*t) • (c-c')=0 := by
    have ht := h t
    rw [h0,add_assoc,add_assoc] at ht
    rw [smul_sub,smul_sub,sub_add_sub_comm,sub_eq_zero]
    exact add_left_cancel ht
  have h1 := hH 1
  have hm := hH (-1)
  simp only [one_smul,one_mul,neg_smul,neg_mul,mul_neg,neg_neg] at h1 hm
  have he : (2:ℝ) • (c-c')=0 := by
    rw [two_smul]
    calc (c-c')+(c-c')=((b-b')+(c-c'))+(-(b-b')+(c-c')) := by abel
      _=0 := by rw [h1,hm,add_zero]
  have hc : c-c'=0 := (smul_eq_zero.mp he).resolve_left (by norm_num)
  have hb : b-b'=0 := by rw [hc,add_zero] at h1; exact h1
  exact ⟨sub_eq_zero.mp hb,sub_eq_zero.mp hc⟩

/-- The appended zero-load equilibrium candidate and the scaled zero-load rates. -/
abbrev zeroState {n : ℕ} (x : PhosphorylationSharpness.State n) :
    PhosphorylationSharpness.State (n+1) := appendState x 0 0 0

abbrev zeroRates {n : ℕ} (k : Rates n) (κ α : ℝ) : Rates (n+1) :=
  appendScaledRates k κ 0 α

theorem zeroState_totals {n : ℕ} (x : PhosphorylationSharpness.State n) :
    totalE (zeroState x)=totalE x ∧ totalF (zeroState x)=totalF x ∧
      totalS (zeroState x)=totalS x := by
  obtain ⟨he,hf,hs⟩ := append_totals x 0 0 0
  exact ⟨by simpa using he,by simpa using hf,by simpa using hs⟩

theorem project_zeroState {n : ℕ} (x : PhosphorylationSharpness.State n) :
    project (zeroState x)=faceInclusion n (project x) :=
  project_appendState x 0 0 0

/-- The literal centered field about the appended state restricts exactly to
the parent centered field on the zero-load face. -/
theorem centered_face {n : ℕ} (k : Rates n) (κ α : ℝ)
    (x : PhosphorylationSharpness.State n) (y : ReducedState n) :
    centeredField (totalE (zeroState x)) (totalF (zeroState x)) (totalS (zeroState x))
      (zeroRates k κ α) (project (zeroState x)) (faceInclusion n y)=
      faceInclusion n (centeredField (totalE x) (totalF x) (totalS x) k (project x) y) := by
  obtain ⟨he,hf,hs⟩ := zeroState_totals x
  rw [he,hf,hs,project_zeroState]
  change reducedField (totalE x) (totalF x) (totalS x) (zeroRates k κ α)
      (faceInclusion n (project x)+faceInclusion n y)=_
  rw [← (faceInclusion n).map_add]
  change project (field (appendScaledRates k κ 0 α)
      (chart (totalE x) (totalF x) (totalS x) (appendReduced (project x+y) 0 0 0)))=
    appendReduced (reducedField (totalE x) (totalF x) (totalS x) k (project x+y)) 0 0 0
  rw [chart_zero_append,scaled_zero_load_face,project_appendState]
  rfl

/-- Exact Jacobian and diagonal-Hessian face identities, extracted as
coefficients of the literal polynomial restriction. -/
theorem linear_diagonal_face {n : ℕ} (k : Rates n) (κ α : ℝ)
    (x : PhosphorylationSharpness.State n) (y : ReducedState n) :
    linearTerm (zeroRates k κ α) (zeroState x) (faceInclusion n y)=
      faceInclusion n (linearTerm k x y) ∧
    bilinearTerm (zeroRates k κ α) (faceInclusion n y) (faceInclusion n y)=
      faceInclusion n (bilinearTerm k y y) := by
  have h := fun t : ℝ => centered_face k κ α x (t • y)
  have hp : ∀ t : ℝ,
      project (field (zeroRates k κ α) (zeroState x))+
        t • linearTerm (zeroRates k κ α) (zeroState x) (faceInclusion n y)+
        (t*t) • ((1/2:ℝ) • bilinearTerm (zeroRates k κ α)
          (faceInclusion n y) (faceInclusion n y))=
      faceInclusion n (project (field k x))+
        t • faceInclusion n (linearTerm k x y)+
        (t*t) • faceInclusion n ((1/2:ℝ) • bilinearTerm k y y) := by
    intro t
    have ht := h t
    rw [exact_expansion,exact_expansion,map_smul] at ht
    have hl1 : linearTerm (zeroRates k κ α) (zeroState x) (t • faceInclusion n y)=
        t • linearTerm (zeroRates k κ α) (zeroState x) (faceInclusion n y) :=
      (sourceLinear (zeroRates k κ α) (zeroState x)).map_smul t (faceInclusion n y)
    have hl2 : linearTerm k x (t • y)=t • linearTerm k x y :=
      (sourceLinear k x).map_smul t y
    have hb1 : bilinearTerm (zeroRates k κ α) (t • faceInclusion n y) (t • faceInclusion n y)=
        (t*t) • bilinearTerm (zeroRates k κ α) (faceInclusion n y) (faceInclusion n y) := by
      change sourceBilinear (zeroRates k κ α) (t • faceInclusion n y) (t • faceInclusion n y)=
        (t*t) • sourceBilinear (zeroRates k κ α) (faceInclusion n y) (faceInclusion n y)
      rw [LinearMap.map_smul₂,map_smul,smul_smul]
    have hb2 : bilinearTerm k (t • y) (t • y)=(t*t) • bilinearTerm k y y := by
      change sourceBilinear k (t • y) (t • y)=(t*t) • sourceBilinear k y y
      rw [LinearMap.map_smul₂,map_smul,smul_smul]
    rw [hl1,hl2,hb1,hb2,map_add,map_add,map_smul,map_smul,map_smul] at ht
    rw [map_smul]
    simpa only [smul_comm (1/2:ℝ) (t*t)] using ht
  obtain ⟨hl,hb⟩ := quadratic_coefficients _ _ _ _ _ _ hp
  refine ⟨hl,?_⟩
  rw [map_smul] at hb
  have h2 := congrArg (fun z => (2:ℝ) • z) hb
  simpa only [smul_smul,show (2:ℝ)*(1/2)=1 by norm_num,one_smul] using h2

/-- The literal Jacobian intertwines through the face (step 1). -/
theorem linear_face {n : ℕ} (k : Rates n) (κ α : ℝ)
    (x : PhosphorylationSharpness.State n) (y : ReducedState n) :
    linearTerm (zeroRates k κ α) (zeroState x) (faceInclusion n y)=
      faceInclusion n (linearTerm k x y) :=
  (linear_diagonal_face k κ α x y).1

/-- The full symmetric Hessian intertwines through the face, by polarization
of the diagonal identity. -/
theorem bilinear_face {n : ℕ} (k : Rates n) (κ α : ℝ)
    (x : PhosphorylationSharpness.State n) (u v : ReducedState n) :
    bilinearTerm (zeroRates k κ α) (faceInclusion n u) (faceInclusion n v)=
      faceInclusion n (bilinearTerm k u v) := by
  let B' := sourceBilinear (zeroRates k κ α)
  let B := sourceBilinear k
  have hd (y : ReducedState n) : B' (faceInclusion n y) (faceInclusion n y)=
      faceInclusion n (B y y) := (linear_diagonal_face k κ α x y).2
  have hs' : B' (faceInclusion n v) (faceInclusion n u)=
      B' (faceInclusion n u) (faceInclusion n v) :=
    bilinearTerm_symmetric _ _ _
  have hs : B v u=B u v := bilinearTerm_symmetric _ _ _
  have hsum := hd (u+v)
  simp only [map_add,LinearMap.add_apply,hs',hs] at hsum
  rw [hd u,hd v] at hsum
  change B' (faceInclusion n u) (faceInclusion n v)=faceInclusion n (B u v)
  have h2 : (2:ℝ) • B' (faceInclusion n u) (faceInclusion n v)=
      (2:ℝ) • faceInclusion n (B u v) := by
    rw [two_smul,two_smul,← sub_eq_zero]
    rw [← sub_eq_zero] at hsum
    rw [← hsum]
    abel
  exact smul_right_injective _ (by norm_num : (2:ℝ) ≠ 0) h2

/-! ### Coordinate form -/

/-- The face inclusion in the flat coordinate chart. -/
def coordinateFace (n : ℕ) : CoordinateState n →ₗ[ℝ] CoordinateState (n+1) :=
  (toCoordinates (n+1)).toLinearMap.comp ((faceInclusion n).comp (fromCoordinates n).toLinearMap)

@[simp] theorem coordinateFace_apply {n : ℕ} (y : CoordinateState n) :
    coordinateFace n y=toCoordinates (n+1) (faceInclusion n (fromCoordinates n y)) := rfl

/-- The real rectangular matrix of the face inclusion. -/
def faceMatrix (n : ℕ) : Matrix (CoordinateIndex (n+1)) (CoordinateIndex n) ℝ :=
  LinearMap.toMatrix' (coordinateFace n)

theorem faceMatrix_mulVec {n : ℕ} (y : CoordinateState n) :
    (faceMatrix n).mulVec y=coordinateFace n y :=
  LinearMap.toMatrix'_mulVec (coordinateFace n) y

theorem coordinateLinear_face {n : ℕ} (k : Rates n) (κ α : ℝ)
    (x : PhosphorylationSharpness.State n) :
    (coordinateLinear (zeroRates k κ α) (zeroState x)).comp (coordinateFace n)=
      (coordinateFace n).comp (coordinateLinear k x) := by
  apply LinearMap.ext
  intro y
  simp only [LinearMap.comp_apply,coordinateLinear_apply,coordinateFace_apply,
    fromCoordinates_toCoordinates,linear_face]

/-- Matrix form of the actual zero-load Jacobian intertwining. -/
theorem sourceMatrix_face {n : ℕ} (k : Rates n) (κ α : ℝ)
    (x : PhosphorylationSharpness.State n) :
    sourceMatrix (zeroRates k κ α) (zeroState x)*faceMatrix n=
      faceMatrix n*sourceMatrix k x := by
  unfold sourceMatrix faceMatrix
  rw [← LinearMap.toMatrix'_comp,← LinearMap.toMatrix'_comp,coordinateLinear_face]

/-- Tensor form of the actual zero-load Hessian intertwining. -/
theorem sourceTensor_face {n : ℕ} (k : Rates n) (κ α : ℝ)
    (x : PhosphorylationSharpness.State n) (u v : CoordinateState n) :
    GenericTensorBilinear.realBilinear (sourceTensor (zeroRates k κ α))
      ((faceMatrix n).mulVec u) ((faceMatrix n).mulVec v)=
      (faceMatrix n).mulVec (GenericTensorBilinear.realBilinear (sourceTensor k) u v) := by
  rw [sourceTensor_action,sourceTensor_action]
  simp only [faceMatrix_mulVec,coordinateBilinear_apply,coordinateFace_apply,
    fromCoordinates_toCoordinates,bilinear_face k κ α x]

/-! ### Affine kinetic families at zero load -/

theorem realBilinear_add_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H0 H1 : GenericQuadraticTensor.Tensor ι) (s : ℝ) (u v : ι → ℝ) :
    GenericTensorBilinear.realBilinear (H0+s • H1) u v=
      GenericTensorBilinear.realBilinear H0 u v+
        s • GenericTensorBilinear.realBilinear H1 u v := by
  ext i
  simp only [GenericTensorBilinear.realBilinear,GenericTensorBilinear.tensorBilinear_apply,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  apply congrArg
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The actual extended family at zero load uses these rate arrays. -/
theorem extendedFamily_zero {n : ℕ} (offset slope : Rates n)
    (x : PhosphorylationSharpness.State n) (κ r : ℝ) :
    extendedFamily (affineRates offset slope) x κ 0 r=
      affineRates (zeroRates offset κ (κ/x.F)) (zeroRates slope 0 0) r := by
  unfold extendedFamily
  simp only [mul_zero,zero_div]
  exact append_affineRates offset slope κ 0 (κ/x.F) r

theorem zero_load_state {n : ℕ} (x : PhosphorylationSharpness.State n) :
    appendState x 0 (2*0) 0=zeroState x := by
  simp only [mul_zero]

/-- Critical operator, parameter derivative and Hessian identities for the
actual affine child family at zero load (step 1). -/
theorem affine_face {n : ℕ} (offset slope : Rates n)
    (x : PhosphorylationSharpness.State n) (κ α r : ℝ) :
    (sourceMatrix (zeroRates offset κ α) (zeroState x)+
        r • sourceMatrix (zeroRates slope 0 0) (zeroState x))*faceMatrix n=
      faceMatrix n*(sourceMatrix offset x+r • sourceMatrix slope x) ∧
    sourceMatrix (zeroRates slope 0 0) (zeroState x)*faceMatrix n=
      faceMatrix n*sourceMatrix slope x ∧
    ∀ u v : CoordinateState n,
      GenericTensorBilinear.realBilinear
        (sourceTensor (zeroRates offset κ α)+r • sourceTensor (zeroRates slope 0 0))
        ((faceMatrix n).mulVec u) ((faceMatrix n).mulVec v)=
      (faceMatrix n).mulVec (GenericTensorBilinear.realBilinear
        (sourceTensor offset+r • sourceTensor slope) u v) := by
  have hA := sourceMatrix_face offset κ α x
  have hD := sourceMatrix_face slope 0 0 x
  refine ⟨?_,hD,?_⟩
  · rw [Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul,Matrix.mul_smul,hA,hD]
  · intro u v
    rw [realBilinear_add_smul,realBilinear_add_smul,sourceTensor_face offset κ α x,
      sourceTensor_face slope 0 0 x,
      Matrix.mulVec_add,Matrix.mulVec_smul]

end
end ThreeSitePhosphorylation.AddedSiteHessianTransport
