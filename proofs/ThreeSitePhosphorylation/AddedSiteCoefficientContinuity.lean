import proofs.ThreeSitePhosphorylation.AddedSiteCoefficientTransport
import Mathlib.Topology.Instances.Matrix

/-! Continuity of the normalized resolvent coefficient built from GENUINE
matrix inverses, and persistence of strict signs of the coefficient and of the
kinetic crossing pairing along any continuous family of critical data.

The resolvents are the actual `Matrix` inverses; the identities showing that
they solve the zero and second-harmonic equations use invertibility of the
determinant, which is itself propagated from the base point by continuity.
Nothing here constructs the critical family: it consumes continuity of the
operator, tensor, critical vector, left functional and frequency. -/
namespace ThreeSitePhosphorylation.AddedSiteCoefficientContinuity
noncomputable section
open scoped Topology BigOperators
open Filter GenericComplexification GenericTensorBilinear AddedSiteCoefficientTransport

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {X : Type*} [TopologicalSpace X]

theorem continuousAt_sum {α M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    [ContinuousAdd M] {f : α → X → M} (s : Finset α) {x : X}
    (h : ∀ i ∈ s, ContinuousAt (f i) x) : ContinuousAt (fun a => ∑ i ∈ s, f i a) x :=
  tendsto_finsetSum s h

/-! ### Genuine resolvents -/

/-- The complex second-harmonic operator `2iw-A`. -/
def secondShift (M : Matrix ι ι ℝ) (w : ℝ) : Matrix ι ι ℂ :=
  (2*Complex.I*(w:ℂ)) • (1 : Matrix ι ι ℂ)-complexMatrix M

theorem secondShift_mulVec (M : Matrix ι ι ℝ) (w : ℝ) (h : ι → ℂ) :
    (secondShift M w).mulVec h=(2*Complex.I*(w:ℂ)) • h-(complexMatrix M).mulVec h := by
  rw [secondShift,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec]

/-- The genuine zero resolvent solution `A⁻¹ B(q,conj q)`. -/
def zeroResolvent (M : Matrix ι ι ℝ) (T : GenericQuadraticTensor.Tensor ι) (q : ι → ℂ) :
    ι → ℂ :=
  (complexMatrix M)⁻¹.mulVec (complexBilinear T q (conjugateVector q))

/-- The genuine second-harmonic solution `(2iw-A)⁻¹ B(q,q)`. -/
def secondResolvent (M : Matrix ι ι ℝ) (T : GenericQuadraticTensor.Tensor ι) (q : ι → ℂ)
    (w : ℝ) : ι → ℂ :=
  (secondShift M w)⁻¹.mulVec (complexBilinear T q q)

/-- The normalized coefficient `G` with genuine resolvents. -/
def resolventCoefficient (p : (ι → ℂ) →L[ℂ] ℂ) (M : Matrix ι ι ℝ)
    (T : GenericQuadraticTensor.Tensor ι) (q : ι → ℂ) (w : ℝ) : ℂ :=
  coefficient p.toLinearMap T q (zeroResolvent M T q) (secondResolvent M T q w)

theorem zeroResolvent_eq (M : Matrix ι ι ℝ) (T : GenericQuadraticTensor.Tensor ι)
    (q : ι → ℂ) (hdet : (complexMatrix M).det ≠ 0) :
    (complexMatrix M).mulVec (zeroResolvent M T q)=complexBilinear T q (conjugateVector q) := by
  rw [zeroResolvent,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

theorem secondResolvent_eq (M : Matrix ι ι ℝ) (T : GenericQuadraticTensor.Tensor ι)
    (q : ι → ℂ) (w : ℝ) (hdet : (secondShift M w).det ≠ 0) :
    (2*Complex.I*(w:ℂ)) • secondResolvent M T q w-
      (complexMatrix M).mulVec (secondResolvent M T q w)=complexBilinear T q q := by
  rw [← secondShift_mulVec,secondResolvent,Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),Matrix.one_mulVec]

/-- Genuine injectivity of the zero operator is equivalent to a nonzero determinant. -/
theorem det_ne_zero_of_injective (M : Matrix ι ι ℝ)
    (h : Function.Injective (complexMatrix M).mulVecLin) : (complexMatrix M).det ≠ 0 := by
  have hu : IsUnit (complexMatrix M) := Matrix.mulVec_injective_iff_isUnit.mp h
  exact (Matrix.isUnit_iff_isUnit_det _).mp hu |>.ne_zero

theorem secondShift_det_ne_zero_of_injective (M : Matrix ι ι ℝ) (w : ℝ)
    (h : Function.Injective ((2*Complex.I*(w:ℂ)) •
      (LinearMap.id : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))-(complexMatrix M).mulVecLin)) :
    (secondShift M w).det ≠ 0 := by
  have hi : Function.Injective (secondShift M w).mulVec := by
    intro a c hac
    apply h
    simp only [LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,
      Matrix.mulVecLin_apply]
    rw [← secondShift_mulVec,← secondShift_mulVec]
    exact hac
  have hu : IsUnit (secondShift M w) := Matrix.mulVec_injective_iff_isUnit.mp hi
  exact (Matrix.isUnit_iff_isUnit_det _).mp hu |>.ne_zero

/-- Any genuine solutions give the same coefficient as the genuine inverses. -/
theorem coefficient_eq_resolventCoefficient (p : (ι → ℂ) →L[ℂ] ℂ) (M : Matrix ι ι ℝ)
    (T : GenericQuadraticTensor.Tensor ι) (q : ι → ℂ) (w : ℝ)
    (h0 : (complexMatrix M).det ≠ 0) (h2 : (secondShift M w).det ≠ 0)
    (k11 k20 : ι → ℂ)
    (k11eq : (complexMatrix M).mulVec k11=complexBilinear T q (conjugateVector q))
    (k20eq : (2*Complex.I*(w:ℂ)) • k20-(complexMatrix M).mulVec k20=complexBilinear T q q) :
    coefficient p.toLinearMap T q k11 k20=resolventCoefficient p M T q w := by
  have hi0 : Function.Injective (complexMatrix M).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h0))
  have hi2 : Function.Injective (secondShift M w).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h2))
  have e11 : k11=zeroResolvent M T q := hi0 (k11eq.trans (zeroResolvent_eq M T q h0).symm)
  have e20 : k20=secondResolvent M T q w := by
    apply hi2
    rw [secondShift_mulVec,secondShift_mulVec,k20eq,secondResolvent_eq M T q w h2]
  rw [resolventCoefficient,e11,e20]

/-! ### Continuity -/

omit [Fintype ι] [DecidableEq ι] in
theorem continuousAt_complexMatrix {M : X → Matrix ι ι ℝ} {x : X} (hM : ContinuousAt M x) :
    ContinuousAt (fun a => complexMatrix (M a)) x := by
  have hc : Continuous (fun N : Matrix ι ι ℝ => complexMatrix N) :=
    Continuous.matrix_map continuous_id Complex.continuous_ofReal
  exact hc.continuousAt.comp hM

omit [Fintype ι] in
theorem continuousAt_secondShift {M : X → Matrix ι ι ℝ} {w : X → ℝ} {x : X}
    (hM : ContinuousAt M x) (hw : ContinuousAt w x) :
    ContinuousAt (fun a => secondShift (M a) (w a)) x := by
  unfold secondShift
  have hw' : ContinuousAt (fun a => 2*Complex.I*((w a:ℝ):ℂ)) x :=
    continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp hw)
  exact (hw'.smul continuousAt_const).sub (continuousAt_complexMatrix hM)

theorem continuousAt_inv {F : X → Matrix ι ι ℂ} {x : X} (hF : ContinuousAt F x)
    (hdet : (F x).det ≠ 0) : ContinuousAt (fun a => (F a)⁻¹) x := by
  have hr : ContinuousAt (Ring.inverse : ℂ → ℂ) (F x).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  exact (continuousAt_matrix_inv (F x) hr).comp hF

omit [DecidableEq ι] in
theorem continuousAt_mulVec {F : X → Matrix ι ι ℂ} {u : X → ι → ℂ} {x : X}
    (hF : ContinuousAt F x) (hu : ContinuousAt u x) :
    ContinuousAt (fun a => (F a).mulVec (u a)) x := by
  have hc : Continuous (fun z : Matrix ι ι ℂ × (ι → ℂ) => z.1.mulVec z.2) :=
    Continuous.matrix_mulVec continuous_fst continuous_snd
  exact hc.continuousAt.comp (hF.prodMk hu)

omit [Fintype ι] [DecidableEq ι] in
theorem continuousAt_conjugate {q : X → ι → ℂ} {x : X} (hq : ContinuousAt q x) :
    ContinuousAt (fun a => conjugateVector (q a)) x := by
  have hc : Continuous (fun z : ι → ℂ => conjugateVector z) :=
    continuous_pi fun i => Complex.continuous_conj.comp (continuous_apply i)
  exact hc.continuousAt.comp hq

theorem continuousAt_complexBilinear {T : X → GenericQuadraticTensor.Tensor ι}
    {u v : X → ι → ℂ} {x : X} (hT : ContinuousAt T x) (hu : ContinuousAt u x)
    (hv : ContinuousAt v x) :
    ContinuousAt (fun a => complexBilinear (T a) (u a) (v a)) x := by
  apply continuousAt_pi.2
  intro i
  simp only [complexBilinear,tensorBilinear_apply]
  apply continuousAt_sum
  intro j _
  apply continuousAt_sum
  intro k _
  have hTijk : ContinuousAt (fun a => ((T a i j k:ℝ):ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_pi.1 (continuousAt_pi.1 (continuousAt_pi.1 hT i) j) k)
  exact (hTijk.mul (continuousAt_pi.1 hu j)).mul (continuousAt_pi.1 hv k)

/-- The genuine-resolvent coefficient is continuous wherever both resolvent
operators are invertible at the base point. -/
theorem resolventCoefficient_continuousAt {p : X → (ι → ℂ) →L[ℂ] ℂ}
    {M : X → Matrix ι ι ℝ} {T : X → GenericQuadraticTensor.Tensor ι}
    {q : X → ι → ℂ} {w : X → ℝ} {x : X}
    (hp : ContinuousAt p x) (hM : ContinuousAt M x) (hT : ContinuousAt T x)
    (hq : ContinuousAt q x) (hw : ContinuousAt w x)
    (h0 : (complexMatrix (M x)).det ≠ 0) (h2 : (secondShift (M x) (w x)).det ≠ 0) :
    ContinuousAt (fun a => resolventCoefficient (p a) (M a) (T a) (q a) (w a)) x := by
  have hq' := continuousAt_conjugate hq
  have h11 : ContinuousAt (fun a => zeroResolvent (M a) (T a) (q a)) x :=
    continuousAt_mulVec (continuousAt_inv (continuousAt_complexMatrix hM) h0)
      (continuousAt_complexBilinear hT hq hq')
  have h20 : ContinuousAt (fun a => secondResolvent (M a) (T a) (q a) (w a)) x :=
    continuousAt_mulVec (continuousAt_inv (continuousAt_secondShift hM hw) h2)
      (continuousAt_complexBilinear hT hq hq)
  unfold resolventCoefficient coefficient
  simp only [ContinuousLinearMap.coe_coe]
  exact (continuousAt_const.mul (hp.clm_apply (continuousAt_complexBilinear hT hq h11))).add
    (hp.clm_apply (continuousAt_complexBilinear hT hq' h20))

/-- Both genuine resolvent operators remain invertible near the base point. -/
theorem eventually_invertible {M : X → Matrix ι ι ℝ} {w : X → ℝ} {x : X}
    (hM : ContinuousAt M x) (hw : ContinuousAt w x)
    (h0 : (complexMatrix (M x)).det ≠ 0) (h2 : (secondShift (M x) (w x)).det ≠ 0) :
    ∀ᶠ a in 𝓝 x, (complexMatrix (M a)).det ≠ 0 ∧ (secondShift (M a) (w a)).det ≠ 0 := by
  have hd0 : ContinuousAt (fun a => (complexMatrix (M a)).det) x :=
    (continuous_id.matrix_det).continuousAt.comp (continuousAt_complexMatrix hM)
  have hd2 : ContinuousAt (fun a => (secondShift (M a) (w a)).det) x :=
    (continuous_id.matrix_det).continuousAt.comp (continuousAt_secondShift hM hw)
  exact (hd0.eventually_ne h0).and (hd2.eventually_ne h2)

/-- Strict negativity of the genuine coefficient persists. -/
theorem eventually_coefficient_negative {p : X → (ι → ℂ) →L[ℂ] ℂ}
    {M : X → Matrix ι ι ℝ} {T : X → GenericQuadraticTensor.Tensor ι}
    {q : X → ι → ℂ} {w : X → ℝ} {x : X}
    (hp : ContinuousAt p x) (hM : ContinuousAt M x) (hT : ContinuousAt T x)
    (hq : ContinuousAt q x) (hw : ContinuousAt w x)
    (h0 : (complexMatrix (M x)).det ≠ 0) (h2 : (secondShift (M x) (w x)).det ≠ 0)
    (hG : (resolventCoefficient (p x) (M x) (T x) (q x) (w x)).re<0) :
    ∀ᶠ a in 𝓝 x, (resolventCoefficient (p a) (M a) (T a) (q a) (w a)).re<0 := by
  have hc := Complex.continuous_re.continuousAt.comp
    (resolventCoefficient_continuousAt hp hM hT hq hw h0 h2)
  exact hc.eventually (gt_mem_nhds hG)

omit [DecidableEq ι] in
/-- Strict negativity of the kinetic crossing pairing persists. -/
theorem eventually_crossing_negative {p : X → (ι → ℂ) →L[ℂ] ℂ}
    {D : X → Matrix ι ι ℝ} {q : X → ι → ℂ} {x : X}
    (hp : ContinuousAt p x) (hD : ContinuousAt D x) (hq : ContinuousAt q x)
    (hc : (p x ((complexMatrix (D x)).mulVec (q x))).re<0) :
    ∀ᶠ a in 𝓝 x, (p a ((complexMatrix (D a)).mulVec (q a))).re<0 := by
  have h := Complex.continuous_re.continuousAt.comp
    (hp.clm_apply (continuousAt_mulVec (continuousAt_complexMatrix hD) hq))
  exact h.eventually (gt_mem_nhds hc)

end
end ThreeSitePhosphorylation.AddedSiteCoefficientContinuity
