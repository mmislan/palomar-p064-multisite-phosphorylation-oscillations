import proofs.ThreeSitePhosphorylation.MultisiteTaylor
import proofs.ThreeSitePhosphorylation.MultisiteCoordinates
import proofs.ThreeSitePhosphorylation.GenericTensorBilinear

/-! Coordinate extraction of the actual chemical linear and quadratic terms.
No identification with an arbitrary smooth quadratic field is assumed. -/
namespace ThreeSitePhosphorylation.MultisiteTensor
noncomputable section
open PhosphorylationSharpness MultisiteChart MultisiteCenteredFace MultisiteCoordinates
open MultisiteTaylor ScaledAffineFamily
open scoped BigOperators
set_option maxHeartbeats 700000

def linearMapOfAddSmul {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (f : E → F)
    (h : ∀ (u v : E) (t : ℝ), f (u+t • v)=f u+t • f v) : E →ₗ[ℝ] F where
  toFun := f
  map_add' u v := by simpa only [one_smul] using h u v 1
  map_smul' t v := by
    have hzero : f 0=0 := by
      have hh := h 0 0 1
      simp only [one_smul,add_zero] at hh
      have hc : f 0+f 0=f 0+0 := by simpa only [add_zero] using hh.symm
      exact add_left_cancel hc
    simpa only [zero_add,hzero] using h 0 v t

def sourceLinear {n : ℕ} (k : Rates n) (x : PhosphorylationSharpness.State n) :
    ReducedState n →ₗ[ℝ] ReducedState n :=
  linearMapOfAddSmul (linearTerm k x) (linearTerm_add_smul k x)

def sourceBilinear {n : ℕ} (k : Rates n) :
    ReducedState n →ₗ[ℝ] ReducedState n →ₗ[ℝ] ReducedState n :=
  linearMapOfAddSmul
    (fun u => linearMapOfAddSmul (bilinearTerm k u) (bilinearTerm_add_smul_right k u))
    (by
      intro u v t
      apply LinearMap.ext
      intro z
      exact bilinearTerm_add_smul_left k u v z t)

def coordinateLinear {n : ℕ} (k : Rates n) (x : PhosphorylationSharpness.State n) :
    CoordinateState n →ₗ[ℝ] CoordinateState n :=
  (toCoordinates n).toLinearMap.comp ((sourceLinear k x).comp (fromCoordinates n).toLinearMap)

@[simp] theorem coordinateLinear_apply {n : ℕ} (k : Rates n)
    (x : PhosphorylationSharpness.State n) (y : CoordinateState n) :
    coordinateLinear k x y = toCoordinates n (linearTerm k x (fromCoordinates n y)) := rfl

def coordinateBilinear {n : ℕ} (k : Rates n) :
    CoordinateState n →ₗ[ℝ] CoordinateState n →ₗ[ℝ] CoordinateState n :=
  linearMapOfAddSmul
    (fun u => (toCoordinates n).toLinearMap.comp
      ((sourceBilinear k (fromCoordinates n u)).comp (fromCoordinates n).toLinearMap))
    (by
      intro u v t
      apply LinearMap.ext
      intro z
      change toCoordinates n (bilinearTerm k (fromCoordinates n (u+t • v)) (fromCoordinates n z)) =
        toCoordinates n (bilinearTerm k (fromCoordinates n u) (fromCoordinates n z)) +
          t • toCoordinates n (bilinearTerm k (fromCoordinates n v) (fromCoordinates n z))
      rw [map_add,map_smul,bilinearTerm_add_smul_left,map_add,map_smul])

@[simp] theorem coordinateBilinear_apply {n : ℕ} (k : Rates n)
    (u v : CoordinateState n) :
    coordinateBilinear k u v =
      toCoordinates n (bilinearTerm k (fromCoordinates n u) (fromCoordinates n v)) := rfl

def sourceMatrix {n : ℕ} (k : Rates n) (x : PhosphorylationSharpness.State n) :
    Matrix (CoordinateIndex n) (CoordinateIndex n) ℝ :=
  LinearMap.toMatrix' (coordinateLinear k x)

def sourceTensor {n : ℕ} (k : Rates n) : GenericQuadraticTensor.Tensor (CoordinateIndex n) :=
  fun i j l => coordinateBilinear k (Pi.single j 1) (Pi.single l 1) i

theorem sourceMatrix_action {n : ℕ} (k : Rates n)
    (x : PhosphorylationSharpness.State n) (y : CoordinateState n) :
    (sourceMatrix k x).mulVec y = coordinateLinear k x y :=
  LinearMap.toMatrix'_mulVec (coordinateLinear k x) y

theorem sum_coordinate_vectors {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → ℝ) :
    ∑ j, u j • Pi.single j (1 : ℝ) = u := by
  ext i
  simp [Finset.sum_apply,Pi.single_apply]

theorem bilinear_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (u v : ι → ℝ) (i : ι) :
    B u v i = ∑ j, ∑ l, B (Pi.single j 1) (Pi.single l 1) i*u j*v l := by
  calc
    B u v i = B (∑ j, u j • Pi.single j 1) (∑ l, v l • Pi.single l 1) i := by
      rw [sum_coordinate_vectors,sum_coordinate_vectors]
    _ = _ := by
      simp [map_sum,Finset.sum_apply,Finset.mul_sum,mul_comm,mul_left_comm]
      rw [Finset.sum_comm]

theorem sourceTensor_action {n : ℕ} (k : Rates n) (u v : CoordinateState n) :
    GenericTensorBilinear.realBilinear (sourceTensor k) u v = coordinateBilinear k u v := by
  ext i
  exact (bilinear_coordinates (coordinateBilinear k) u v i).symm

theorem sourceTensor_symmetric {n : ℕ} (k : Rates n) (i j l : CoordinateIndex n) :
    sourceTensor k i j l = sourceTensor k i l j := by
  unfold sourceTensor
  simp only [coordinateBilinear_apply,bilinearTerm_symmetric k
    (fromCoordinates n (Pi.single j 1)) (fromCoordinates n (Pi.single l 1))]

def coordinateField {n : ℕ} (k : Rates n) (x : PhosphorylationSharpness.State n)
    (y : CoordinateState n) : CoordinateState n :=
  toCoordinates n (centeredField (totalE x) (totalF x) (totalS x) k (project x)
    (fromCoordinates n y))

theorem coordinateField_exact {n : ℕ} (k : Rates n)
    (x : PhosphorylationSharpness.State n) (y : CoordinateState n) :
    coordinateField k x y = toCoordinates n (project (field k x)) +
      (sourceMatrix k x).mulVec y +
      (1/2 : ℝ) • GenericTensorBilinear.realBilinear (sourceTensor k) y y := by
  rw [sourceMatrix_action,sourceTensor_action]
  change toCoordinates n (centeredField (totalE x) (totalF x) (totalS x) k (project x)
    (fromCoordinates n y)) = _
  rw [exact_expansion,map_add,map_add,map_smul]
  rfl

theorem coordinateField_equilibrium {n : ℕ} (k : Rates n)
    (x : PhosphorylationSharpness.State n) (hx : Equilibrium k x) (y : CoordinateState n) :
    coordinateField k x y = (sourceMatrix k x).mulVec y +
      (1/2 : ℝ) • GenericTensorBilinear.realBilinear (sourceTensor k) y y := by
  rw [sourceMatrix_action,sourceTensor_action]
  change toCoordinates n (centeredField (totalE x) (totalF x) (totalS x) k (project x)
    (fromCoordinates n y)) = _
  rw [equilibrium_expansion k x hx,map_add,map_smul]
  rfl

theorem sourceMatrix_affine {n : ℕ} (k0 k1 : Rates n)
    (x : PhosphorylationSharpness.State n) (r : ℝ) :
    sourceMatrix (affineRates k0 k1 r) x = sourceMatrix k0 x+r • sourceMatrix k1 x := by
  have he : coordinateLinear (affineRates k0 k1 r) x =
      coordinateLinear k0 x+r • coordinateLinear k1 x := by
    apply LinearMap.ext
    intro y
    simp only [coordinateLinear_apply,linearTerm_affine_rates,map_add,map_smul,
      LinearMap.add_apply,LinearMap.smul_apply]
  unfold sourceMatrix
  rw [he,map_add,map_smul]

theorem sourceTensor_affine {n : ℕ} (k0 k1 : Rates n) (r : ℝ) :
    sourceTensor (affineRates k0 k1 r) = sourceTensor k0+r • sourceTensor k1 := by
  funext i j l
  simp only [sourceTensor,coordinateBilinear_apply,bilinearTerm_affine_rates,
    map_add,map_smul,Pi.add_apply,Pi.smul_apply]

/-- Exact chemical-source input to GenericQuadraticClosedPaths after
fixing the load and translating the critical kinetic parameter if needed. -/
theorem affine_coordinateField {n : ℕ} (k0 k1 : Rates n)
    (x : PhosphorylationSharpness.State n)
    (hx : ∀ r, Equilibrium (affineRates k0 k1 r) x) (r : ℝ) (y : CoordinateState n) :
    coordinateField (affineRates k0 k1 r) x y =
      (sourceMatrix k0 x+r • sourceMatrix k1 x).mulVec y +
        GenericQuadraticTensor.field (fun s => sourceTensor k0+s • sourceTensor k1) r y := by
  rw [coordinateField_equilibrium _ _ (hx r),sourceMatrix_affine,sourceTensor_affine,
    GenericTensorBilinear.field_eq_half_bilinear]

theorem affine_sourceTensor_smooth {n : ℕ} (k0 k1 : Rates n)
    (i j l : CoordinateIndex n) :
    ContDiff ℝ ⊤ (fun r : ℝ => (sourceTensor k0+r • sourceTensor k1) i j l) := by
  change ContDiff ℝ ⊤ (fun r : ℝ => sourceTensor k0 i j l+r*sourceTensor k1 i j l)
  fun_prop

end
end ThreeSitePhosphorylation.MultisiteTensor
