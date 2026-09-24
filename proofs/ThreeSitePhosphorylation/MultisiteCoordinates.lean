import proofs.ThreeSitePhosphorylation.MultisiteChart

/-! A finite function-coordinate presentation of the actual reduced state.
The three summands retain the S1,...,Sm, C, D order without arithmetic
reindexing into Fin (3*m). -/
namespace ThreeSitePhosphorylation.MultisiteCoordinates
noncomputable section
open MultisiteChart

abbrev CoordinateIndex (m : ℕ) := Fin m ⊕ (Fin m ⊕ Fin m)
abbrev CoordinateState (m : ℕ) := CoordinateIndex m → ℝ

def coordinateLinearEquiv (m : ℕ) : ReducedState m ≃ₗ[ℝ] CoordinateState m where
  toFun y := Sum.elim y.1 (Sum.elim y.2.1 y.2.2)
  invFun z := (fun i => z (Sum.inl i),
    (fun i => z (Sum.inr (Sum.inl i)),fun i => z (Sum.inr (Sum.inr i))))
  left_inv y := by
    rcases y with ⟨s,c,d⟩
    rfl
  right_inv z := by
    funext i
    rcases i with i | (i | i) <;> rfl
  map_add' x y := by
    funext i
    rcases i with i | (i | i) <;> rfl
  map_smul' a y := by
    funext i
    rcases i with i | (i | i) <;> rfl

def coordinateEquiv (m : ℕ) : ReducedState m ≃L[ℝ] CoordinateState m :=
  (coordinateLinearEquiv m).toContinuousLinearEquiv

theorem coordinateEquiv_apply {m : ℕ} (y : ReducedState m) :
    coordinateEquiv m y = Sum.elim y.1 (Sum.elim y.2.1 y.2.2) := rfl

@[simp] theorem coordinateEquiv_apply_s {m : ℕ} (y : ReducedState m) (i : Fin m) :
    coordinateEquiv m y (Sum.inl i) = y.1 i := rfl

@[simp] theorem coordinateEquiv_apply_c {m : ℕ} (y : ReducedState m) (i : Fin m) :
    coordinateEquiv m y (Sum.inr (Sum.inl i)) = y.2.1 i := rfl

@[simp] theorem coordinateEquiv_apply_d {m : ℕ} (y : ReducedState m) (i : Fin m) :
    coordinateEquiv m y (Sum.inr (Sum.inr i)) = y.2.2 i := rfl

theorem coordinateEquiv_symm_apply {m : ℕ} (z : CoordinateState m) :
    (coordinateEquiv m).symm z =
      (fun i => z (Sum.inl i),
        (fun i => z (Sum.inr (Sum.inl i)),fun i => z (Sum.inr (Sum.inr i)))) := rfl

@[simp] theorem coordinateEquiv_symm_s {m : ℕ} (z : CoordinateState m) (i : Fin m) :
    ((coordinateEquiv m).symm z).1 i = z (Sum.inl i) := rfl

@[simp] theorem coordinateEquiv_symm_c {m : ℕ} (z : CoordinateState m) (i : Fin m) :
    ((coordinateEquiv m).symm z).2.1 i = z (Sum.inr (Sum.inl i)) := rfl

@[simp] theorem coordinateEquiv_symm_d {m : ℕ} (z : CoordinateState m) (i : Fin m) :
    ((coordinateEquiv m).symm z).2.2 i = z (Sum.inr (Sum.inr i)) := rfl

/-- The continuous linear maps used when conjugating a source derivative
or transporting either argument of a bilinear source tensor. -/
def toCoordinates (m : ℕ) : ReducedState m →L[ℝ] CoordinateState m :=
  (coordinateEquiv m).toContinuousLinearMap

def fromCoordinates (m : ℕ) : CoordinateState m →L[ℝ] ReducedState m :=
  (coordinateEquiv m).symm.toContinuousLinearMap

@[simp] theorem toCoordinates_apply {m : ℕ} (y : ReducedState m) :
    toCoordinates m y = coordinateEquiv m y := rfl

@[simp] theorem fromCoordinates_apply {m : ℕ} (z : CoordinateState m) :
    fromCoordinates m z = (coordinateEquiv m).symm z := rfl

@[simp] theorem fromCoordinates_toCoordinates {m : ℕ} (y : ReducedState m) :
    fromCoordinates m (toCoordinates m y) = y :=
  (coordinateEquiv m).symm_apply_apply y

@[simp] theorem toCoordinates_fromCoordinates {m : ℕ} (z : CoordinateState m) :
    toCoordinates m (fromCoordinates m z) = z :=
  (coordinateEquiv m).apply_symm_apply z

end
end ThreeSitePhosphorylation.MultisiteCoordinates
