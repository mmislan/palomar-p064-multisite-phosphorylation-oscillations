import proofs.ThreeSitePhosphorylation.MultisiteNormalDerivative

/-! Exact old/normal reduced-coordinate split, with normal order C,S,D. -/
namespace ThreeSitePhosphorylation.MultisiteSplit
noncomputable section
open MultisiteChart MultisiteCenteredFace MultisiteNormalDerivative

def oldCoordinates {n : ℕ} (y : ReducedState (n+1)) : ReducedState n :=
  ((fun i => y.1 i.castSucc),
    ((fun i => y.2.1 i.castSucc),(fun i => y.2.2 i.castSucc)))

theorem oldCoordinates_append {n : ℕ} (y : ReducedState n) (c s d : ℝ) :
    oldCoordinates (appendReduced y c s d)=y := by
  rcases y with ⟨ys,yc,yd⟩
  simp [oldCoordinates,appendReduced]

theorem normalProjection_append {n : ℕ} (y : ReducedState n) (c s d : ℝ) :
    normalProjection (appendReduced y c s d)=![c,s,d] := by
  ext i
  fin_cases i <;> simp [normalProjection,appendReduced]

theorem append_coordinates {n : ℕ} (y : ReducedState (n+1)) :
    appendReduced (oldCoordinates y) (normalProjection y 0)
      (normalProjection y 1) (normalProjection y 2)=y := by
  ext i <;> refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [appendReduced,oldCoordinates,normalProjection]

def splitEquiv (n : ℕ) :
    (ReducedState n × (Fin 3 → ℝ)) ≃ₗ[ℝ] ReducedState (n+1) where
  toFun z := appendReduced z.1 (z.2 0) (z.2 1) (z.2 2)
  invFun y := (oldCoordinates y,normalProjection y)
  left_inv z := by
    apply Prod.ext
    · exact oldCoordinates_append _ _ _ _
    · change normalProjection (appendReduced z.1 (z.2 0) (z.2 1) (z.2 2)) = z.2
      rw [normalProjection_append]
      funext i
      fin_cases i <;> rfl
  right_inv y := append_coordinates y
  map_add' x y := appendReduced_add x.1 y.1 (x.2 0) (x.2 1) (x.2 2)
    (y.2 0) (y.2 1) (y.2 2)
  map_smul' a z := appendReduced_smul a z.1 (z.2 0) (z.2 1) (z.2 2)

def splitContinuous (n : ℕ) :
    (ReducedState n × (Fin 3 → ℝ)) ≃L[ℝ] ReducedState (n+1) :=
  (splitEquiv n).toContinuousLinearEquiv

def oldProjection (n : ℕ) : ReducedState (n+1) →L[ℝ] ReducedState n :=
  (ContinuousLinearMap.fst ℝ (ReducedState n) (Fin 3 → ℝ)).comp
    (splitContinuous n).symm.toContinuousLinearMap

def normalProjectionCLM (n : ℕ) : ReducedState (n+1) →L[ℝ] (Fin 3 → ℝ) :=
  (ContinuousLinearMap.snd ℝ (ReducedState n) (Fin 3 → ℝ)).comp
    (splitContinuous n).symm.toContinuousLinearMap

theorem oldProjection_apply {n : ℕ} (y : ReducedState (n+1)) :
    oldProjection n y=oldCoordinates y := rfl

theorem normalProjectionCLM_apply {n : ℕ} (y : ReducedState (n+1)) :
    normalProjectionCLM n y=normalProjection y := rfl

def normalInclusion (n : ℕ) : (Fin 3 → ℝ) →L[ℝ] ReducedState (n+1) :=
  (splitContinuous n).toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ (ReducedState n) (Fin 3 → ℝ))

theorem normalInclusion_apply {n : ℕ} (z : Fin 3 → ℝ) :
    normalInclusion n z=appendReduced 0 (z 0) (z 1) (z 2) := rfl

theorem split_decomposition {n : ℕ} (y : ReducedState n) (z : Fin 3 → ℝ) :
    splitEquiv n (y,z)=faceInclusion n y+normalInclusion n z := by
  change appendReduced y (z 0) (z 1) (z 2)=
    appendReduced y 0 0 0+appendReduced 0 (z 0) (z 1) (z 2)
  simpa only [add_zero,zero_add] using appendReduced_add y 0 0 0 0 (z 0) (z 1) (z 2)

theorem oldCoordinates_face {n : ℕ} (y : ReducedState n) :
    oldCoordinates (faceInclusion n y)=y := oldCoordinates_append y 0 0 0

theorem normalProjection_face {n : ℕ} (y : ReducedState n) :
    normalProjection (faceInclusion n y)=0 := by
  change normalProjection (appendReduced y 0 0 0) = 0
  rw [normalProjection_append]
  funext i
  fin_cases i <;> rfl

theorem oldCoordinates_normal {n : ℕ} (z : Fin 3 → ℝ) :
    oldCoordinates (normalInclusion n z)=0 := oldCoordinates_append 0 (z 0) (z 1) (z 2)

theorem normalProjection_normal {n : ℕ} (z : Fin 3 → ℝ) :
    normalProjection (normalInclusion n z)=z := by
  rw [normalInclusion_apply,normalProjection_append]
  funext i
  fin_cases i <;> rfl

end
end ThreeSitePhosphorylation.MultisiteSplit
