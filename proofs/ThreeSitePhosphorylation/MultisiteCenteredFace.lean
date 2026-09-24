import proofs.ThreeSitePhosphorylation.MultisiteChart
import proofs.ThreeSitePhosphorylation.MultisiteSource

/-! Uniform actual reduced-source restriction on the added-site zero-load
face. All conservation-class reconstruction corrections are retained. -/
namespace ThreeSitePhosphorylation.MultisiteCenteredFace
noncomputable section
open MultisiteChart
open MultisiteSource
set_option maxHeartbeats 500000

/-- Old reduced arrays are retained; the new coordinates have order C,S,D
in the arguments, consistently with the literal full-state append operation. -/
def appendReduced {n : ℕ} (y : ReducedState n) (c s d : ℝ) : ReducedState (n+1) :=
  (Fin.lastCases s y.1,(Fin.lastCases c y.2.1,Fin.lastCases d y.2.2))

theorem project_appendState {n : ℕ} (x : PhosphorylationSharpness.State n)
    (c s d : ℝ) :
    project (appendState x c s d)=appendReduced (project x) c s d := by
  apply Prod.ext
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [project,appendState,appendReduced]
    · simp [project,appendState,appendReduced,← Fin.castSucc_succ]
  · rfl

/-- The shifts in inventories exactly account for the newly appended species.
In particular this identity does not discard the omitted S0,E,F equations. -/
theorem chart_appendReduced {n : ℕ} (Et Ft St : ℝ) (y : ReducedState n)
    (c s d : ℝ) :
    chart (Et+c) (Ft+d) (St+c+s+d) (appendReduced y c s d)=
      appendState (chart Et Ft St y) c s d := by
  have h := append_totals (chart Et Ft St y) c s d
  have g := chart_totals Et Ft St y
  have hp : project (appendState (chart Et Ft St y) c s d)=appendReduced y c s d := by
    rw [project_appendState,project_chart]
  rw [← hp]
  apply chart_project_of_totals
  · simpa only [g.1] using h.1
  · simpa only [g.2.1] using h.2.1
  · simpa only [g.2.2] using h.2.2

theorem chart_zero_append {n : ℕ} (Et Ft St : ℝ) (y : ReducedState n) :
    chart Et Ft St (appendReduced y 0 0 0)=appendState (chart Et Ft St y) 0 0 0 := by
  simpa only [add_zero] using chart_appendReduced Et Ft St y 0 0 0

/-- Intertwining of the actual reduced mass-action vector fields, uniformly
in the site count and the remaining new phosphatase binding constant. -/
theorem reducedField_zero_load {n : ℕ} (Et Ft St : ℝ)
    (k : PhosphorylationSharpness.Rates n) (α : ℝ) (y : ReducedState n) :
    reducedField Et Ft St (appendRates k 0 α) (appendReduced y 0 0 0)=
      appendReduced (reducedField Et Ft St k y) 0 0 0 := by
  unfold reducedField
  rw [chart_zero_append,zero_load_face,project_appendState]

theorem appendReduced_add {n : ℕ} (x y : ReducedState n)
    (c s d c' s' d' : ℝ) :
    appendReduced (x+y) (c+c') (s+s') (d+d')=
      appendReduced x c s d + appendReduced y c' s' d' := by
  ext i <;> refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [appendReduced]

theorem appendReduced_smul {n : ℕ} (a : ℝ) (y : ReducedState n) (c s d : ℝ) :
    appendReduced (a • y) (a*c) (a*s) (a*d)=a • appendReduced y c s d := by
  ext i <;> refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [appendReduced]

/-- The zero-normal-coordinate inclusion is linear on the existing normed
reduced spaces. No structure is introduced on full structured states. -/
def faceInclusion (n : ℕ) : ReducedState n →ₗ[ℝ] ReducedState (n+1) where
  toFun y := appendReduced y 0 0 0
  map_add' x y := by simpa only [zero_add] using appendReduced_add x y 0 0 0 0 0 0
  map_smul' a y := by simpa only [mul_zero] using appendReduced_smul a y 0 0 0

/-- Translation of the actual reduced field to coordinates about zstar.
No equilibrium equation is assumed or subtracted from the vector field. -/
def centeredField {n : ℕ} (Et Ft St : ℝ) (k : PhosphorylationSharpness.Rates n)
    (zstar y : ReducedState n) : ReducedState n :=
  reducedField Et Ft St k (zstar+y)

/-- The centered zero-load restriction needed before differentiating the
actual source to obtain Jacobian, Hessian, and parameter restrictions. -/
theorem centeredField_zero_load {n : ℕ} (Et Ft St : ℝ)
    (k : PhosphorylationSharpness.Rates n) (α : ℝ) (zstar y : ReducedState n) :
    centeredField Et Ft St (appendRates k 0 α) (faceInclusion n zstar) (faceInclusion n y)=
      faceInclusion n (centeredField Et Ft St k zstar y) := by
  change reducedField Et Ft St (appendRates k 0 α)
      (faceInclusion n zstar + faceInclusion n y)=_
  rw [← (faceInclusion n).map_add]
  exact reducedField_zero_load Et Ft St k α (zstar+y)

end
end ThreeSitePhosphorylation.MultisiteCenteredFace
