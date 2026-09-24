import proofs.ThreeSitePhosphorylation.ScaledMultisiteCenteredFace
import proofs.ThreeSitePhosphorylation.MultisiteSmoothField

/-! The actual joint load/kinetic-parameter source family for scaled site
addition. Algebra and smoothness hold for signed loads; positivity is separate. -/
namespace ThreeSitePhosphorylation.ScaledJointSource
noncomputable section
open PhosphorylationSharpness MultisiteChart MultisiteSource MultisiteCenteredFace
open ScaledMultisiteSource MultisiteSmoothField

def jointRates {n : ℕ} (k : ℝ → Rates n) (x : PhosphorylationSharpness.State n)
    (κ : ℝ) (p : ℝ × ℝ) : Rates (n+1) :=
  appendScaledRates (k p.2) κ (2*κ*p.1/(x.S (Fin.last n)*x.E)) (κ/x.F)

def center {n : ℕ} (x : PhosphorylationSharpness.State n) (ε : ℝ) : ReducedState (n+1) :=
  appendReduced (project x) ε (2*ε) ε

def jointField {n : ℕ} (k : ℝ → Rates n) (x : PhosphorylationSharpness.State n)
    (κ : ℝ) (p : ℝ × ℝ) (y : ReducedState (n+1)) : ReducedState (n+1) :=
  centeredField (totalE x+p.1) (totalF x+p.1) (totalS x+4*p.1)
    (jointRates k x κ p) (center x p.1) y

theorem jointRates_smooth {n : ℕ} (k : ℝ → Rates n)
    (x : PhosphorylationSharpness.State n) (κ : ℝ) (hk : RatesSmooth k) :
    RatesSmooth (jointRates k x κ) := by
  obtain ⟨ha,hb,hc,hα,hβ,hγ⟩ := hk
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [jointRates,appendScaledRates,Fin.lastCases_last]
      exact (contDiff_const.mul contDiff_fst).div_const _
    · simpa only [jointRates,appendScaledRates,Fin.lastCases_castSucc] using
        (ha j).comp contDiff_snd
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [jointRates,appendScaledRates,Fin.lastCases_last] using
        (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => κ))
    · simpa only [jointRates,appendScaledRates,Fin.lastCases_castSucc] using
        (hb j).comp contDiff_snd
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [jointRates,appendScaledRates,Fin.lastCases_last] using
        (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => κ))
    · simpa only [jointRates,appendScaledRates,Fin.lastCases_castSucc] using
        (hc j).comp contDiff_snd
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [jointRates,appendScaledRates,Fin.lastCases_last] using
        (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => κ/x.F))
    · simpa only [jointRates,appendScaledRates,Fin.lastCases_castSucc] using
        (hα j).comp contDiff_snd
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [jointRates,appendScaledRates,Fin.lastCases_last] using
        (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => κ))
    · simpa only [jointRates,appendScaledRates,Fin.lastCases_castSucc] using
        (hβ j).comp contDiff_snd
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [jointRates,appendScaledRates,Fin.lastCases_last] using
        (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ × ℝ => κ))
    · simpa only [jointRates,appendScaledRates,Fin.lastCases_castSucc] using
        (hγ j).comp contDiff_snd

theorem center_smooth {n : ℕ} (x : PhosphorylationSharpness.State n) :
    ContDiff ℝ ⊤ (center x) := by
  have hs : ContDiff ℝ ⊤ (fun ε : ℝ => (center x ε).1) := by
    apply contDiff_pi.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp only [center,appendReduced,Fin.lastCases_last,Fin.lastCases_castSucc] <;> fun_prop
  have hc : ContDiff ℝ ⊤ (fun ε : ℝ => (center x ε).2.1) := by
    apply contDiff_pi.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp only [center,appendReduced,Fin.lastCases_last,Fin.lastCases_castSucc] <;> fun_prop
  have hd : ContDiff ℝ ⊤ (fun ε : ℝ => (center x ε).2.2) := by
    apply contDiff_pi.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp only [center,appendReduced,Fin.lastCases_last,Fin.lastCases_castSucc] <;> fun_prop
  exact hs.prodMk (hc.prodMk hd)

/-- No assumed field smoothness: the literal rate components, inventory
functions, and moving chart center supply the joint smoothness. -/
theorem jointField_smooth {n : ℕ} (k : ℝ → Rates n)
    (x : PhosphorylationSharpness.State n) (κ : ℝ) (hk : RatesSmooth k) :
    ContDiff ℝ ⊤ (fun q : (ℝ × ℝ) × ReducedState (n+1) => jointField k x κ q.1 q.2) := by
  have hE : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => totalE x+p.1) := by fun_prop
  have hF : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => totalF x+p.1) := by fun_prop
  have hS : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => totalS x+4*p.1) := by fun_prop
  have hred := reducedField_joint_smooth (jointRates k x κ)
    (fun p => totalE x+p.1) (fun p => totalF x+p.1) (fun p => totalS x+4*p.1)
    (jointRates_smooth k x κ hk) hE hF hS
  have hshift : ContDiff ℝ ⊤
      (fun q : (ℝ × ℝ) × ReducedState (n+1) => (q.1,center x q.1.1+q.2)) :=
    contDiff_fst.prodMk (((center_smooth x).comp (contDiff_fst.comp contDiff_fst)).add contDiff_snd)
  have he : (fun q : (ℝ × ℝ) × ReducedState (n+1) => jointField k x κ q.1 q.2) =
      (fun p : (ℝ × ℝ) × ReducedState (n+1) =>
        reducedField (totalE x+p.1.1) (totalF x+p.1.1) (totalS x+4*p.1.1)
          (jointRates k x κ p.1) p.2) ∘
        (fun q : (ℝ × ℝ) × ReducedState (n+1) => (q.1,center x q.1.1+q.2)) := by
    funext q
    rfl
  rw [he]
  exact hred.comp hshift

theorem chart_center {n : ℕ} (x : PhosphorylationSharpness.State n) (ε : ℝ) :
    chart (totalE x+ε) (totalF x+ε) (totalS x+4*ε) (center x ε) =
      appendState x ε (2*ε) ε := by
  have h := chart_appendReduced (totalE x) (totalF x) (totalS x) (project x) ε (2*ε) ε
  rw [chart_project] at h
  have ht : totalS x+ε+2*ε+ε=totalS x+4*ε := by ring
  rw [ht] at h
  exact h

/-- Signed-load equilibrium identity from the actual full chemical source. -/
theorem jointField_zero {n : ℕ} (k : ℝ → Rates n)
    (x : PhosphorylationSharpness.State n) (κ : ℝ)
    (heq : ∀ r, Equilibrium (k r) x)
    (hs : x.S (Fin.last n) ≠ 0) (hE : x.E ≠ 0) (hF : x.F ≠ 0)
    (p : ℝ × ℝ) : jointField k x κ p 0 = 0 := by
  have h := scaled_append_equilibrium (k p.2) x (heq p.2) hs hE hF κ p.1
  change project (field (jointRates k x κ p)
    (chart (totalE x+p.1) (totalF x+p.1) (totalS x+4*p.1) (center x p.1+0))) = 0
  rw [add_zero,chart_center]
  apply Prod.ext
  · exact funext (fun i => h.1 i.succ)
  · apply Prod.ext
    · exact funext h.2.2.2.1
    · exact funext h.2.2.2.2

theorem jointField_zero_of_positive {n : ℕ} (k : ℝ → Rates n)
    (x : PhosphorylationSharpness.State n) (κ : ℝ)
    (heq : ∀ r, Equilibrium (k r) x) (hx : x.Positive) (p : ℝ × ℝ) :
    jointField k x κ p 0 = 0 :=
  jointField_zero k x κ heq (ne_of_gt (hx.1 _)) (ne_of_gt hx.2.1)
    (ne_of_gt hx.2.2.1) p

theorem jointRates_center_positive {n : ℕ} (k : ℝ → Rates n)
    (x : PhosphorylationSharpness.State n) (κ : ℝ) (p : ℝ × ℝ)
    (hk : (k p.2).Positive) (hx : x.Positive) (hκ : 0<κ) (hε : 0<p.1) :
    (jointRates k x κ p).Positive ∧ (appendState x p.1 (2*p.1) p.1).Positive :=
  scaled_append_positive (k p.2) x hk hx κ p.1 hκ hε

end
end ThreeSitePhosphorylation.ScaledJointSource
