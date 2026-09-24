import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

namespace ThreeSitePhosphorylation.SmoothForwardUniqueness
noncomputable section
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Smooth autonomous fields have a Lipschitz bound on each closed ball.
The bound is derived from compactness, rather than assumed globally. -/
theorem closedBall_lipschitz (F : E → E) (hF : ContDiff ℝ ⊤ F)
    (c : E) (R : ℝ) : ∃ K : NNReal, LipschitzOnWith K F (Metric.closedBall c R) := by
  have hc : Continuous (fun x => ‖fderiv ℝ F x‖₊) :=
    (hF.continuous_fderiv (by simp)).nnnorm
  obtain ⟨K,hK⟩ := (isCompact_closedBall c R).bddAbove_image hc.continuousOn
  refine ⟨K,Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => hF.differentiable (by simp) x) ?_ (convex_closedBall c R)⟩
  intro x hx
  exact hK (mem_image_of_mem _ hx)

/-- Compare two actual solutions on a finite interval. Their compact images
provide a common ball, on which smoothness gives the needed Lipschitz bound. -/
theorem eqOn_Icc (F : E → E) (hF : ContDiff ℝ ⊤ F)
    (f g : ℝ → E) (a b : ℝ)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (F (f t)) (Ici t) t)
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (F (g t)) (Ici t) t)
    (hinit : f a=g a) : EqOn f g (Icc a b) := by
  have hc : IsCompact (f '' Icc a b ∪ g '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hf).union
      (isCompact_Icc.image_of_continuousOn hg)
  obtain ⟨R,hR⟩ := hc.isBounded.subset_closedBall (0:E)
  obtain ⟨K,hK⟩ := closedBall_lipschitz F hF (0:E) R
  have hfs : ∀ t ∈ Ico a b, f t ∈ Metric.closedBall (0:E) R := by
    intro t ht
    exact hR (Or.inl (mem_image_of_mem f ⟨ht.1,ht.2.le⟩))
  have hgs : ∀ t ∈ Ico a b, g t ∈ Metric.closedBall (0:E) R := by
    intro t ht
    exact hR (Or.inr (mem_image_of_mem g ⟨ht.1,ht.2.le⟩))
  exact ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => F) (s := fun _ => Metric.closedBall (0:E) R)
    (fun _ _ => hK) hf hf' hfs hg hg' hgs hinit

/-- Actual forward solutions of a smooth finite-dimensional autonomous field
with the same initial value agree at every nonnegative time. -/
theorem forward_unique (F : E → E) (hF : ContDiff ℝ ⊤ F)
    (f g : ℝ → E)
    (hf : ∀ t, 0≤t → HasDerivWithinAt f (F (f t)) (Ici 0) t)
    (hg : ∀ t, 0≤t → HasDerivWithinAt g (F (g t)) (Ici 0) t)
    (hinit : f 0=g 0) : ∀ t, 0≤t → f t=g t := by
  intro T hT
  have hfc : ContinuousOn f (Icc 0 T) := by
    intro t ht
    exact (hf t ht.1).continuousWithinAt.mono (fun _ hs => hs.1)
  have hgc : ContinuousOn g (Icc 0 T) := by
    intro t ht
    exact (hg t ht.1).continuousWithinAt.mono (fun _ hs => hs.1)
  have hfd : ∀ t ∈ Ico 0 T, HasDerivWithinAt f (F (f t)) (Ici t) t := by
    intro t ht
    exact (hf t ht.1).mono (fun _ hs => ht.1.trans hs)
  have hgd : ∀ t ∈ Ico 0 T, HasDerivWithinAt g (F (g t)) (Ici t) t := by
    intro t ht
    exact (hg t ht.1).mono (fun _ hs => ht.1.trans hs)
  exact eqOn_Icc F hF f g 0 T hfc hgc hfd hgd hinit ⟨hT,le_rfl⟩

end
end ThreeSitePhosphorylation.SmoothForwardUniqueness
