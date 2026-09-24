import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.Linarith

namespace ThreeSitePhosphorylation.ForwardSolutionShift
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An autonomous forward solution can be restarted at any nonnegative
physical time, including when that time crosses a return-arc seam. -/
theorem source (F : E → E) (v : ℝ → E) (σ : ℝ) (hσ : 0≤σ)
    (hv : ∀ t, 0≤t → HasDerivWithinAt v (F (v t)) (Set.Ici 0) t) :
    ∀ t, 0≤t → HasDerivWithinAt (fun s => v (s+σ))
      (F (v (t+σ))) (Set.Ici 0) t := by
  intro t ht
  have hh := (hv (t+σ) (add_nonneg ht hσ)).scomp t
    (((hasDerivAt_id t).add_const σ).hasDerivWithinAt)
    (show Set.MapsTo (fun s : ℝ => s+σ) (Set.Ici 0) (Set.Ici 0) from
      fun s hs => add_nonneg hs hσ)
  simpa only [Function.comp_apply,one_smul] using hh

theorem add_tendsto_atTop (σ : ℝ) :
    Tendsto (fun t : ℝ => t+σ) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  exact eventually_atTop.2 ⟨b-σ,fun t ht => by linarith⟩

omit [NormedSpace ℝ E] in
theorem orbit_attraction (v : ℝ → E) (Γ : Set E) (σ : ℝ)
    (hv : Tendsto (fun t => Metric.infDist (v t) Γ) atTop (𝓝 0)) :
    Tendsto (fun t => Metric.infDist (v (t+σ)) Γ) atTop (𝓝 0) :=
  hv.comp (add_tendsto_atTop σ)

end ThreeSitePhosphorylation.ForwardSolutionShift
