import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach

namespace ThreeSitePhosphorylation.LinearEndpointInjective
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Backward uniqueness makes every finite-time linear evolution injective.
The left derivative at the final time is sufficient; no spectral hypothesis
or expansion of a fundamental matrix is needed. -/
theorem endpoint_injective (A L : ℝ → E →L[ℝ] E) (T : ℝ) (hT : 0≤T)
    (K : NNReal) (hA : ∀ t ∈ Set.Ioc (0:ℝ) T, ‖A t‖≤K)
    (hL0 : L 0=1)
    (hcont : ∀ x, ContinuousOn (fun t => L t x) (Set.Icc (0:ℝ) T))
    (hderiv : ∀ x t, t ∈ Set.Ioc (0:ℝ) T →
      HasDerivWithinAt (fun s => L s x) (A t (L t x)) (Set.Iic t) t) :
    Function.Injective (L T) := by
  have hlip : ∀ t ∈ Set.Ioc (0:ℝ) T,
      LipschitzOnWith K (A t) (Set.univ : Set E) := by
    intro t ht
    exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le (hA t ht)).lipschitzOnWith
  intro x y hxy
  have he := ODE_solution_unique_of_mem_Icc_left hlip (hcont x)
    (fun t ht => hderiv x t ht) (fun _ _ => Set.mem_univ _) (hcont y)
    (fun t ht => hderiv y t ht) (fun _ _ => Set.mem_univ _) hxy
  have hz := he (show (0:ℝ) ∈ Set.Icc (0:ℝ) T from ⟨le_rfl,hT⟩)
  simpa only [hL0,ContinuousLinearMap.one_apply] using hz

/-- In finite dimension, backward uniqueness supplies the invertible
endpoint derivative needed for an open fixed-time solution map. -/
theorem endpoint_isUnit [FiniteDimensional ℝ E]
    (A L : ℝ → E →L[ℝ] E) (T : ℝ) (hT : 0≤T)
    (K : NNReal) (hA : ∀ t ∈ Set.Ioc (0:ℝ) T, ‖A t‖≤K)
    (hL0 : L 0=1)
    (hcont : ∀ x, ContinuousOn (fun t => L t x) (Set.Icc (0:ℝ) T))
    (hderiv : ∀ x t, t ∈ Set.Ioc (0:ℝ) T →
      HasDerivWithinAt (fun s => L s x) (A t (L t x)) (Set.Iic t) t) :
    IsUnit (L T) := by
  have hi := endpoint_injective A L T hT K hA hL0 hcont hderiv
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hi,(LinearMap.injective_iff_surjective (f := (L T).toLinearMap)).mp hi⟩

end
end ThreeSitePhosphorylation.LinearEndpointInjective
