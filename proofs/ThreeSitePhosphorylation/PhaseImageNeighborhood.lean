import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Operator.Banach

namespace ThreeSitePhosphorylation.PhaseImageNeighborhood
noncomputable section
open Filter Set
open scoped Topology

variable {E F I : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- Interiors of phase images retain points of the reference orbit when each
phase map sends the neighborhood filter at the reference point onto the
neighborhood filter at its image. No common inverse or uniform derivative
bound over the phase index is required. -/
def phaseImages (Φ : I → E → F) (B : Set E) : Set F :=
  ⋃ s, interior (Φ s '' B)

omit [TopologicalSpace E] in
theorem phaseImages_open (Φ : I → E → F) (B : Set E) :
    IsOpen (phaseImages Φ B) := isOpen_iUnion (fun _ => isOpen_interior)

theorem reference_range_subset (Φ : I → E → F) (p : E) (B : Set E)
    (hB : B ∈ 𝓝 p) (hΦ : ∀ s, map (Φ s) (𝓝 p)=𝓝 (Φ s p)) :
    range (fun s => Φ s p) ⊆ phaseImages Φ B := by
  rintro _ ⟨s,rfl⟩
  apply mem_iUnion.mpr
  refine ⟨s,mem_interior_iff_mem_nhds.mpr ?_⟩
  rw [← hΦ s]
  exact image_mem_map hB

omit [TopologicalSpace E] in
theorem phaseImages_has_preimage (Φ : I → E → F) (B : Set E) {z : F}
    (hz : z ∈ phaseImages Φ B) : ∃ s x, x∈B ∧ Φ s x=z := by
  obtain ⟨s,hs⟩ := mem_iUnion.mp hz
  obtain ⟨x,hx,he⟩ := interior_subset hs
  exact ⟨s,x,hx,he⟩

end

section Derivative
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A genuine invertible strict derivative supplies the neighborhood-filter
identity used above. The operator must be the actual derivative. -/
theorem map_nhds_of_isUnit_derivative (f : E → E) (p : E) (L : E →L[ℝ] E)
    (hf : HasStrictFDerivAt f L p) (hL : IsUnit L) :
    map f (𝓝 p)=𝓝 (f p) := by
  apply hf.map_nhds_eq_of_surj
  exact LinearMap.range_eq_top.mpr
    (ContinuousLinearMap.isUnit_iff_bijective.mp hL).2

end Derivative
end ThreeSitePhosphorylation.PhaseImageNeighborhood
