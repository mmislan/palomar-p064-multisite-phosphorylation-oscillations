import Mathlib.Analysis.Calculus.FDeriv.Basic
import proofs.ThreeSitePhosphorylation.OrbitalStability

/-! An ordinary derivative at a fixed point suffices for radial contraction.
The derivative bound is an explicit hypothesis, not a source stability claim. -/
namespace ThreeSitePhosphorylation.OrbitalStability

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem derivative_radial_contraction (P : E → E) (p : E) (A : E →L[ℝ] E)
    (hp : P p = p) (hD : HasFDerivAt P A p) (hA : ‖A‖ < 1) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∃ δ > 0,
      ∀ y, dist y p < δ → dist (P y) p ≤ q * dist y p := by
  let ε : ℝ := (1 - ‖A‖) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have he := hD.isLittleO.bound hε
  obtain ⟨δ,hδ,hbound⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨‖A‖ + ε, by positivity, ?_, δ, hδ, ?_⟩
  · dsimp [ε]; linarith
  intro y hy
  have hb := hbound hy
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖P y - p‖ = ‖(P y - P p - A (y-p)) + A (y-p)‖ := by rw [hp]; congr 1; abel
    _ ≤ ‖P y - P p - A (y-p)‖ + ‖A (y-p)‖ := norm_add_le _ _
    _ ≤ ε * ‖y-p‖ + ‖A‖ * ‖y-p‖ := add_le_add hb (A.le_opNorm _)
    _ = (‖A‖ + ε) * ‖y-p‖ := by ring

theorem derivative_return_bound (P : E → E) (p : E) (A : E →L[ℝ] E)
    (hp : P p = p) (hD : HasFDerivAt P A p) (hA : ‖A‖ < 1) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∃ δ > 0, ∀ x, dist x p < δ →
      ∀ n : ℕ, dist (P^[n] x) p ≤ q ^ n * dist x p ∧ dist (P^[n] x) p < δ := by
  obtain ⟨q,hq,hq1,δ,hδ,hP⟩ := derivative_radial_contraction P p A hp hD hA
  exact ⟨q,hq,hq1,δ,hδ,fun x hx => local_return_bound P p x q δ hq hq1.le hx hP⟩

end ThreeSitePhosphorylation.OrbitalStability
