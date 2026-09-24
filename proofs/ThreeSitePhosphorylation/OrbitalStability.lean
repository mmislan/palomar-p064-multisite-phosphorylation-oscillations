import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! A local return-map criterion for attraction to an orbit as a set.
The return map and its contraction estimate are hypotheses, not conclusions
about the phosphorylation source. No phase convergence is assumed. -/
namespace ThreeSitePhosphorylation.OrbitalStability

open Filter
open scoped Topology

variable {E A : Type*} [MetricSpace E]

/-- A radial contraction on a section ball keeps every iterate in that ball
and gives a geometric error bound. Full pairwise contractivity is unnecessary. -/
theorem local_return_bound (P : E → E) (p x : E) (q δ : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hx : dist x p < δ)
    (hP : ∀ y, dist y p < δ → dist (P y) p ≤ q * dist y p) :
    ∀ n : ℕ, dist (P^[n] x) p ≤ q ^ n * dist x p ∧ dist (P^[n] x) p < δ := by
  intro n
  induction n with
  | zero => simpa using And.intro (le_refl (dist x p)) hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hb : dist (P (P^[n] x)) p ≤ q ^ (n + 1) * dist x p := by
      calc
        _ ≤ q * dist (P^[n] x) p := hP _ ih.2
        _ ≤ q * (q ^ n * dist x p) := mul_le_mul_of_nonneg_left ih.1 hq
        _ = _ := by ring
    refine ⟨hb, lt_of_le_of_lt ?_ hx⟩
    exact hb.trans (mul_le_of_le_one_left dist_nonneg (pow_le_one₀ hq hq1))

/-- Uniform control of each arc upgrades the discrete return-map estimate
to distance from the whole reference orbit, uniformly in phase. -/
theorem orbit_distance_bound (P : E → E) (arc : A → E → E) (p x : E)
    (q δ C : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hC : 0 ≤ C)
    (hx : dist x p < δ)
    (hP : ∀ y, dist y p < δ → dist (P y) p ≤ q * dist y p)
    (ha : ∀ s y, dist y p < δ → dist (arc s y) (arc s p) ≤ C * dist y p)
    (n : ℕ) (s : A) :
    Metric.infDist (arc s (P^[n] x)) (Set.range (fun a => arc a p)) ≤
      C * (q ^ n * dist x p) := by
  obtain ⟨hb, hi⟩ := local_return_bound P p x q δ hq hq1 hx hP n
  exact (Metric.infDist_le_dist_of_mem (Set.mem_range_self s)).trans
    ((ha s _ hi).trans (mul_le_mul_of_nonneg_left hb hC))

/-- Tube stability, uniformly in the number of returns and in arc phase. -/
theorem orbit_tube_stability (P : E → E) (arc : A → E → E) (p : E)
    (q δ C : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hP : ∀ y, dist y p < δ → dist (P y) p ≤ q * dist y p)
    (ha : ∀ s y, dist y p < δ → dist (arc s y) (arc s p) ≤ C * dist y p) :
    ∀ ε > 0, ∃ η > 0, ∀ x, dist x p < η → ∀ n s,
      Metric.infDist (arc s (P^[n] x)) (Set.range (fun a => arc a p)) < ε := by
  intro ε hε
  have hCp : 0 < C + 1 := by linarith
  refine ⟨min δ (ε / (C + 1)), lt_min hδ (div_pos hε hCp), ?_⟩
  intro x hx n s
  have hxδ := lt_of_lt_of_le hx (min_le_left _ _)
  have hxε := lt_of_lt_of_le hx (min_le_right _ _)
  have hb := orbit_distance_bound P arc p x q δ C hq hq1 hC hxδ hP ha n s
  have hp : q ^ n * dist x p ≤ dist x p :=
    mul_le_of_le_one_left dist_nonneg (pow_le_one₀ hq hq1)
  have he : (C + 1) * dist x p < ε := by
    have := (lt_div_iff₀ hCp).1 hxε
    nlinarith
  calc
    _ ≤ C * (q ^ n * dist x p) := hb
    _ ≤ C * dist x p := mul_le_mul_of_nonneg_left hp hC
    _ ≤ (C + 1) * dist x p := by nlinarith [dist_nonneg (x := x) (y := p)]
    _ < ε := he

/-- Arbitrary phase changes are allowed. If the return count tends to infinity,
the interpolated trajectory converges to the reference orbit as a set. A real
flow application must separately prove this decomposition and non-Zeno returns. -/
theorem orbit_attraction {ι : Type*} (l : Filter ι) (count : ι → ℕ) (phase : ι → A)
    (hc : Tendsto count l atTop) (P : E → E) (arc : A → E → E) (p x : E)
    (q δ C : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (hC : 0 ≤ C)
    (hx : dist x p < δ)
    (hP : ∀ y, dist y p < δ → dist (P y) p ≤ q * dist y p)
    (ha : ∀ s y, dist y p < δ → dist (arc s y) (arc s p) ≤ C * dist y p) :
    Tendsto (fun t => Metric.infDist (arc (phase t) (P^[count t] x))
      (Set.range (fun a => arc a p))) l (𝓝 0) := by
  have ht : Tendsto (fun t => C * (q ^ count t * dist x p)) l (𝓝 0) := by
    simpa using (((tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).comp hc).mul_const
      (dist x p)).const_mul C
  exact squeeze_zero (fun _ => Metric.infDist_nonneg)
    (fun t => orbit_distance_bound P arc p x q δ C hq hq1.le hC hx hP ha _ _) ht

end ThreeSitePhosphorylation.OrbitalStability
