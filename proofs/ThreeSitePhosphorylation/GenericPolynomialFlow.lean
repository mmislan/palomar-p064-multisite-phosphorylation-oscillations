import proofs.ThreeSitePhosphorylation.PolynomialPathLift
import proofs.ThreeSitePhosphorylation.NonlinearPathIFT

/-! Full-interval local paths for a literal finite quadratic polynomial field.
The smooth path lift is constructed, rather than assumed as extra input. -/
namespace ThreeSitePhosphorylation.GenericPolynomialFlow
noncomputable section
open scoped BigOperators Topology
open PolynomialPathLift
open MeasureTheory

variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

def field (e : ι → E) (c α β : ι → P → ℝ) (ℓ m : ι → E →L[ℝ] ℝ)
    (p : P) (x : E) : E :=
  ∑ i, (c i p*((α i p+ℓ i x)*(β i p+m i x))) • e i

def pathField (e : ι → E) (c α β : ι → P → ℝ) (ℓ m : ι → E →L[ℝ] ℝ)
    (p : P) (u : ContinuousPath E) : ContinuousPath E :=
  injectedSum e (fun i => polynomialRow (c i) (α i) (β i) (ℓ i) (m i)) p u

theorem field_smooth (e : ι → E) (c α β : ι → P → ℝ)
    (ℓ m : ι → E →L[ℝ] ℝ) (hc : ∀ i, ContDiff ℝ ⊤ (c i))
    (hα : ∀ i, ContDiff ℝ ⊤ (α i)) (hβ : ∀ i, ContDiff ℝ ⊤ (β i)) :
    ContDiff ℝ ⊤ (fun p : P × E => field e c α β ℓ m p.1 p.2) := by
  apply ContDiff.sum
  intro i _
  have hs := ((hc i).comp (contDiff_fst : ContDiff ℝ ⊤ (Prod.fst : P × E → P))).mul
    ((((hα i).comp contDiff_fst).add ((ℓ i).contDiff.comp contDiff_snd)).mul
      (((hβ i).comp contDiff_fst).add ((m i).contDiff.comp contDiff_snd)))
  exact hs.smul contDiff_const

theorem pathField_smooth (e : ι → E) (c α β : ι → P → ℝ)
    (ℓ m : ι → E →L[ℝ] ℝ) (hc : ∀ i, ContDiff ℝ ⊤ (c i))
    (hα : ∀ i, ContDiff ℝ ⊤ (α i)) (hβ : ∀ i, ContDiff ℝ ⊤ (β i)) :
    ContDiff ℝ ⊤ (fun p : P × ContinuousPath E => pathField e c α β ℓ m p.1 p.2) :=
  polynomial_injectedSum_smooth e c α β ℓ m hc hα hβ

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem pathField_apply (e : ι → E) (c α β : ι → P → ℝ)
    (ℓ m : ι → E →L[ℝ] ℝ) (p : P) (u : ContinuousPath E) (t : UnitTime) :
    pathField e c α β ℓ m p u t=field e c α β ℓ m p (u t) :=
  polynomial_injectedSum_apply e c α β ℓ m p u t

/-- Every supplied reference solution of this literal polynomial integral
equation admits a smooth, locally unique full-interval family. This is an
initial-value result, not periodic shooting or a Hopf existence theorem. -/
theorem smooth_paths [CompleteSpace P] [CompleteSpace E] (e : ι → E) (c α β : ι → P → ℝ)
    (ℓ m : ι → E →L[ℝ] ℝ) (hc : ∀ i, ContDiff ℝ ⊤ (c i))
    (hα : ∀ i, ContDiff ℝ ⊤ (α i)) (hβ : ∀ i, ContDiff ℝ ⊤ (β i))
    (d : NonlinearPathData P E) (u : ContinuousPath E)
    (hu : nonlinearPathResidual (pathField e c α β ℓ m) (d,u)=0) :
    ∃ ψ : NonlinearPathData P E → ContinuousPath E,
      ContDiffAt ℝ ⊤ ψ d ∧ ψ d=u ∧
      (∀ᶠ p in 𝓝 d, nonlinearPathResidual (pathField e c α β ℓ m) (p,ψ p)=0) ∧
      (∀ᶠ p in 𝓝 (d,u), nonlinearPathResidual (pathField e c α β ℓ m) p=0 ↔ ψ p.1=p.2) ∧
      (∀ᶠ p in 𝓝 d, ∀ t : UnitTime,
        ψ p t=p.2+∫ s in (0:ℝ)..(t:ℝ),
          p.1.2 • field e c α β ℓ m p.1.1 (pathExtension (ψ p) s)) := by
  exact smooth_nonlinear_full_interval_paths (field e c α β ℓ m)
    (pathField e c α β ℓ m) (field_smooth e c α β ℓ m hc hα hβ)
    (pathField_smooth e c α β ℓ m hc hα hβ) (pathField_apply e c α β ℓ m) d u hu

end
end ThreeSitePhosphorylation.GenericPolynomialFlow
