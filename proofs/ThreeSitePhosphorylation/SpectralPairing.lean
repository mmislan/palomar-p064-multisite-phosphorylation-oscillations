import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace ThreeSitePhosphorylation.SpectralPairing
open Filter
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]

/-- Differentiating a genuine eigenbranch identifies the normalized left/right
parameter pairing. No companion matrix or explicit inverse is needed. -/
theorem eigenbranch_pairing (A : ℝ → V →L[ℝ] V) (dA : V →L[ℝ] V)
    (q : ℝ → V) (dq : V) (z : ℝ → ℂ) (dz : ℂ) (r : ℝ)
    (p : V →ₗ[ℂ] ℂ)
    (hA : HasDerivAt A dA r) (hq : HasDerivAt q dq r)
    (hz : HasDerivAt z dz r)
    (he : ∀ᶠ s in 𝓝 r, A s (q s) = z s • q s)
    (hp : ∀ v, p (A r v) = z r * p v) (hn : p (q r) = 1) :
    p (dA (q r)) = dz := by
  have ha := hA.clm_apply hq
  have hb := hz.smul hq
  have he' : (fun s => A s (q s)) =ᶠ[𝓝 r] (fun s => z s • q s) := he
  have hd := (ha.congr_of_eventuallyEq he'.symm).unique hb
  have h := congrArg p hd
  simp only [map_add,map_smul,smul_eq_mul,hp,hn,mul_one] at h
  linear_combination h

end ThreeSitePhosphorylation.SpectralPairing
