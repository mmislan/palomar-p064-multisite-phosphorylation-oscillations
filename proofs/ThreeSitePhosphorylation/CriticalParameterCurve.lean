import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Banach

namespace ThreeSitePhosphorylation.CriticalParameterCurve
noncomputable section
open scoped Topology

/-- A nonzero actual parameter derivative supplies the scalar IFT inverse. -/
theorem scalar_curve (F : ℝ × ℝ → ℝ) (r0 c : ℝ)
    (hF : ContDiffAt ℝ ⊤ F (0,r0)) (hzero : F (0,r0)=0)
    (hd : HasDerivAt (fun r => F (0,r)) c r0) (hc : c≠0) :
    ∃ R : ℝ → ℝ, ContDiffAt ℝ ⊤ R 0 ∧ R 0=r0 ∧
      (∀ᶠ ε in 𝓝 (0:ℝ), F (ε,R ε)=0) ∧
      ∀ᶠ d in 𝓝 ((0:ℝ),r0), F d=0 ↔ R d.1=d.2 := by
  let J := fderiv ℝ F (0,r0) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ
  have hi : HasFDerivAt (fun r : ℝ => ((0:ℝ),r))
      (ContinuousLinearMap.inr ℝ ℝ ℝ) r0 := by
    convert (hasFDerivAt_const (0:ℝ) r0).prodMk (hasFDerivAt_id r0) using 1
  have hslice : HasFDerivAt (fun r => F (0,r)) J r0 :=
    (hF.differentiableAt (by simp)).hasFDerivAt.comp r0 hi
  have hJ1 : J 1=c := hslice.hasDerivAt.unique hd
  have hJ (t : ℝ) : J t=t*c := by
    have hh := J.map_smul t (1:ℝ)
    simpa only [smul_eq_mul,mul_one,hJ1] using hh
  have hbij : Function.Bijective J := by
    constructor
    · intro x y hxy
      exact mul_right_cancel₀ hc (by simpa only [hJ] using hxy)
    · intro y
      exact ⟨y/c,by rw [hJ,div_mul_cancel₀ _ hc]⟩
  have hInv : J.IsInvertible := by
    obtain ⟨u,hu⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr hbij
    exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ ℝ u,hu⟩
  let R := hF.implicitFunction (by simp) hInv
  refine ⟨R,hF.contDiffAt_implicitFunction (by simp) hInv,
    hF.implicitFunction_apply_self (by simp) hInv,?_,?_⟩
  · simpa only [hzero] using hF.eventually_apply_implicitFunction (by simp) hInv
  · simpa only [hzero] using hF.eventually_apply_eq_iff_implicitFunction (by simp) hInv

/-- The continued complex eigenvalue is purely imaginary on an actual
smooth parameter curve, and its imaginary part remains positive. This
statement assumes no spectral facts beyond the supplied function data. -/
theorem complex_curve (μ : ℝ × ℝ → ℂ) (r0 w0 c : ℝ)
    (hμ : ContDiffAt ℝ ⊤ μ (0,r0))
    (hμ0 : μ (0,r0)=Complex.I*(w0:ℂ)) (hw : 0<w0)
    (hd : HasDerivAt (fun r => (μ (0,r)).re) c r0) (hc : c≠0) :
    ∃ R : ℝ → ℝ, ContDiffAt ℝ ⊤ R 0 ∧ R 0=r0 ∧
      (∀ᶠ ε in 𝓝 (0:ℝ), (μ (ε,R ε)).re=0 ∧ 0<(μ (ε,R ε)).im) ∧
      ∀ᶠ d in 𝓝 ((0:ℝ),r0), (μ d).re=0 ↔ R d.1=d.2 := by
  have hF : ContDiffAt ℝ ⊤ (fun d => (μ d).re) (0,r0) :=
    Complex.reCLM.contDiff.contDiffAt.comp (0,r0) hμ
  have hz : (μ (0,r0)).re=0 := by simp [hμ0]
  obtain ⟨R,hR,hR0,he,huniq⟩ := scalar_curve (fun d => (μ d).re) r0 c hF hz hd hc
  have harg : ContinuousAt (fun ε => (ε,R ε)) 0 :=
    continuousAt_id.prodMk hR.continuousAt
  have hcomp : ContinuousAt (fun ε => μ (ε,R ε)) 0 := by
    apply ContinuousAt.comp (f := fun ε => (ε,R ε)) _ harg
    simpa only [hR0] using hμ.continuousAt
  have him : ContinuousAt (fun ε => (μ (ε,R ε)).im) 0 :=
    Complex.imCLM.continuous.continuousAt.comp hcomp
  have hpos : 0<(μ ((0:ℝ),R 0)).im := by simpa [hR0,hμ0] using hw
  refine ⟨R,hR,hR0,?_,huniq⟩
  filter_upwards [he,him.tendsto.eventually (Ioi_mem_nhds hpos)] with ε hre hε
  exact ⟨hre,hε⟩

end
end ThreeSitePhosphorylation.CriticalParameterCurve
