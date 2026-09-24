import proofs.ThreeSitePhosphorylation.AttractingCrossing
import proofs.ThreeSitePhosphorylation.SpectralPairing

namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section
open scoped Topology
set_option maxHeartbeats 1000000

def sourceOperator (r : ℝ) : (Fin 9 → ℂ) →L[ℝ] (Fin 9 → ℂ) :=
  (complexSource r).mulVecLin.toContinuousLinearMap.restrictScalars ℝ

theorem sourceOperator_apply (r : ℝ) (v : Fin 9 → ℂ) :
    sourceOperator r v = (complexSource r).mulVec v := rfl

theorem complexSource_affine (r : ℝ) :
    complexSource r = complexSource 0 + (r : ℂ) • (complexSource 1-complexSource 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [complexSource,sourceMatrix]

theorem sourceOperator_affine (r : ℝ) :
    sourceOperator r = sourceOperator 0 + r • (sourceOperator 1-sourceOperator 0) := by
  ext v i
  simp only [sourceOperator_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply]
  rw [complexSource_affine r,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.sub_mulVec]
  simp

theorem sourceOperator_derivative (r : ℝ) :
    HasDerivAt sourceOperator (sourceOperator 1-sourceOperator 0) r := by
  have he : sourceOperator = (fun s => sourceOperator 0+s • (sourceOperator 1-sourceOperator 0)) :=
    funext sourceOperator_affine
  convert ((hasDerivAt_id r).smul_const (sourceOperator 1-sourceOperator 0)).const_add
    (sourceOperator 0) using 1
  simp only [one_smul]

theorem adjugateVector_smooth : ContDiff ℝ ⊤ adjugateVector := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [adjugateVector] <;> fun_prop

/-- The actual source parameter pairing equals the previously certified
eigenvalue derivative quotient for any normalized left eigenfunctional. -/
theorem source_parameter_pairing (r : ℝ) (z : ℂ)
    (hp : candidatePolynomial r z=0) (hs : candidateSlope r z ≠ 0)
    (p : (Fin 9 → ℂ) →ₗ[ℂ] ℂ)
    (hleft : ∀ v, p ((complexSource r).mulVec v)=z*p v)
    (hn : p (adjugateVector z)=1) :
    p ((sourceOperator 1-sourceOperator 0) (adjugateVector z)) =
      -candidateParameter z/candidateSlope r z := by
  obtain ⟨g,hg,hgr,hge⟩ := simple_root_branch r z hp hs
  have hdg := (hg.differentiableAt (by simp)).hasDerivAt
  have hq := (adjugateVector_smooth.contDiffAt.comp r hg).differentiableAt (by simp)
  have hpair := SpectralPairing.eigenbranch_pairing sourceOperator
    (sourceOperator 1-sourceOperator 0) (fun s => adjugateVector (g s))
    (deriv (fun s => adjugateVector (g s)) r) g (deriv g r) r p
    (sourceOperator_derivative r) hq.hasDerivAt hdg
    (by
      filter_upwards [hge] with s hsp
      exact (source_root_eigenvector s (g s) hsp).2)
    (by simpa only [sourceOperator_apply,hgr] using hleft)
    (by simpa only [hgr] using hn)
  have hd := root_branch_derivative r g (hg.differentiableAt (by simp)) hge
    (by simpa only [hgr] using hs)
  simpa only [hgr,hd] using hpair

theorem source_parameter_pairing_negative (r w : ℝ) (hw : w ≠ 0)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0)
    (p : (Fin 9 → ℂ) →ₗ[ℂ] ℂ)
    (hleft : ∀ v, p ((complexSource r).mulVec v)=(Complex.I*(w:ℂ))*p v)
    (hn : p (adjugateVector (Complex.I*(w:ℂ)))=1) :
    (p ((sourceOperator 1-sourceOperator 0) (adjugateVector (Complex.I*(w:ℂ))))).re < 0 := by
  rw [source_parameter_pairing r _ hp (candidate_imaginary_root_simple r w hw hp) p hleft hn]
  exact candidate_crossing_negative r w hw hp

end
end ThreeSitePhosphorylation.AttractingWitness
