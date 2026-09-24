import proofs.ThreeSitePhosphorylation.ScaledNormalSpectrum
import proofs.ThreeSitePhosphorylation.ScaledNormalJacobian

/-! Explicit real and complex eigenbases of the actual scaled normal block.
The ordering agrees with ScaledNormalSpectrum.normalRoots. -/
namespace ThreeSitePhosphorylation.NormalEigenbasis
noncomputable section
open ScaledNormalSpectrum ScaledNormalJacobian
set_option maxHeartbeats 500000

def realVectors : Fin 3 → Fin 3 → ℝ :=
  ![![0,(1-Real.sqrt 5)/2,1], ![1,0,-1], ![0,(1+Real.sqrt 5)/2,1]]

def complexVectors (i j : Fin 3) : ℂ := (realVectors i j : ℂ)

theorem realVectors_det : Matrix.det realVectors = Real.sqrt 5 := by
  simp [realVectors,Matrix.det_fin_three]
  ring

theorem realVectors_independent : LinearIndependent ℝ realVectors := by
  apply Matrix.linearIndependent_rows_of_det_ne_zero
  rw [realVectors_det]
  exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))

def realBasis : Module.Basis (Fin 3) ℝ (Fin 3 → ℝ) := by
  classical
  exact basisOfPiSpaceOfLinearIndependent realVectors_independent

@[simp] theorem realBasis_apply (i : Fin 3) : realBasis i = realVectors i := by
  classical
  exact congrFun (coe_basisOfPiSpaceOfLinearIndependent realVectors_independent) i

theorem complexVectors_det : Matrix.det complexVectors = (Real.sqrt 5 : ℂ) := by
  simp [complexVectors,realVectors,Matrix.det_fin_three]
  ring

theorem complexVectors_independent : LinearIndependent ℂ complexVectors := by
  apply Matrix.linearIndependent_rows_of_det_ne_zero
  rw [complexVectors_det]
  exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (show (0 : ℝ)<5 by norm_num)))

def complexBasis : Module.Basis (Fin 3) ℂ (Fin 3 → ℂ) := by
  classical
  exact basisOfPiSpaceOfLinearIndependent complexVectors_independent

@[simp] theorem complexBasis_apply (i : Fin 3) : complexBasis i = complexVectors i := by
  classical
  exact congrFun (coe_basisOfPiSpaceOfLinearIndependent complexVectors_independent) i

theorem real_eigen (κ : ℝ) (i : Fin 3) :
    κ • normalBlock (realVectors i) = normalRoots κ i • realVectors i := by
  have hs : (Real.sqrt (5 : ℝ))^2=5 := Real.sq_sqrt (by norm_num)
  have hks : κ*(Real.sqrt (5 : ℝ))^2=5*κ := by rw [hs]; ring
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [normalBlock_apply,realVectors,normalRoots] <;> nlinarith

theorem realBasis_eigen (κ : ℝ) (i : Fin 3) :
    (κ • normalBlock) (realBasis i) = normalRoots κ i • realBasis i := by
  simpa using real_eigen κ i

/-- Explicit link between the real Jacobian normal map and the actual
complex matrix used by the source spectral calculation. -/
theorem scaledBlock_mulVec_ofReal (κ : ℝ) (z : Fin 3 → ℝ) :
    (scaledBlock κ).mulVec (fun j => (z j : ℂ)) =
      fun j => ((κ • normalBlock z) j : ℂ) := by
  ext j
  fin_cases j <;>
    simp [scaledBlock,AddedSite.limitingBlock,normalBlock_apply,
      Matrix.mulVec, dotProduct,Fin.sum_univ_succ] <;> ring

theorem complex_eigen (κ : ℝ) (i : Fin 3) :
    (scaledBlock κ).mulVec (complexVectors i) =
      (normalRoots κ i : ℂ) • complexVectors i := by
  change (scaledBlock κ).mulVec (fun j => (realVectors i j : ℂ)) = _
  rw [scaledBlock_mulVec_ofReal,real_eigen]
  ext j
  simp [complexVectors]

/-- Directly usable as the normal basis input to UpperTriangularEigenbasis. -/
theorem complexBasis_eigen (κ : ℝ) (i : Fin 3) :
    (scaledBlock κ).mulVecLin (complexBasis i) =
      (normalRoots κ i : ℂ) • complexBasis i := by
  simpa only [complexBasis_apply,Matrix.mulVecLin_apply] using complex_eigen κ i

theorem complexBasis_ofReal (i j : Fin 3) :
    complexBasis i j = (realBasis i j : ℂ) := by
  simp [complexVectors]

theorem complexBasis_conj (i j : Fin 3) :
    star (complexBasis i j) = complexBasis i j := by
  rw [complexBasis_ofReal]
  simp

theorem normalRoots_conj (κ : ℝ) (i : Fin 3) :
    star (normalRoots κ i : ℂ) = (normalRoots κ i : ℂ) := by simp

end
end ThreeSitePhosphorylation.NormalEigenbasis
