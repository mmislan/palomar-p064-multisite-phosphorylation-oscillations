import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-! Literal complexification of an arbitrary finite real matrix.
These lemmas do not supply a spectral hypothesis or a Hopf theorem. -/
namespace ThreeSitePhosphorylation.GenericComplexification
noncomputable section
variable {ι : Type*} [Fintype ι]

def realPart (v : ι → ℂ) : ι → ℝ := fun i => (v i).re
def imagPart (v : ι → ℂ) : ι → ℝ := fun i => (v i).im
def conjugateVector (v : ι → ℂ) : ι → ℂ := fun i => star (v i)
def complexMatrix (A : Matrix ι ι ℝ) : Matrix ι ι ℂ := fun i j => (A i j : ℂ)
def complexify : (ι → ℝ) →L[ℝ] (ι → ℂ) :=
  ContinuousLinearMap.pi (fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))

omit [Fintype ι] in
@[simp] theorem complexify_apply (y : ι → ℝ) (i : ι) :
    complexify y i=(y i:ℂ) := rfl

theorem complexify_action (A : Matrix ι ι ℝ) (y : ι → ℝ) :
    complexify (A.mulVec y)=(complexMatrix A).mulVec (complexify y) := by
  ext i
  simp [complexMatrix,Matrix.mulVec,dotProduct]

theorem real_action (A : Matrix ι ι ℝ) (v : ι → ℂ) :
    A.mulVec (realPart v)=realPart ((complexMatrix A).mulVec v) := by
  ext i
  simp [realPart,complexMatrix,Matrix.mulVec,dotProduct,Complex.mul_re]

theorem imag_action (A : Matrix ι ι ℝ) (v : ι → ℂ) :
    A.mulVec (imagPart v)=imagPart ((complexMatrix A).mulVec v) := by
  ext i
  simp [imagPart,complexMatrix,Matrix.mulVec,dotProduct,Complex.mul_im]

theorem conjugate_action (A : Matrix ι ι ℝ) (v : ι → ℂ) :
    (complexMatrix A).mulVec (conjugateVector v)=
      conjugateVector ((complexMatrix A).mulVec v) := by
  ext i
  simp [conjugateVector,complexMatrix,Matrix.mulVec,dotProduct]

theorem source_eigen_real_imag (A : Matrix ι ι ℝ) (w : ℝ) (v : ι → ℂ)
    (he : (complexMatrix A).mulVec v=(Complex.I*(w:ℂ)) • v) :
    A.mulVec (realPart v)=(-w) • imagPart v ∧
      A.mulVec (imagPart v)=w • realPart v := by
  rw [real_action,imag_action,he]
  constructor <;> ext i <;>
    simp [realPart,imagPart,Complex.mul_re,Complex.mul_im]

theorem conjugate_eigen (A : Matrix ι ι ℝ) (w : ℝ) (v : ι → ℂ)
    (he : (complexMatrix A).mulVec v=(Complex.I*(w:ℂ)) • v) :
    (complexMatrix A).mulVec (conjugateVector v)=
      (-Complex.I*(w:ℂ)) • conjugateVector v := by
  rw [conjugate_action,he]
  ext i
  simp [conjugateVector]

theorem real_vector_imaginary_eigen_zero (A : Matrix ι ι ℝ) (w : ℝ)
    (hw : w ≠ 0) (v : ι → ℂ) (hv : imagPart v=0)
    (he : (complexMatrix A).mulVec v=(Complex.I*(w:ℂ)) • v) : v=0 := by
  have hh := (source_eigen_real_imag A w v he).2
  rw [hv,Matrix.mulVec_zero] at hh
  have hr : realPart v=0 := (smul_eq_zero.mp hh.symm).resolve_left hw
  ext i
  exact Complex.ext (congrFun hr i) (congrFun hv i)

theorem eigen_real_nonzero (A : Matrix ι ι ℝ) (w : ℝ) (hw : w ≠ 0)
    (v : ι → ℂ) (hv : v ≠ 0)
    (he : (complexMatrix A).mulVec v=(Complex.I*(w:ℂ)) • v) : realPart v ≠ 0 := by
  intro hr
  have hi := (source_eigen_real_imag A w v he).1
  rw [hr,Matrix.mulVec_zero] at hi
  have hb : imagPart v=0 := (smul_eq_zero.mp hi.symm).resolve_left (neg_ne_zero.mpr hw)
  apply hv
  ext i
  exact Complex.ext (congrFun hr i) (congrFun hb i)

omit [Fintype ι] in
theorem complexify_orbit (v : ι → ℂ) (θ : ℝ) :
    complexify (Real.cos θ • realPart v-Real.sin θ • imagPart v)=
      (Complex.exp ((θ:ℂ)*Complex.I)/2) • v+
      (Complex.exp (-(θ:ℂ)*Complex.I)/2) • conjugateVector v := by
  rw [Complex.exp_ofReal_mul_I,← Complex.ofReal_neg,Complex.exp_ofReal_mul_I]
  ext i
  apply Complex.ext <;>
    simp [complexify,realPart,imagPart,conjugateVector,Complex.mul_re,Complex.mul_im] <;> ring

end
end ThreeSitePhosphorylation.GenericComplexification
