import proofs.ThreeSitePhosphorylation.GenericComplexification
import Mathlib

/-! Spectral part of the strengthened site-addition invariant for an actual
real source matrix: a full complex eigenbasis whose stable columns are real
with distinct negative real eigenvalues, plus one conjugate critical pair
`±i*freq`. The normalized left functional is the basis coordinate. -/
namespace ThreeSitePhosphorylation.CriticalSpectrum
noncomputable section
open GenericComplexification

/-- Full complex spectral data of a real matrix at a critical parameter. -/
structure Data {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Type*)
    (A : Matrix ι ι ℝ) where
  basis : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ)
  stable : σ → ℝ
  freq : ℝ
  freq_pos : 0 < freq
  stable_neg : ∀ s, stable s < 0
  stable_injective : Function.Injective stable
  stable_eigen : ∀ s, (complexMatrix A).mulVec (basis (Sum.inl s)) =
    (stable s : ℂ) • basis (Sum.inl s)
  critical_eigen : (complexMatrix A).mulVec (basis (Sum.inr 0)) =
    (Complex.I*(freq:ℂ)) • basis (Sum.inr 0)
  stable_real : ∀ s, conjugateVector (basis (Sum.inl s)) = basis (Sum.inl s)
  critical_pair : basis (Sum.inr 1) = conjugateVector (basis (Sum.inr 0))

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}

/-- The complete eigenvalue list, including the conjugate critical value. -/
def eigenvalues (d : Data σ A) : σ ⊕ Fin 2 → ℂ :=
  Sum.elim (fun s => (d.stable s : ℂ)) ![Complex.I*(d.freq:ℂ),-Complex.I*(d.freq:ℂ)]

@[simp] theorem eigenvalues_inl (d : Data σ A) (s : σ) :
    eigenvalues d (Sum.inl s) = (d.stable s : ℂ) := rfl

@[simp] theorem eigenvalues_inr_zero (d : Data σ A) :
    eigenvalues d (Sum.inr 0) = Complex.I*(d.freq:ℂ) := rfl

@[simp] theorem eigenvalues_inr_one (d : Data σ A) :
    eigenvalues d (Sum.inr 1) = -Complex.I*(d.freq:ℂ) := rfl

theorem eigen (d : Data σ A) (i : σ ⊕ Fin 2) :
    (complexMatrix A).mulVec (d.basis i) = eigenvalues d i • d.basis i := by
  rcases i with s | j
  · exact d.stable_eigen s
  · fin_cases j
    · exact d.critical_eigen
    · have h1 : (complexMatrix A).mulVec (d.basis (Sum.inr 1)) =
          eigenvalues d (Sum.inr 1) • d.basis (Sum.inr 1) := by
        rw [eigenvalues_inr_one,d.critical_pair]
        exact conjugate_eigen A d.freq _ d.critical_eigen
      exact h1

theorem eigen_lin (d : Data σ A) (i : σ ⊕ Fin 2) :
    (complexMatrix A).mulVecLin (d.basis i) = eigenvalues d i • d.basis i := by
  rw [Matrix.mulVecLin_apply]
  exact eigen d i

theorem eigenvalues_injective (d : Data σ A) : Function.Injective (eigenvalues d) := by
  have hw := d.freq_pos
  intro i j hij
  rcases i with s | a <;> rcases j with t | b
  · exact congrArg Sum.inl (d.stable_injective (by simpa using hij))
  · exfalso
    have him := congrArg Complex.im hij
    fin_cases b <;> simp at him <;> linarith
  · exfalso
    have him := congrArg Complex.im hij
    fin_cases a <;> simp at him <;> linarith
  · have him := congrArg Complex.im hij
    fin_cases a <;> fin_cases b
    · rfl
    · simp at him; linarith
    · simp at him; linarith
    · rfl

theorem stable_real_eigenvalue (d : Data σ A) (s : σ) :
    star (eigenvalues d (Sum.inl s)) = eigenvalues d (Sum.inl s) := by simp

theorem critical_conj_eigenvalue (d : Data σ A) :
    star (eigenvalues d (Sum.inr 0)) = eigenvalues d (Sum.inr 1) := by
  simp

/-- The actual kinetic crossing pairing of a parameter derivative `A1`. -/
def crossing (d : Data σ A) (A1 : Matrix ι ι ℝ) : ℂ :=
  d.basis.coord (Sum.inr 0) ((complexMatrix A1).mulVec (d.basis (Sum.inr 0)))

end
end ThreeSitePhosphorylation.CriticalSpectrum
