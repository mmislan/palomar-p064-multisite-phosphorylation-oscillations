import proofs.ThreeSitePhosphorylation.RealEigenpairPersistence
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic.LinearCombination

namespace ThreeSitePhosphorylation.RealEigenfunctional
noncomputable section
open RealEigenpairPersistence

variable {ι η : Type*} [DecidableEq η]

theorem coordinate_eigen (A : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (b : Module.Basis η ℂ (ι → ℂ)) (eig : η → ℂ)
    (he : ∀ j, A (b j)=eig j • b j) (i : η) (x : ι → ℂ) :
    b.coord i (A x)=eig i*b.coord i x := by
  have hh : (b.coord i).comp A=eig i • b.coord i := by
    apply b.ext
    intro j
    by_cases hij : i=j
    · subst j
      simp [he,Module.Basis.coord_apply]
    · simp [he,Module.Basis.coord_apply,hij]
  exact DFunLike.congr_fun hh x

omit [DecidableEq η] in
theorem left_other_basis (A : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (b : Module.Basis η ℂ (ι → ℂ)) (eig : η → ℂ)
    (he : ∀ j, A (b j)=eig j • b j) (i : η)
    (hi : ∀ j, j≠i → eig j≠eig i)
    (ell : (ι → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ x, ell (A x)=eig i*ell x)
    (j : η) (hj : j≠i) : ell (b j)=0 := by
  have hh := hl (b j)
  rw [he,map_smul,smul_eq_mul] at hh
  have hz : (eig j-eig i)*ell (b j)=0 := by linear_combination hh
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (hi j hj))

/-- Only the selected eigenvalue must be simple relative to the supplied
basis; the other eigenvalues and eigenvectors need not be real. -/
theorem normalized_left_unique (A : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (b : Module.Basis η ℂ (ι → ℂ)) (eig : η → ℂ)
    (he : ∀ j, A (b j)=eig j • b j) (i : η)
    (hi : ∀ j, j≠i → eig j≠eig i)
    (ell m : (ι → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ x, ell (A x)=eig i*ell x) (hm : ∀ x, m (A x)=eig i*m x)
    (hln : ell (b i)=1) (hmn : m (b i)=1) : ell=m := by
  apply b.ext
  intro j
  by_cases hj : j=i
  · subst j
    rw [hln,hmn]
  · rw [left_other_basis A b eig he i hi ell hl j hj,
      left_other_basis A b eig he i hi m hm j hj]

theorem conjugate_add (x y : ι → ℂ) : conjugate (x+y)=conjugate x+conjugate y := by
  ext i
  simp [conjugate]

def conjugatedFunctional (ell : (ι → ℂ) →ₗ[ℂ] ℂ) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun x := star (ell (conjugate x))
  map_add' x y := by rw [conjugate_add,map_add,star_add]
  map_smul' c x := by
    rw [conjugate_smul,map_smul]
    simp [smul_eq_mul,star_mul,mul_comm]

theorem conjugatedFunctional_eigen (A : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (ell : (ι → ℂ) →ₗ[ℂ] ℂ) (z : ℂ)
    (hA : ∀ x, A (conjugate x)=conjugate (A x)) (hz : star z=z)
    (hl : ∀ x, ell (A x)=z*ell x) (x : ι → ℂ) :
    conjugatedFunctional ell (A x)=z*conjugatedFunctional ell x := by
  change star (ell (conjugate (A x)))=z*star (ell (conjugate x))
  rw [← hA,hl]
  simp [star_mul,hz,mul_comm]

/-- The normalized coordinate of a real simple eigenvector respects
conjugation, even when other basis vectors form a nonreal critical pair. -/
theorem coordinate_conjugation (A : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (b : Module.Basis η ℂ (ι → ℂ)) (eig : η → ℂ)
    (he : ∀ j, A (b j)=eig j • b j) (i : η)
    (hi : ∀ j, j≠i → eig j≠eig i)
    (hA : ∀ x, A (conjugate x)=conjugate (A x))
    (hei : star (eig i)=eig i) (hbi : conjugate (b i)=b i) :
    ∀ x, b.coord i (conjugate x)=star (b.coord i x) := by
  have hn : b.coord i (b i)=1 := by simp [Module.Basis.coord_apply]
  have hcn : conjugatedFunctional (b.coord i) (b i)=1 := by
    change star (b.coord i (conjugate (b i)))=1
    rw [hbi,hn,star_one]
  have huniq := normalized_left_unique A b eig he i hi
    (conjugatedFunctional (b.coord i)) (b.coord i)
    (conjugatedFunctional_eigen A (b.coord i) (eig i) hA hei
      (coordinate_eigen A b eig he i)) (coordinate_eigen A b eig he i) hcn hn
  intro x
  have hh := congrArg (fun ell : (ι → ℂ) →ₗ[ℂ] ℂ => star (ell x)) huniq
  change star (star (b.coord i (conjugate x)))=star (b.coord i x) at hh
  simpa only [star_star] using hh

theorem conjugate_conjugate (x : ι → ℂ) : conjugate (conjugate x)=x := by
  ext i
  simp [conjugate]

theorem conjugatedFunctional_eigen_star (A : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (ell : (ι → ℂ) →ₗ[ℂ] ℂ) (z : ℂ)
    (hA : ∀ x, A (conjugate x)=conjugate (A x))
    (hl : ∀ x, ell (A x)=z*ell x) (x : ι → ℂ) :
    conjugatedFunctional ell (A x)=star z*conjugatedFunctional ell x := by
  change star (ell (conjugate (A x)))=star z*star (ell (conjugate x))
  rw [← hA,hl,star_mul,mul_comm]

/-- Conjugation exchanges the normalized coordinates of a conjugate pair of
simple eigenvectors. Only the target eigenvalue must be simple. -/
theorem coordinate_pair_conjugation (A : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))
    (b : Module.Basis η ℂ (ι → ℂ)) (eig : η → ℂ)
    (he : ∀ j, A (b j)=eig j • b j) (i i' : η)
    (hi' : ∀ j, j≠i' → eig j≠eig i')
    (hA : ∀ x, A (conjugate x)=conjugate (A x))
    (hei : star (eig i)=eig i') (hbi : conjugate (b i)=b i') :
    ∀ x, b.coord i' (conjugate x)=star (b.coord i x) := by
  have hn : b.coord i' (b i')=1 := by simp [Module.Basis.coord_apply]
  have hcn : conjugatedFunctional (b.coord i) (b i')=1 := by
    change star (b.coord i (conjugate (b i')))=1
    rw [← hbi,conjugate_conjugate]
    simp [Module.Basis.coord_apply]
  have hl : ∀ x, conjugatedFunctional (b.coord i) (A x)=
      eig i'*conjugatedFunctional (b.coord i) x := by
    intro x
    rw [conjugatedFunctional_eigen_star A (b.coord i) (eig i) hA
      (coordinate_eigen A b eig he i) x,hei]
  have huniq := normalized_left_unique A b eig he i' hi'
    (conjugatedFunctional (b.coord i)) (b.coord i') hl
    (coordinate_eigen A b eig he i') hcn hn
  intro x
  have hh := congrArg (fun ell : (ι → ℂ) →ₗ[ℂ] ℂ => ell (conjugate x)) huniq
  change star (b.coord i (conjugate (conjugate x)))=b.coord i' (conjugate x) at hh
  rw [conjugate_conjugate] at hh
  exact hh.symm

end
end ThreeSitePhosphorylation.RealEigenfunctional