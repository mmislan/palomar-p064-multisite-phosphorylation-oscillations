import proofs.ThreeSitePhosphorylation.GenericComplexification
import Mathlib

/-! A real basis from real stable columns and one conjugate critical pair.
No operator, return map, eigenvalue separation or real basis is assumed. -/
namespace ThreeSitePhosphorylation.GenericRealCriticalBasis
noncomputable section
open GenericComplexification
open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]

def vectors (b : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ)) : (σ ⊕ Fin 2) → (ι → ℝ) :=
  Sum.elim (fun i => GenericComplexification.realPart (b (Sum.inl i)))
    (fun j => ![GenericComplexification.realPart (b (Sum.inr 0)),imagPart (b (Sum.inr 0))] j)

def complexCoordinate (b : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ)) (i : σ ⊕ Fin 2) :
    (ι → ℝ) →L[ℝ] ℂ :=
  ((b.coord i).toContinuousLinearMap.restrictScalars ℝ).comp complexify

def realCoordinate (b : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ)) :
    (σ ⊕ Fin 2) → ((ι → ℝ) →L[ℝ] ℝ) :=
  Sum.elim (fun i => Complex.reCLM.comp (complexCoordinate b (Sum.inl i)))
    (fun j => ![(2:ℝ) • Complex.reCLM.comp (complexCoordinate b (Sum.inr 0)),
      (-2:ℝ) • Complex.imCLM.comp (complexCoordinate b (Sum.inr 0))] j)

omit [Fintype ι] in
theorem complexify_realPart (v : ι → ℂ) :
    complexify (GenericComplexification.realPart v)=(1/2:ℂ) • v+(1/2:ℂ) • conjugateVector v := by
  funext i
  apply Complex.ext <;>
    simp [complexify_apply,GenericComplexification.realPart,conjugateVector,Complex.mul_re,Complex.mul_im]; ring

omit [Fintype ι] in
theorem complexify_imagPart (v : ι → ℂ) :
    complexify (imagPart v)=(-Complex.I/2) • v+(Complex.I/2) • conjugateVector v := by
  funext i
  apply Complex.ext <;>
    simp [complexify_apply,imagPart,conjugateVector,Complex.mul_re,Complex.mul_im] <;> ring

omit [Fintype ι] in
theorem complexify_realPart_of_fixed (v : ι → ℂ) (hv : conjugateVector v=v) :
    complexify (GenericComplexification.realPart v)=v := by
  rw [complexify_realPart,hv,← add_smul]
  norm_num

omit [Fintype σ] in
/-- These actual real linear functionals form the dual coordinate system.
The phase coordinate has sign -2 Im because x=2 Re(c) Re(v)-2 Im(c) Im(v). -/
theorem coordinate_vectors (b : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ))
    (hreal : ∀ i : σ, conjugateVector (b (Sum.inl i))=b (Sum.inl i))
    (hpair : b (Sum.inr 1)=conjugateVector (b (Sum.inr 0)))
    (i j : σ ⊕ Fin 2) : realCoordinate b i (vectors b j)=if i=j then 1 else 0 := by
  have hs (j : σ) : complexify (GenericComplexification.realPart (b (Sum.inl j)))=b (Sum.inl j) :=
    complexify_realPart_of_fixed _ (hreal j)
  have hr := complexify_realPart (b (Sum.inr 0))
  have hi := complexify_imagPart (b (Sum.inr 0))
  rw [← hpair] at hr hi
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      by_cases hij : i=j
      · subst j
        simp [realCoordinate,vectors,complexCoordinate,hs,Module.Basis.coord_apply]
      · simp [realCoordinate,vectors,complexCoordinate,hs,Module.Basis.coord_apply,hij]
    | inr j =>
      fin_cases j <;>
        norm_num [realCoordinate,vectors,complexCoordinate,hr,hi,Module.Basis.coord_apply,Finsupp.single_apply] <;>
        simp
  | inr i =>
    cases j with
    | inl j =>
      fin_cases i <;>
        simp [realCoordinate,vectors,complexCoordinate,hs,Module.Basis.coord_apply]
    | inr j =>
      fin_cases i <;> fin_cases j <;>
        norm_num [realCoordinate,vectors,complexCoordinate,hr,hi,Module.Basis.coord_apply,Finsupp.single_apply]

theorem vectors_independent (b : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ))
    (hreal : ∀ i : σ, conjugateVector (b (Sum.inl i))=b (Sum.inl i))
    (hpair : b (Sum.inr 1)=conjugateVector (b (Sum.inr 0))) :
    LinearIndependent ℝ (vectors b) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have hh := congrArg (realCoordinate b i) ha
  simp only [map_sum,map_smul,map_zero,coordinate_vectors b hreal hpair,
    smul_eq_mul,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true] at hh
  exact hh

omit [DecidableEq σ] in
theorem index_card (b : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ)) :
    Fintype.card (σ ⊕ Fin 2)=Module.finrank ℝ (ι → ℝ) := by
  have hh := Module.finrank_eq_card_basis b
  simpa only [Module.finrank_fintype_fun_eq_card] using hh.symm

/-- Completeness comes from the supplied full complex basis, not from a
new spectral or spanning hypothesis on the real vectors. -/
def realBasis (b : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ))
    (hreal : ∀ i : σ, conjugateVector (b (Sum.inl i))=b (Sum.inl i))
    (hpair : b (Sum.inr 1)=conjugateVector (b (Sum.inr 0))) :
    Module.Basis (σ ⊕ Fin 2) ℝ (ι → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank (vectors_independent b hreal hpair) (index_card b)

@[simp] theorem realBasis_apply (b : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ))
    (hreal : ∀ i : σ, conjugateVector (b (Sum.inl i))=b (Sum.inl i))
    (hpair : b (Sum.inr 1)=conjugateVector (b (Sum.inr 0))) (i : σ ⊕ Fin 2) :
    realBasis b hreal hpair i=vectors b i := by
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank
    (vectors_independent b hreal hpair) (index_card b)) i

theorem realBasis_coordinate (b : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ))
    (hreal : ∀ i : σ, conjugateVector (b (Sum.inl i))=b (Sum.inl i))
    (hpair : b (Sum.inr 1)=conjugateVector (b (Sum.inr 0))) (i : σ ⊕ Fin 2) :
    ((realBasis b hreal hpair).coord i).toContinuousLinearMap=realCoordinate b i := by
  apply ContinuousLinearMap.coe_injective
  apply (realBasis b hreal hpair).ext
  intro j
  change (realBasis b hreal hpair).coord i (realBasis b hreal hpair j)=
    realCoordinate b i (realBasis b hreal hpair j)
  rw [Module.Basis.coord_apply,Module.Basis.repr_self_apply,
    realBasis_apply,coordinate_vectors b hreal hpair]
  simp [eq_comm]

end
end ThreeSitePhosphorylation.GenericRealCriticalBasis
