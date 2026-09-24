import proofs.ThreeSitePhosphorylation.GenericPeriodicKernel

namespace ThreeSitePhosphorylation.GenericResolvents
noncomputable section
open scoped BigOperators
open GenericPeriodicKernel

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]

theorem eigenbasis_bijective {ι : Type*} [Fintype ι]
    (A : E →ₗ[ℂ] E) (b : Module.Basis ι ℂ E) (eig : ι → ℂ)
    (he : ∀ i, A (b i)=eig i • b i) (hn : ∀ i, eig i ≠ 0) :
    Function.Bijective A := by
  have hs : Function.Surjective A := by
    intro y
    refine ⟨∑ i, (b.repr y i/eig i) • b i,?_⟩
    simp only [map_sum,map_smul,he,smul_smul,div_mul_cancel₀ _ (hn _)]
    exact b.sum_repr y
  exact ⟨LinearMap.injective_iff_surjective.mpr hs,hs⟩

variable {σ : Type*} [Fintype σ]

omit [Fintype σ] in
theorem spectralValues_ne_zero (roots : σ → ℝ) (w : ℝ)
    (hn : ∀ i, roots i<0) (hw : 0<w) (i : σ ⊕ Fin 2) :
    spectralValues roots w i ≠ 0 := by
  intro h
  cases i with
  | inl i =>
    have hh := congrArg Complex.re h
    simp [spectralValues] at hh
    linarith [hn i]
  | inr i =>
    have hh := congrArg Complex.im h
    fin_cases i <;> simp [spectralValues] at hh <;> linarith

omit [Fintype σ] in
theorem spectralValues_second_harmonic_ne (roots : σ → ℝ) (w : ℝ)
    (hn : ∀ i, roots i<0) (hw : 0<w) (i : σ ⊕ Fin 2) :
    2*Complex.I*(w:ℂ)-spectralValues roots w i ≠ 0 := by
  intro h
  cases i with
  | inl i =>
    have hh := congrArg Complex.re h
    simp [spectralValues] at hh
    linarith [hn i]
  | inr i =>
    have hh := congrArg Complex.im h
    fin_cases i <;> simp [spectralValues] at hh <;> linarith

def secondHarmonic (A : E →ₗ[ℂ] E) (w : ℝ) : E →ₗ[ℂ] E :=
  (2*Complex.I*(w:ℂ)) • LinearMap.id-A

theorem resolvents_bijective (A : E →ₗ[ℂ] E) (w : ℝ) (roots : σ → ℝ)
    (b : Module.Basis (σ ⊕ Fin 2) ℂ E) (hn : ∀ i, roots i<0) (hw : 0<w)
    (he : ∀ i, A (b i)=spectralValues roots w i • b i) :
    Function.Bijective A ∧ Function.Bijective (secondHarmonic A w) := by
  constructor
  · exact eigenbasis_bijective A b _ he (spectralValues_ne_zero roots w hn hw)
  · apply eigenbasis_bijective _ b (fun i => 2*Complex.I*(w:ℂ)-spectralValues roots w i)
    · intro i
      simp only [secondHarmonic,LinearMap.sub_apply,LinearMap.smul_apply,
        LinearMap.id_apply,he,sub_smul]
    · exact spectralValues_second_harmonic_ne roots w hn hw

theorem resolvents_unique (A : E →ₗ[ℂ] E) (w : ℝ) (roots : σ → ℝ)
    (b : Module.Basis (σ ⊕ Fin 2) ℂ E) (hn : ∀ i, roots i<0) (hw : 0<w)
    (he : ∀ i, A (b i)=spectralValues roots w i • b i) (u v : E) :
    (∃! h11, A h11=u) ∧ (∃! h20, (2*Complex.I*(w:ℂ)) • h20-A h20=v) := by
  obtain ⟨hA,hH⟩ := resolvents_bijective A w roots b hn hw he
  constructor
  · obtain ⟨h,hh⟩ := hA.2 u
    exact ⟨h,hh,fun y hy => hA.1 (hy.trans hh.symm)⟩
  · obtain ⟨h,hh⟩ := hH.2 v
    exact ⟨h,hh,fun y hy => hH.1 (hy.trans hh.symm)⟩

end
end ThreeSitePhosphorylation.GenericResolvents
