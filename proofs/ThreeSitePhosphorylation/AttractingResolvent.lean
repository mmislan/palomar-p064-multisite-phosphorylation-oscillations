import proofs.ThreeSitePhosphorylation.AttractingEigenbasis

namespace ThreeSitePhosphorylation.AttractingWitness

noncomputable section
open scoped BigOperators

/-- A finite eigenbasis with no zero eigenvalue gives unique solvability. -/
theorem eigenbasis_bijective {ι : Type*} [Fintype ι]
    (f : (Fin 9 → ℂ) →ₗ[ℂ] (Fin 9 → ℂ))
    (b : Module.Basis ι ℂ (Fin 9 → ℂ)) (eig : ι → ℂ)
    (he : ∀ i, f (b i) = eig i • b i) (hn : ∀ i, eig i ≠ 0) :
    Function.Bijective f := by
  have hs : Function.Surjective f := by
    intro y
    refine ⟨∑ i, (b.repr y i / eig i) • b i, ?_⟩
    simp only [map_sum, map_smul, he, smul_smul, div_mul_cancel₀ _ (hn _)]
    exact b.sum_repr y
  exact ⟨LinearMap.injective_iff_surjective.mpr hs, hs⟩

theorem spectralValues_ne_zero (x : Fin 7 → ℝ) (w : ℝ)
    (hx : ∀ i, x i < 0) (hw : 0 < w) (i : SpectralIndex) :
    spectralValues x w i ≠ 0 := by
  intro h
  cases i with
  | inl i =>
    have hh := congrArg Complex.re h
    simp [spectralValues] at hh
    linarith [hx i]
  | inr i =>
    have hh := congrArg Complex.im h
    fin_cases i <;> simp [spectralValues] at hh <;> linarith

theorem spectralValues_second_harmonic_ne (x : Fin 7 → ℝ) (w : ℝ)
    (hx : ∀ i, x i < 0) (hw : 0 < w) (i : SpectralIndex) :
    2 * Complex.I * (w : ℂ) - spectralValues x w i ≠ 0 := by
  intro h
  cases i with
  | inl i =>
    have hh := congrArg Complex.re h
    simp [spectralValues] at hh
    linarith [hx i]
  | inr i =>
    have hh := congrArg Complex.im h
    fin_cases i <;> simp [spectralValues] at hh <;> linarith

def secondHarmonic (r w : ℝ) : (Fin 9 → ℂ) →ₗ[ℂ] (Fin 9 → ℂ) :=
  (2 * Complex.I * (w : ℂ)) • LinearMap.id - (complexSource r).mulVecLin

theorem source_resolvents_bijective (r w : ℝ) (x : Fin 7 → ℝ)
    (b : Module.Basis SpectralIndex ℂ (Fin 9 → ℂ))
    (hx : ∀ i, x i < 0) (hw : 0 < w)
    (he : ∀ i, (complexSource r).mulVec (b i) = spectralValues x w i • b i) :
    Function.Bijective (complexSource r).mulVecLin ∧
      Function.Bijective (secondHarmonic r w) := by
  constructor
  · exact eigenbasis_bijective _ b _ he (spectralValues_ne_zero x w hx hw)
  · apply eigenbasis_bijective _ b
      (fun i => 2 * Complex.I * (w : ℂ) - spectralValues x w i)
    · intro i
      simp only [secondHarmonic, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, Matrix.mulVecLin_apply, he, sub_smul]
    · exact spectralValues_second_harmonic_ne x w hx hw

/-- Both resolvents needed in the quadratic Hopf coefficient are uniquely solvable
at the same source parameter and frequency. -/
theorem source_resolvents_unique (r w : ℝ) (x : Fin 7 → ℝ)
    (b : Module.Basis SpectralIndex ℂ (Fin 9 → ℂ))
    (hx : ∀ i, x i < 0) (hw : 0 < w)
    (he : ∀ i, (complexSource r).mulVec (b i) = spectralValues x w i • b i)
    (u v : Fin 9 → ℂ) :
    (∃! h11, (complexSource r).mulVec h11 = u) ∧
      (∃! h20, (2 * Complex.I * (w : ℂ)) • h20 - (complexSource r).mulVec h20 = v) := by
  obtain ⟨hJ, hH⟩ := source_resolvents_bijective r w x b hx hw he
  constructor
  · obtain ⟨h, hh⟩ := hJ.2 u
    exact ⟨h, hh, fun y hy => hJ.1 (hy.trans hh.symm)⟩
  · obtain ⟨h, hh⟩ := hH.2 v
    refine ⟨h, hh, ?_⟩
    intro y hy
    exact hH.1 (hy.trans hh.symm)

/-- The dual coordinate of an eigenbasis is a left eigenfunctional. -/
theorem eigenbasis_coordinate {ι : Type*}
    (f : (Fin 9 → ℂ) →ₗ[ℂ] (Fin 9 → ℂ))
    (b : Module.Basis ι ℂ (Fin 9 → ℂ)) (eig : ι → ℂ)
    (he : ∀ i, f (b i) = eig i • b i) (i : ι) (v : Fin 9 → ℂ) :
    b.coord i (f v) = eig i * b.coord i v := by
  classical
  have hh : (b.coord i).comp f = eig i • b.coord i := by
    apply b.ext
    intro j
    by_cases hij : i = j
    · subst j
      simp [he, Module.Basis.coord_apply]
    · simp [he, Module.Basis.coord_apply, hij]
  exact DFunLike.congr_fun hh v

/-- The positive-frequency dual coordinate is already normalized on its eigenvector. -/
theorem source_left_eigenfunctional (r w : ℝ) (x : Fin 7 → ℝ)
    (b : Module.Basis SpectralIndex ℂ (Fin 9 → ℂ))
    (he : ∀ i, (complexSource r).mulVec (b i) = spectralValues x w i • b i) :
    b.coord (Sum.inr 0) (b (Sum.inr 0)) = 1 ∧
      ∀ v, b.coord (Sum.inr 0) ((complexSource r).mulVec v) =
        (Complex.I * (w : ℂ)) * b.coord (Sum.inr 0) v := by
  constructor
  · simp [Module.Basis.coord_apply]
  · intro v
    simpa [spectralValues] using
      eigenbasis_coordinate (complexSource r).mulVecLin b (spectralValues x w) he
        (Sum.inr 0) v

end
end ThreeSitePhosphorylation.AttractingWitness



