import proofs.ThreeSitePhosphorylation.GenericReturnBaseModes
import proofs.ThreeSitePhosphorylation.GenericRealCriticalBasis

/-! Full real eigenbasis of the actual zero-amplitude return derivative.
No return-mode formula or desired real basis is assumed. -/
namespace ThreeSitePhosphorylation.GenericReturnBaseEigenbasis
noncomputable section
open scoped Topology
open GenericComplexification GenericReturnIFT GenericReturnBaseModes GenericVariationalODE

variable {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]

def returnValues (T : ℝ) (roots : σ → ℝ) : (σ ⊕ Fin 2) → ℝ :=
  Sum.elim (fun i => Real.exp (T*roots i)) (fun j => ![1,0] j)

omit [Fintype σ] [DecidableEq σ] in
theorem stable_value_bounds (T : ℝ) (hT : 0<T) (roots : σ → ℝ)
    (hn : ∀ i, roots i<0) (i : σ) :
    0<returnValues T roots (Sum.inl i) ∧ returnValues T roots (Sum.inl i)<1 :=
  ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg hT (hn i))⟩

omit [Fintype σ] [DecidableEq σ] in
theorem returnValues_injective (T : ℝ) (hT : 0<T) (roots : σ → ℝ)
    (hi : Function.Injective roots) (hn : ∀ i, roots i<0) :
    Function.Injective (returnValues T roots) := by
  intro i j hij
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have he : T*roots i=T*roots j := Real.exp_injective hij
      exact congrArg Sum.inl (hi (mul_left_cancel₀ (ne_of_gt hT) he))
    | inr j =>
      have hb := stable_value_bounds T hT roots hn i
      fin_cases j
      · exact (hb.2.ne hij).elim
      · exact (hb.1.ne' hij).elim
  | inr i =>
    cases j with
    | inl j =>
      have hb := stable_value_bounds T hT roots hn j
      fin_cases i
      · exact (hb.2.ne hij.symm).elim
      · exact (hb.1.ne' hij.symm).elim
    | inr j =>
      fin_cases i <;> fin_cases j <;>
        first | rfl | norm_num [returnValues] at hij

omit [Fintype σ] [DecidableEq σ] in
theorem nonradial_value_abs_lt_one (T : ℝ) (hT : 0<T) (roots : σ → ℝ)
    (hn : ∀ i, roots i<0) (i : σ ⊕ Fin 2) (hi : i ≠ Sum.inr 0) :
    |returnValues T roots i|<1 := by
  cases i with
  | inl i =>
    have hb := stable_value_bounds T hT roots hn i
    simpa only [abs_of_pos hb.1] using hb.2
  | inr i =>
    fin_cases i
    · exact (hi rfl).elim
    · norm_num [returnValues]

theorem real_eigenvector (A : Matrix ι ι ℝ) (eig : ℝ) (v : ι → ℂ)
    (he : (complexMatrix A).mulVec v=(eig:ℂ) • v) :
    A.mulVec (GenericComplexification.realPart v)=eig • GenericComplexification.realPart v := by
  rw [real_action,he]
  funext i
  simp [GenericComplexification.realPart,Complex.mul_re]

def stateDerivative
    (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (τ : ReturnData (ι → ℝ) → ℝ) (d : ReturnData (ι → ℝ)) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  (fderiv ℝ (returnPoint ψ τ) d).comp
    (ContinuousLinearMap.inr ℝ (ℝ × ℝ) (ι → ℝ))

/-- Assemble the real basis already derived from source conjugation data
with the actual residual-derived stable/radial/phase return actions. -/
theorem actual_return_base_eigenbasis (A0 D : Matrix ι ι ℝ)
    (B : ℝ → ContinuousPath (ι → ℝ) → ContinuousPath (ι → ℝ))
    (r w : ℝ) (hw : 0<w) (roots : σ → ℝ)
    (hinj : Function.Injective roots) (hn : ∀ i, roots i<0)
    (b : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ))
    (hreal : ∀ i : σ, conjugateVector (b (Sum.inl i))=b (Sum.inl i))
    (hpair : b (Sum.inr 1)=conjugateVector (b (Sum.inr 0)))
    (he : ∀ i, (complexMatrix (A0+r • D)).mulVec (b i)=
      GenericPeriodicKernel.spectralValues roots w i • b i)
    (p : (ι → ℂ) →ₗ[ℂ] ℂ)
    (hleft : ∀ z, p ((complexMatrix (A0+r • D)).mulVec z)=(Complex.I*(w:ℂ))*p z)
    (hnorm : p (b (Sum.inr 0))=1)
    (ψ : GenericShootingMap.FlowData (ι → ℝ) → ContinuousPath (ι → ℝ))
    (τ : ReturnData (ι → ℝ) → ℝ)
    (hψ : ContDiffAt ℝ ⊤ ψ ((0,(r,2*Real.pi/w)),GenericComplexification.realPart (b (Sum.inr 0))))
    (hτ : ContDiffAt ℝ ⊤ τ ((0,r),GenericComplexification.realPart (b (Sum.inr 0))))
    (hτ0 : τ ((0,r),GenericComplexification.realPart (b (Sum.inr 0)))=2*Real.pi/w)
    (hres : ∀ᶠ d in 𝓝 ((0,(r,2*Real.pi/w)),GenericComplexification.realPart (b (Sum.inr 0))),
      GenericAffinePathResidual.pathResidual A0.mulVecLin.toContinuousLinearMap
        D.mulVecLin.toContinuousLinearMap B (d,ψ d)=0)
    (hphase : ∀ᶠ d in 𝓝 ((0,r),GenericComplexification.realPart (b (Sum.inr 0))), endpointPhase ψ p (d,τ d)=0) :
    ∃ c : Module.Basis (σ ⊕ Fin 2) ℝ (ι → ℝ),
      (∀ i, c i=GenericRealCriticalBasis.vectors b i) ∧
      (∀ i, stateDerivative ψ τ ((0,r),GenericComplexification.realPart (b (Sum.inr 0))) (c i)=
        returnValues (2*Real.pi/w) roots i • c i) ∧
      Function.Injective (returnValues (2*Real.pi/w) roots) := by
  let v := b (Sum.inr 0)
  have hev : (complexMatrix (A0+r • D)).mulVec v=(Complex.I*(w:ℂ)) • v := by
    simpa only [v,GenericPeriodicKernel.spectralValues] using he (Sum.inr 0)
  let c := GenericRealCriticalBasis.realBasis b hreal hpair
  have hc (i : σ ⊕ Fin 2) : c i=GenericRealCriticalBasis.vectors b i :=
    GenericRealCriticalBasis.realBasis_apply b hreal hpair i
  refine ⟨c,hc,?_,returnValues_injective (2*Real.pi/w) (by positivity) roots hinj hn⟩
  intro i
  rw [hc]
  cases i with
  | inl i =>
    have hs : (A0+r • D).mulVec (GenericComplexification.realPart (b (Sum.inl i)))=
        roots i • GenericComplexification.realPart (b (Sum.inl i)) := by
      apply real_eigenvector
      simpa only [GenericPeriodicKernel.spectralValues] using he (Sum.inl i)
    simpa [stateDerivative,GenericRealCriticalBasis.vectors,returnValues,v] using
      actual_return_stable_mode A0 D B r w hw v p hev hleft hnorm ψ τ hψ hτ hτ0
        hres hphase (roots i) (hn i) (GenericComplexification.realPart (b (Sum.inl i))) hs
  | inr j =>
    fin_cases j
    · simpa [stateDerivative,GenericRealCriticalBasis.vectors,returnValues,v] using
        actual_return_radial_mode A0 D B r w hw v p hev hleft hnorm ψ τ hψ hτ hτ0 hres hphase
    · simpa [stateDerivative,GenericRealCriticalBasis.vectors,returnValues,v] using
        actual_return_phase_mode A0 D B r w hw v p hev hleft hnorm ψ τ hψ hτ hτ0 hres hphase

end
end ThreeSitePhosphorylation.GenericReturnBaseEigenbasis
