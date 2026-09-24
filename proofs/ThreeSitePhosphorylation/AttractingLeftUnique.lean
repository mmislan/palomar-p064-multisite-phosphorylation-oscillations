import proofs.ThreeSitePhosphorylation.AttractingLyapunovLeft
import proofs.ThreeSitePhosphorylation.AttractingClosedPaths

namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section

theorem spectralValues_other_critical (roots : Fin 7 → ℝ) (w : ℝ) (hw : 0<w)
    (i : SpectralIndex) (hi : i ≠ Sum.inr 0) :
    spectralValues roots w i ≠ Complex.I*(w:ℂ) := by
  intro h
  have hh := congrArg Complex.im h
  cases i with
  | inl i => simp [spectralValues] at hh; linarith
  | inr i =>
    fin_cases i
    · exact hi rfl
    · simp [spectralValues] at hh; linarith

theorem source_left_other_basis (r w : ℝ) (roots : Fin 7 → ℝ) (hw : 0<w)
    (b : Module.Basis SpectralIndex ℂ (Fin 9 → ℂ))
    (he : ∀ i, (complexSource r).mulVec (b i)=spectralValues roots w i • b i)
    (p : (Fin 9 → ℂ) →ₗ[ℂ] ℂ)
    (hp : ∀ v, p ((complexSource r).mulVec v)=(Complex.I*(w:ℂ))*p v)
    (i : SpectralIndex) (hi : i ≠ Sum.inr 0) : p (b i)=0 := by
  have hh := hp (b i)
  rw [he,map_smul,smul_eq_mul] at hh
  have hz : (spectralValues roots w i-Complex.I*(w:ℂ))*p (b i)=0 := by
    linear_combination hh
  exact (mul_eq_zero.mp hz).resolve_left
    (sub_ne_zero.mpr (spectralValues_other_critical roots w hw i hi))

/-- The normalized critical left functional is unique at this same supplied
source eigenbasis; no separate spectral witness is selected. -/
theorem normalized_source_left_unique (r w : ℝ) (hw : 0<w)
    (roots : Fin 7 → ℝ) (b : Module.Basis SpectralIndex ℂ (Fin 9 → ℂ))
    (hb : ∀ i, b i=adjugateVector (spectralValues roots w i))
    (he : ∀ i, (complexSource r).mulVec (b i)=spectralValues roots w i • b i)
    (p q : (Fin 9 → ℂ) →ₗ[ℂ] ℂ)
    (hp : ∀ v, p ((complexSource r).mulVec v)=(Complex.I*(w:ℂ))*p v)
    (hq : ∀ v, q ((complexSource r).mulVec v)=(Complex.I*(w:ℂ))*q v)
    (hpn : p (adjugateVector (Complex.I*(w:ℂ)))=1)
    (hqn : q (adjugateVector (Complex.I*(w:ℂ)))=1) : p=q := by
  apply b.ext
  intro i
  by_cases hi : i=Sum.inr 0
  · subst i
    rw [hb]
    change p (adjugateVector (Complex.I*(w:ℂ)))=q (adjugateVector (Complex.I*(w:ℂ)))
    rw [hpn,hqn]
  · rw [source_left_other_basis r w roots hw b he p hp i hi,
      source_left_other_basis r w roots hw b he q hq i hi]

theorem normalized_left_eq_lyapunovLeft (r w : ℝ) (hw : 0<w)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0)
    (roots : Fin 7 → ℝ) (b : Module.Basis SpectralIndex ℂ (Fin 9 → ℂ))
    (hb : ∀ i, b i=adjugateVector (spectralValues roots w i))
    (he : ∀ i, (complexSource r).mulVec (b i)=spectralValues roots w i • b i)
    (p : (Fin 9 → ℂ) →ₗ[ℂ] ℂ)
    (hleft : ∀ v, p ((complexSource r).mulVec v)=(Complex.I*(w:ℂ))*p v)
    (hnorm : p (adjugateVector (Complex.I*(w:ℂ)))=1) :
    p=lyapunovLeft (Complex.I*(w:ℂ)) := by
  have hc := critical_normalized_left r w (ne_of_gt hw) hp
  exact normalized_source_left_unique r w hw roots b hb he p _ hleft hc.2 hnorm hc.1

theorem ClosedPathFamily.left_eq_lyapunovLeft (r w : ℝ) (hw : 0<w)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0)
    (roots : Fin 7 → ℝ) (b : Module.Basis SpectralIndex ℂ (Fin 9 → ℂ))
    (hb : ∀ i, b i=adjugateVector (spectralValues roots w i))
    (he : ∀ i, (complexSource r).mulVec (b i)=spectralValues roots w i • b i)
    (C : ClosedPathFamily r w) : C.left=lyapunovLeft (Complex.I*(w:ℂ)) :=
  normalized_left_eq_lyapunovLeft r w hw hp roots b hb he C.left C.left_eigen C.left_normalized

end
end ThreeSitePhosphorylation.AttractingWitness
