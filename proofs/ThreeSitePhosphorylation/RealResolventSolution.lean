import proofs.ThreeSitePhosphorylation.GenericComplexification

namespace ThreeSitePhosphorylation.RealResolventSolution
noncomputable section
open GenericComplexification
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- A real resolvent equation has a real solution whenever the shifted
operator is injective. The spectral proof of injectivity is separate. -/
theorem real_solution (A : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) (eig : ℂ)
    (f u : ι → ℂ)
    (hA : ∀ x, A (conjugateVector x)=conjugateVector (A x))
    (heig : star eig=eig) (hf : conjugateVector f=f)
    (hinj : Function.Injective (fun x => eig • x-A x))
    (hu : eig • u-A u=f) : conjugateVector u=u := by
  have hc : eig • conjugateVector u-A (conjugateVector u)=f := by
    calc
      eig • conjugateVector u-A (conjugateVector u) =
          conjugateVector (eig • u-A u) := by
        rw [hA]
        ext i
        simp [conjugateVector,heig]
      _ = f := by rw [hu,hf]
  exact hinj (hc.trans hu.symm)

omit [Fintype ι] [DecidableEq ι] in
/-- In the triangular source block, conjugation and uniqueness force the
upper part of a stable eigenvector to be real when its normal part is real.
No zero-coupling hypothesis is used. -/
theorem real_upper_column {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) (U : (κ → ℂ) →ₗ[ℂ] (ι → ℂ))
    (eig : ℂ) (u : ι → ℂ) (c : κ → ℂ)
    (hA : ∀ x, A (conjugateVector x)=conjugateVector (A x))
    (hU : ∀ z, U (conjugateVector z)=conjugateVector (U z))
    (heig : star eig=eig) (hc : conjugateVector c=c)
    (hinj : Function.Injective (fun x => eig • x-A x))
    (hu : A u+U c=eig • u) : conjugateVector u=u := by
  have hf : conjugateVector (U c)=U c := by rw [← hU,hc]
  have hres : eig • u-A u=U c := by rw [← hu]; abel
  exact real_solution A eig (U c) u hA heig hf hinj hres

end
end ThreeSitePhosphorylation.RealResolventSolution
