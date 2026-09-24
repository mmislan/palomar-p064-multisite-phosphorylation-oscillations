import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Tactic.FunProp

namespace ThreeSitePhosphorylation.RealEigenpairPersistence
noncomputable section
open scoped Topology

variable {P ι : Type*} [TopologicalSpace P] [Zero P] [Fintype ι]

def conjugate (v : ι → ℂ) : ι → ℂ := fun i => star (v i)

omit [Fintype ι] in
theorem conjugate_continuous : Continuous (conjugate : (ι → ℂ) → (ι → ℂ)) := by
  apply continuous_pi
  intro i
  exact Complex.continuous_conj.comp (continuous_apply i)

omit [Fintype ι] in
theorem conjugate_smul (z : ℂ) (v : ι → ℂ) :
    conjugate (z • v)=star z • conjugate v := by
  ext i
  simp [conjugate,star_mul,mul_comm]

omit [Fintype ι] in
/-- Conjugating a normalized eigenpair gives another nearby normalized
eigenpair. Local uniqueness therefore forces a branch based at real data to
stay real. No reality hypothesis on the nearby selected branch is assumed. -/
theorem eventually_real
    (A : P → (ι → ℂ) →L[ℂ] (ι → ℂ)) (ell : (ι → ℂ) →ₗ[ℂ] ℂ)
    (μ : P → ℂ) (v : P → ι → ℂ)
    (hμ : ContinuousAt μ 0) (hv : ContinuousAt v 0)
    (hμ0 : star (μ 0)=μ 0) (hv0 : conjugate (v 0)=v 0)
    (hA : ∀ᶠ p in 𝓝 (0:P), ∀ u, A p (conjugate u)=conjugate (A p u))
    (hell : ∀ u, ell (conjugate u)=star (ell u))
    (he : ∀ᶠ p in 𝓝 (0:P), A p (v p)=μ p • v p ∧ ell (v p)=1)
    (hunique : ∀ᶠ d in 𝓝 ((0:P),(v 0,μ 0)),
      (A d.1 d.2.1=d.2.2 • d.2.1 ∧ ell d.2.1=1) ↔
        (v d.1,μ d.1)=d.2) :
    ∀ᶠ p in 𝓝 (0:P), star (μ p)=μ p ∧ conjugate (v p)=v p := by
  let d : P → P × ((ι → ℂ) × ℂ) := fun p => (p,(conjugate (v p),star (μ p)))
  have hd : ContinuousAt d 0 :=
    continuousAt_id.prodMk
      ((conjugate_continuous.continuousAt.comp hv).prodMk
        (Complex.continuous_conj.continuousAt.comp hμ))
  have hd0 : d 0=((0:P),(v 0,μ 0)) := by simp only [d,hv0,hμ0]
  have ht : Filter.Tendsto d (𝓝 (0:P)) (𝓝 ((0:P),(v 0,μ 0))) := by
    simpa only [hd0] using hd.tendsto
  filter_upwards [hA,he,ht.eventually hunique] with p hAp hep hup
  have hce : A p (conjugate (v p))=star (μ p) • conjugate (v p) := by
    rw [hAp,hep.1,conjugate_smul]
  have hcn : ell (conjugate (v p))=1 := by rw [hell,hep.2,star_one]
  have hh : (v p,μ p)=(conjugate (v p),star (μ p)) := hup.mp ⟨hce,hcn⟩
  exact ⟨(congrArg Prod.snd hh).symm,(congrArg Prod.fst hh).symm⟩

omit [Fintype ι] in
/-- Conjugating a normalized branch gives a normalized branch for the
conjugate eigenvalue. Local uniqueness of that second branch identifies it
with the conjugate of the first; no nearby reality is assumed. -/
theorem eventually_conjugate_pair
    (A : P → (ι → ℂ) →L[ℂ] (ι → ℂ)) (ell ell' : (ι → ℂ) →ₗ[ℂ] ℂ)
    (μ μ' : P → ℂ) (v v' : P → ι → ℂ)
    (hμ : ContinuousAt μ 0) (hv : ContinuousAt v 0)
    (hμ0 : star (μ 0)=μ' 0) (hv0 : conjugate (v 0)=v' 0)
    (hA : ∀ᶠ p in 𝓝 (0:P), ∀ u, A p (conjugate u)=conjugate (A p u))
    (hell : ∀ u, ell' (conjugate u)=star (ell u))
    (he : ∀ᶠ p in 𝓝 (0:P), A p (v p)=μ p • v p ∧ ell (v p)=1)
    (hunique : ∀ᶠ d in 𝓝 ((0:P),(v' 0,μ' 0)),
      (A d.1 d.2.1=d.2.2 • d.2.1 ∧ ell' d.2.1=1) ↔
        (v' d.1,μ' d.1)=d.2) :
    ∀ᶠ p in 𝓝 (0:P), star (μ p)=μ' p ∧ conjugate (v p)=v' p := by
  let d : P → P × ((ι → ℂ) × ℂ) := fun p => (p,(conjugate (v p),star (μ p)))
  have hd : ContinuousAt d 0 :=
    continuousAt_id.prodMk
      ((conjugate_continuous.continuousAt.comp hv).prodMk
        (Complex.continuous_conj.continuousAt.comp hμ))
  have hd0 : d 0=((0:P),(v' 0,μ' 0)) := by simp only [d,hv0,hμ0]
  have ht : Filter.Tendsto d (𝓝 (0:P)) (𝓝 ((0:P),(v' 0,μ' 0))) := by
    simpa only [hd0] using hd.tendsto
  filter_upwards [hA,he,ht.eventually hunique] with p hAp hep hup
  have hce : A p (conjugate (v p))=star (μ p) • conjugate (v p) := by
    rw [hAp,hep.1,conjugate_smul]
  have hcn : ell' (conjugate (v p))=1 := by rw [hell,hep.2,star_one]
  have hh : (v' p,μ' p)=(conjugate (v p),star (μ p)) := hup.mp ⟨hce,hcn⟩
  exact ⟨(congrArg Prod.snd hh).symm,(congrArg Prod.fst hh).symm⟩

/-- A scalar fixed by complex conjugation has vanishing imaginary part. -/
theorem eventually_im_zero (μ : P → ℂ)
    (hμ : ∀ᶠ p in 𝓝 (0:P), star (μ p)=μ p) :
    ∀ᶠ p in 𝓝 (0:P), (μ p).im=0 := by
  filter_upwards [hμ] with p hp
  exact Complex.conj_eq_iff_im.mp hp

end
end ThreeSitePhosphorylation.RealEigenpairPersistence
