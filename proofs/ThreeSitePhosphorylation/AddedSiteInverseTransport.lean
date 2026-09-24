import Mathlib.Algebra.Module.LinearMap.Basic

namespace ThreeSitePhosphorylation.AddedSiteInverseTransport

/-- An intertwining identity transports actual inverses by uniqueness.
Invertibility is not inferred from the intertwining identity. -/
theorem inverse_transport {V W : Type*} (A I : V → V) (B J : W → W) (j : V → W)
    (hinter : ∀ x, B (j x)=j (A x))
    (hI : ∀ x, A (I x)=x) (hJ : ∀ y, B (J y)=y)
    (hB : Function.Injective B) (x : V) : J (j x)=j (I x) := by
  apply hB
  rw [hJ,hinter,hI]

section Linear
variable {𝕜 V W : Type*} [CommRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]

theorem shift_intertwining (A : V →ₗ[𝕜] V) (B : W →ₗ[𝕜] W) (j : V →ₗ[𝕜] W)
    (hinter : ∀ x, B (j x)=j (A x)) (c : 𝕜) (x : V) :
    c • j x-B (j x)=j (c • x-A x) := by
  rw [hinter,map_sub,map_smul]

/-- Applies to the second-harmonic shift, once its genuine inverse and the
source Jacobian intertwining have been established. -/
theorem inverse_shift_transport (A : V →ₗ[𝕜] V) (B : W →ₗ[𝕜] W)
    (j : V →ₗ[𝕜] W) (hinter : ∀ x, B (j x)=j (A x)) (c : 𝕜)
    (I : V → V) (J : W → W)
    (hI : ∀ x, c • I x-A (I x)=x)
    (hJ : ∀ y, c • J y-B (J y)=y)
    (hB : Function.Injective (fun y => c • y-B y)) (x : V) :
    J (j x)=j (I x) :=
  inverse_transport (fun y => c • y-A y) I (fun y => c • y-B y) J j
    (shift_intertwining A B j hinter c) hI hJ hB x

end Linear
end ThreeSitePhosphorylation.AddedSiteInverseTransport
