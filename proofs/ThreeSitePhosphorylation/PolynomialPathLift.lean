import proofs.ThreeSitePhosphorylation.Volterra

namespace ThreeSitePhosphorylation.PolynomialPathLift
noncomputable section
open scoped BigOperators

variable {P E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An affine scalar functional lifted to continuous paths. -/
def affinePath (α : ℝ) (ℓ : E →L[ℝ] ℝ) (u : ContinuousPath E) : ContinuousPath ℝ :=
  ContinuousLinearMap.const ℝ UnitTime α+ℓ.compLeftContinuous ℝ UnitTime u

@[simp] theorem affinePath_apply (α : ℝ) (ℓ : E →L[ℝ] ℝ)
    (u : ContinuousPath E) (t : UnitTime) : affinePath α ℓ u t=α+ℓ (u t) := rfl

theorem affinePath_smooth [NormedAddCommGroup P] [NormedSpace ℝ P]
    (α : P → ℝ) (ℓ : E →L[ℝ] ℝ)
    (hα : ContDiff ℝ ⊤ α) :
    ContDiff ℝ ⊤ (fun p : P × ContinuousPath E => affinePath (α p.1) ℓ p.2) := by
  exact ((ContinuousLinearMap.const ℝ UnitTime).contDiff.comp (hα.comp contDiff_fst)).add
    ((ℓ.compLeftContinuous ℝ UnitTime).contDiff.comp contDiff_snd)

/-- A scalar quadratic path row, with smooth scalar parameter coefficients.
Multiplication takes place in the supremum-norm ring of scalar paths. -/
def polynomialRow (c α β : P → ℝ) (ℓ m : E →L[ℝ] ℝ)
    (ε : P) (u : ContinuousPath E) : ContinuousPath ℝ :=
  c ε • (affinePath (α ε) ℓ u * affinePath (β ε) m u)

@[simp] theorem polynomialRow_apply (c α β : P → ℝ) (ℓ m : E →L[ℝ] ℝ)
    (ε : P) (u : ContinuousPath E) (t : UnitTime) :
    polynomialRow c α β ℓ m ε u t=
      c ε*((α ε+ℓ (u t))*(β ε+m (u t))) := rfl

theorem polynomialRow_smooth [NormedAddCommGroup P] [NormedSpace ℝ P]
    (c α β : P → ℝ) (ℓ m : E →L[ℝ] ℝ)
    (hc : ContDiff ℝ ⊤ c) (hα : ContDiff ℝ ⊤ α) (hβ : ContDiff ℝ ⊤ β) :
    ContDiff ℝ ⊤ (fun p : P × ContinuousPath E => polynomialRow c α β ℓ m p.1 p.2) := by
  exact (hc.comp contDiff_fst).smul ((affinePath_smooth α ℓ hα).mul (affinePath_smooth β m hβ))

/-- Injection of a scalar path into a fixed vector direction. -/
def injectPath (e : F) : ContinuousPath ℝ →L[ℝ] ContinuousPath F :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight e).compLeftContinuous ℝ UnitTime

@[simp] theorem injectPath_apply (e : F) (u : ContinuousPath ℝ) (t : UnitTime) :
    injectPath e u t=u t • e := rfl

variable {ι : Type*} [Fintype ι]

def injectedSum (e : ι → F) (rows : ι → P → ContinuousPath E → ContinuousPath ℝ)
    (ε : P) (u : ContinuousPath E) : ContinuousPath F :=
  ∑ i, injectPath (e i) (rows i ε u)

omit [NormedSpace ℝ E] in
theorem injectedSum_apply (e : ι → F)
    (rows : ι → P → ContinuousPath E → ContinuousPath ℝ)
    (ε : P) (u : ContinuousPath E) (t : UnitTime) :
    injectedSum e rows ε u t=∑ i, rows i ε u t • e i := by
  change (ContinuousMap.evalCLM (R := ℝ) (M := F) t) (∑ i, injectPath (e i) (rows i ε u))=_
  rw [map_sum]
  rfl

theorem injectedSum_smooth [NormedAddCommGroup P] [NormedSpace ℝ P] (e : ι → F)
    (rows : ι → P → ContinuousPath E → ContinuousPath ℝ)
    (hrows : ∀ i, ContDiff ℝ ⊤ (fun p : P × ContinuousPath E => rows i p.1 p.2)) :
    ContDiff ℝ ⊤ (fun p : P × ContinuousPath E => injectedSum e rows p.1 p.2) := by
  exact ContDiff.sum (fun i _ => (injectPath (e i)).contDiff.comp (hrows i))

/-- Finite assembly of the actual scalar polynomial rows. -/
theorem polynomial_injectedSum_smooth [NormedAddCommGroup P] [NormedSpace ℝ P]
    (e : ι → F) (c α β : ι → P → ℝ)
    (ℓ m : ι → E →L[ℝ] ℝ)
    (hc : ∀ i, ContDiff ℝ ⊤ (c i)) (hα : ∀ i, ContDiff ℝ ⊤ (α i))
    (hβ : ∀ i, ContDiff ℝ ⊤ (β i)) :
    ContDiff ℝ ⊤ (fun p : P × ContinuousPath E =>
      injectedSum e (fun i => polynomialRow (c i) (α i) (β i) (ℓ i) (m i)) p.1 p.2) :=
  injectedSum_smooth e _ (fun i => polynomialRow_smooth _ _ _ _ _ (hc i) (hα i) (hβ i))

theorem polynomial_injectedSum_apply (e : ι → F) (c α β : ι → P → ℝ)
    (ℓ m : ι → E →L[ℝ] ℝ) (ε : P) (u : ContinuousPath E) (t : UnitTime) :
    injectedSum e (fun i => polynomialRow (c i) (α i) (β i) (ℓ i) (m i)) ε u t=
      ∑ i, (c i ε*((α i ε+ℓ i (u t))*(β i ε+m i (u t)))) • e i := by
  rw [injectedSum_apply]
  rfl

end
end ThreeSitePhosphorylation.PolynomialPathLift
