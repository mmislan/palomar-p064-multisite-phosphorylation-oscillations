import proofs.ThreeSitePhosphorylation.MultisiteCenteredFace

/-! Actual fixed-inventory normal directional derivative at zero site load.
The normal order is C,S,D; no assertion is made about the upper-right block. -/
namespace ThreeSitePhosphorylation.MultisiteNormalDerivative
noncomputable section
open MultisiteChart MultisiteSource MultisiteCenteredFace
open scoped BigOperators
set_option maxHeartbeats 500000

def normalProjection {n : ℕ} (y : ReducedState (n+1)) : Fin 3 → ℝ :=
  ![y.2.1 (Fin.last n),y.1 (Fin.last n),y.2.2 (Fin.last n)]

def referenceF {n : ℕ} (Ft : ℝ) (zstar : ReducedState n) : ℝ :=
  Ft-∑ i, zstar.2.2 i

def phosphataseVariation {n : ℕ} (u : ReducedState n) (d : ℝ) : ℝ :=
  -(∑ i, u.2.2 i)-d

/-- Appending new coordinates at fixed inventories diminishes the old
inventories. This accounts explicitly for the omitted S0,E,F corrections. -/
theorem fixed_total_chart_path {n : ℕ} (Et Ft St : ℝ)
    (zstar u : ReducedState n) (c s d t : ℝ) :
    chart Et Ft St (faceInclusion n zstar + t • appendReduced u c s d)=
      appendState (chart (Et-t*c) (Ft-t*d) (St-t*(c+s+d)) (zstar+t • u))
        (t*c) (t*s) (t*d) := by
  have hy : faceInclusion n zstar + t • appendReduced u c s d=
      appendReduced (zstar+t • u) (t*c) (t*s) (t*d) := by
    change appendReduced zstar 0 0 0 + t • appendReduced u c s d=_
    rw [← appendReduced_smul]
    simpa only [zero_add] using
      (appendReduced_add zstar (t • u) 0 0 0 (t*c) (t*s) (t*d)).symm
  rw [hy]
  have h := chart_appendReduced (Et-t*c) (Ft-t*d) (St-t*(c+s+d))
    (zstar+t • u) (t*c) (t*s) (t*d)
  have he : Et-t*c+t*c=Et := by ring
  have hf : Ft-t*d+t*d=Ft := by ring
  have hs : St-t*(c+s+d)+t*c+t*s+t*d=St := by ring
  rw [he,hf,hs] at h
  exact h

/-- The free phosphatase variation is derived from the source chart,
including the newly added phosphatase complex. -/
theorem old_chart_freeF {n : ℕ} (Et Ft St : ℝ) (zstar u : ReducedState n)
    (c s d t : ℝ) :
    (chart (Et-t*c) (Ft-t*d) (St-t*(c+s+d)) (zstar+t • u)).F=
      referenceF Ft zstar+t*phosphataseVariation u d := by
  change Ft-t*d-(∑ i, (zstar.2.2 i+t*u.2.2 i))=
    (Ft-∑ i, zstar.2.2 i)+t*(-(∑ i, u.2.2 i)-d)
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  ring

/-- Exact actual-source normal expansion, for arbitrary site count,
parent center, and direction. Only nonzero reference free F is required. -/
theorem centered_normal_expansion {n : ℕ} (Et Ft St : ℝ)
    (k : PhosphorylationSharpness.Rates n) (zstar u : ReducedState n)
    (c s d t : ℝ) (hf : referenceF Ft zstar ≠ 0) :
    normalProjection (centeredField Et Ft St
      (appendRates k 0 (1/referenceF Ft zstar)) (faceInclusion n zstar)
      (t • appendReduced u c s d))=
      t • (![-2*c,c-s+d,s-2*d] : Fin 3 → ℝ) +
      t^2 • (![0,-phosphataseVariation u d*s/referenceF Ft zstar,
        phosphataseVariation u d*s/referenceF Ft zstar] : Fin 3 → ℝ) := by
  have h := appended_normal_expansion k
    (chart (Et-t*c) (Ft-t*d) (St-t*(c+s+d)) (zstar+t • u))
    (referenceF Ft zstar) (phosphataseVariation u d) c s d t hf
    (old_chart_freeF Et Ft St zstar u c s d t)
  dsimp only at h
  change ![(PhosphorylationSharpness.field (appendRates k 0 (1/referenceF Ft zstar))
      (chart Et Ft St (faceInclusion n zstar+t • appendReduced u c s d))).C (Fin.last n),
    (PhosphorylationSharpness.field (appendRates k 0 (1/referenceF Ft zstar))
      (chart Et Ft St (faceInclusion n zstar+t • appendReduced u c s d))).S (Fin.last (n+1)),
    (PhosphorylationSharpness.field (appendRates k 0 (1/referenceF Ft zstar))
      (chart Et Ft St (faceInclusion n zstar+t • appendReduced u c s d))).D (Fin.last n)]=_
  rw [fixed_total_chart_path]
  exact h

/-- Actual directional derivative of the normal projection is the fixed
Hurwitz block K(c,s,d)=(-2c,c-s+d,s-2d), independent of the old direction. -/
theorem centered_normal_hasDerivAt {n : ℕ} (Et Ft St : ℝ)
    (k : PhosphorylationSharpness.Rates n) (zstar u : ReducedState n)
    (c s d : ℝ) (hf : referenceF Ft zstar ≠ 0) :
    HasDerivAt (fun t : ℝ => normalProjection (centeredField Et Ft St
      (appendRates k 0 (1/referenceF Ft zstar)) (faceInclusion n zstar)
      (t • appendReduced u c s d))) (![-2*c,c-s+d,s-2*d] : Fin 3 → ℝ) 0 := by
  have he : (fun t : ℝ => normalProjection (centeredField Et Ft St
      (appendRates k 0 (1/referenceF Ft zstar)) (faceInclusion n zstar)
      (t • appendReduced u c s d)))=
      (fun t : ℝ => t • (![-2*c,c-s+d,s-2*d] : Fin 3 → ℝ)+
        t^2 • (![0,-phosphataseVariation u d*s/referenceF Ft zstar,
          phosphataseVariation u d*s/referenceF Ft zstar] : Fin 3 → ℝ)) :=
    funext (fun t => centered_normal_expansion Et Ft St k zstar u c s d t hf)
  rw [he]
  simpa only [id_eq, show (2 : ℕ)-1=1 from rfl, pow_one, mul_zero,
    zero_mul, zero_smul, one_smul, add_zero] using ((hasDerivAt_id (0:ℝ)).smul_const
    (![-2*c,c-s+d,s-2*d] : Fin 3 → ℝ)).add
    (((hasDerivAt_id (0:ℝ)).pow 2).smul_const
      (![0,-phosphataseVariation u d*s/referenceF Ft zstar,
        phosphataseVariation u d*s/referenceF Ft zstar] : Fin 3 → ℝ))

end
end ThreeSitePhosphorylation.MultisiteNormalDerivative
