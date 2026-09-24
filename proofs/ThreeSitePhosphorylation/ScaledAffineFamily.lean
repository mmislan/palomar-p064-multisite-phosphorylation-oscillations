import proofs.ThreeSitePhosphorylation.ScaledMultisiteSource

/-! Componentwise affine rate families for the scaled existential induction.
No module structure on Rates is presumed. -/
namespace ThreeSitePhosphorylation.ScaledAffineFamily
noncomputable section
open PhosphorylationSharpness MultisiteSource ScaledMultisiteSource
set_option maxHeartbeats 400000

def affineRates {n : ℕ} (offset slope : Rates n) (r : ℝ) : Rates n where
  a i := offset.a i+r*slope.a i
  b i := offset.b i+r*slope.b i
  c i := offset.c i+r*slope.c i
  alpha i := offset.alpha i+r*slope.alpha i
  beta i := offset.beta i+r*slope.beta i
  gamma i := offset.gamma i+r*slope.gamma i

def ComponentwiseAffine {n : ℕ} (k : ℝ → Rates n) : Prop :=
  ∃ offset slope : Rates n, ∀ r, k r=affineRates offset slope r

theorem rates_ext {n : ℕ} (x y : Rates n)
    (ha : x.a=y.a) (hb : x.b=y.b) (hc : x.c=y.c)
    (hα : x.alpha=y.alpha) (hβ : x.beta=y.beta) (hγ : x.gamma=y.gamma) : x=y := by
  cases x
  cases y
  simp_all

/-- Translating the critical parameter changes only the intercept. -/
theorem affineRates_translate {n : ℕ} (offset slope : Rates n) (rstar r : ℝ) :
    affineRates offset slope (rstar+r)=affineRates (affineRates offset slope rstar) slope r := by
  apply rates_ext <;> funext i <;> simp only [affineRates] <;> ring

theorem componentwiseAffine_translate {n : ℕ} (k : ℝ → Rates n)
    (hk : ComponentwiseAffine k) (rstar : ℝ) :
    ComponentwiseAffine (fun r => k (rstar+r)) := by
  obtain ⟨offset,slope,hk⟩ := hk
  refine ⟨affineRates offset slope rstar,slope,?_⟩
  intro r
  change k (rstar+r) = _
  rw [hk,affineRates_translate]

/-- All six new slope entries are zero, including the four entries supplied
by the scale parameter. The old slope arrays remain unchanged. -/
theorem append_affineRates {n : ℕ} (offset slope : Rates n) (κ a α r : ℝ) :
    appendScaledRates (affineRates offset slope r) κ a α=
      affineRates (appendScaledRates offset κ a α) (appendScaledRates slope 0 0 0) r := by
  apply rates_ext <;> funext i
  all_goals refine Fin.lastCases ?_ (fun j => ?_) i
  all_goals simp [appendScaledRates,affineRates]

theorem componentwiseAffine_append {n : ℕ} (k : ℝ → Rates n)
    (hk : ComponentwiseAffine k) (κ a α : ℝ) :
    ComponentwiseAffine (fun r => appendScaledRates (k r) κ a α) := by
  obtain ⟨offset,slope,hk⟩ := hk
  refine ⟨appendScaledRates offset κ a α,appendScaledRates slope 0 0 0,?_⟩
  intro r
  change appendScaledRates (k r) κ a α = _
  rw [hk,append_affineRates]

/-- Fixed load and scale give constant new rates as r varies. -/
def extendedFamily {n : ℕ} (k : ℝ → Rates n) (x : State n) (κ ε r : ℝ) : Rates (n+1) :=
  appendScaledRates (k r) κ (2*κ*ε/(x.S (Fin.last n)*x.E)) (κ/x.F)

theorem extendedFamily_affine {n : ℕ} (k : ℝ → Rates n)
    (hk : ComponentwiseAffine k) (x : State n) (κ ε : ℝ) :
    ComponentwiseAffine (extendedFamily k x κ ε) :=
  componentwiseAffine_append k hk κ _ _

/-- The same appended state is an equilibrium for every real parameter.
Rate positivity is deliberately not asserted for every real r. -/
theorem extendedFamily_equilibrium {n : ℕ} (k : ℝ → Rates n) (x : State n)
    (hx : x.Positive) (heq : ∀ r, Equilibrium (k r) x) (κ ε : ℝ) :
    ∀ r, Equilibrium (extendedFamily k x κ ε r) (appendState x ε (2*ε) ε) := by
  intro r
  exact scaled_append_equilibrium (k r) x (heq r) (ne_of_gt (hx.1 _))
    (ne_of_gt hx.2.1) (ne_of_gt hx.2.2.1) κ ε

/-- Actual chemical positivity is retained wherever the parent rates are
positive, with the scale and load fixed and positive. -/
theorem extendedFamily_positive {n : ℕ} (k : ℝ → Rates n) (x : State n)
    (hx : x.Positive) (κ ε : ℝ) (hκ : 0<κ) (hε : 0<ε) (r : ℝ)
    (hk : (k r).Positive) :
    (extendedFamily k x κ ε r).Positive ∧ (appendState x ε (2*ε) ε).Positive :=
  scaled_append_positive (k r) x hk hx κ ε hκ hε

/-- Fixed critical-parameter translation preserves both the affine family
and the same parameter-independent appended equilibrium. -/
theorem translated_extension {n : ℕ} (k : ℝ → Rates n)
    (hk : ComponentwiseAffine k) (x : State n) (hx : x.Positive)
    (heq : ∀ r, Equilibrium (k r) x) (κ ε rstar : ℝ) :
    ComponentwiseAffine (fun r => extendedFamily k x κ ε (rstar+r)) ∧
      ∀ r, Equilibrium (extendedFamily k x κ ε (rstar+r)) (appendState x ε (2*ε) ε) := by
  exact ⟨componentwiseAffine_translate _ (extendedFamily_affine k hk x κ ε) rstar,
    fun r => extendedFamily_equilibrium k x hx heq κ ε (rstar+r)⟩

end
end ThreeSitePhosphorylation.ScaledAffineFamily
