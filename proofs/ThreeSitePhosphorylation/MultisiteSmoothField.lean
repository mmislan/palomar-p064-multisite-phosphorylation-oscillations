import proofs.ThreeSitePhosphorylation.MultisiteChart

/-! Actual reduced-source smoothness from scalar mass-action components.
No topological or module structure on full State or Rates is assumed. -/
namespace ThreeSitePhosphorylation.MultisiteSmoothField
noncomputable section
open PhosphorylationSharpness MultisiteChart
open scoped BigOperators
set_option maxHeartbeats 600000

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def RatesSmooth {n : ℕ} (k : P → Rates n) : Prop :=
  (∀ i, ContDiff ℝ ⊤ (fun p => (k p).a i)) ∧
  (∀ i, ContDiff ℝ ⊤ (fun p => (k p).b i)) ∧
  (∀ i, ContDiff ℝ ⊤ (fun p => (k p).c i)) ∧
  (∀ i, ContDiff ℝ ⊤ (fun p => (k p).alpha i)) ∧
  (∀ i, ContDiff ℝ ⊤ (fun p => (k p).beta i)) ∧
  (∀ i, ContDiff ℝ ⊤ (fun p => (k p).gamma i))

def StateSmooth {n : ℕ} (x : P → PhosphorylationSharpness.State n) : Prop :=
  (∀ i, ContDiff ℝ ⊤ (fun p => (x p).S i)) ∧
  ContDiff ℝ ⊤ (fun p => (x p).E) ∧ ContDiff ℝ ⊤ (fun p => (x p).F) ∧
  (∀ i, ContDiff ℝ ⊤ (fun p => (x p).C i)) ∧
  (∀ i, ContDiff ℝ ⊤ (fun p => (x p).D i))

theorem chart_smooth_components {n : ℕ} (Et Ft St : P → ℝ)
    (y : P → ReducedState n) (hE : ContDiff ℝ ⊤ Et) (hF : ContDiff ℝ ⊤ Ft)
    (hS : ContDiff ℝ ⊤ St) (hy : ContDiff ℝ ⊤ y) :
    StateSmooth (fun p => chart (Et p) (Ft p) (St p) (y p)) := by
  have hs (i : Fin n) : ContDiff ℝ ⊤ (fun p => (y p).1 i) := by fun_prop
  have hc (i : Fin n) : ContDiff ℝ ⊤ (fun p => (y p).2.1 i) := by fun_prop
  have hd (i : Fin n) : ContDiff ℝ ⊤ (fun p => (y p).2.2 i) := by fun_prop
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [chart,Fin.cons_zero]
      fun_prop
    · simpa only [chart,Fin.cons_succ] using hs i
  · dsimp only [chart]
    fun_prop
  · dsimp only [chart]
    fun_prop
  · exact hc
  · exact hd

/-- Finite sums of the literal enzyme-binding and conversion terms are
smooth whenever their scalar rate and state components are smooth. -/
theorem field_smooth_components {n : ℕ} (k : P → Rates n)
    (x : P → PhosphorylationSharpness.State n) (hk : RatesSmooth k) (hx : StateSmooth x) :
    StateSmooth (fun p => PhosphorylationSharpness.field (k p) (x p)) := by
  obtain ⟨ha,hb,hc,hα,hβ,hγ⟩ := hk
  obtain ⟨hS,hE,hF,hC,hD⟩ := hx
  have hkn (i : Fin n) : ContDiff ℝ ⊤ (fun p => kinaseNet (k p) (x p) i) := by
    unfold kinaseNet
    fun_prop
  have hpn (i : Fin n) : ContDiff ℝ ⊤ (fun p => phosphataseNet (k p) (x p) i) := by
    unfold phosphataseNet
    fun_prop
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j
    dsimp only [PhosphorylationSharpness.field]
    apply ContDiff.sum
    intro i _
    by_cases h0 : i.castSucc=j <;> by_cases h1 : i.succ=j <;>
      simp only [h0,h1,if_true,if_false] <;> fun_prop
  · dsimp only [PhosphorylationSharpness.field]
    fun_prop
  · dsimp only [PhosphorylationSharpness.field]
    fun_prop
  · intro i
    dsimp only [PhosphorylationSharpness.field]
    fun_prop
  · intro i
    dsimp only [PhosphorylationSharpness.field]
    fun_prop

/-- Joint smoothness of the actual reduced mass-action field with arbitrary
smooth scalar totals and componentwise smooth rate family. -/
theorem reducedField_joint_smooth {n : ℕ} (k : P → Rates n) (Et Ft St : P → ℝ)
    (hk : RatesSmooth k) (hE : ContDiff ℝ ⊤ Et) (hF : ContDiff ℝ ⊤ Ft)
    (hS : ContDiff ℝ ⊤ St) :
    ContDiff ℝ ⊤ (fun p : P × ReducedState n =>
      reducedField (Et p.1) (Ft p.1) (St p.1) (k p.1) p.2) := by
  have hkr : RatesSmooth (fun p : P × ReducedState n => k p.1) := by
    obtain ⟨ha,hb,hc,hα,hβ,hγ⟩ := hk
    exact ⟨fun i => (ha i).comp contDiff_fst,fun i => (hb i).comp contDiff_fst,
      fun i => (hc i).comp contDiff_fst,fun i => (hα i).comp contDiff_fst,
      fun i => (hβ i).comp contDiff_fst,fun i => (hγ i).comp contDiff_fst⟩
  have hchart := chart_smooth_components
    (fun p : P × ReducedState n => Et p.1) (fun p => Ft p.1) (fun p => St p.1)
    (fun p => p.2) (hE.comp contDiff_fst) (hF.comp contDiff_fst)
    (hS.comp contDiff_fst) contDiff_snd
  have hf := field_smooth_components (fun p : P × ReducedState n => k p.1)
    (fun p => chart (Et p.1) (Ft p.1) (St p.1) p.2) hkr hchart
  exact (contDiff_pi.mpr (fun i : Fin n => hf.1 i.succ)).prodMk
    ((contDiff_pi.mpr hf.2.2.2.1).prodMk (contDiff_pi.mpr hf.2.2.2.2))

theorem reducedField_fixed_totals_smooth {n : ℕ} (k : P → Rates n) (Et Ft St : ℝ)
    (hk : RatesSmooth k) :
    ContDiff ℝ ⊤ (fun p : P × ReducedState n => reducedField Et Ft St (k p.1) p.2) :=
  reducedField_joint_smooth k (fun _ => Et) (fun _ => Ft) (fun _ => St)
    hk contDiff_const contDiff_const contDiff_const

end
end ThreeSitePhosphorylation.MultisiteSmoothField
