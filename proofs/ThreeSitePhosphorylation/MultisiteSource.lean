import proofs.PhosphorylationSharpness.Source
import proofs.ThreeSitePhosphorylation.AddedSite

/-! Literal uniform site addition for P064. This is source algebra, not a
theorem of Hopf persistence or orbital attraction. -/
namespace ThreeSitePhosphorylation.MultisiteSource
noncomputable section
open PhosphorylationSharpness
open scoped BigOperators

def appendState {n : ℕ} (x : State n) (c s d : ℝ) : State (n+1) where
  S := Fin.lastCases s x.S
  E := x.E
  F := x.F
  C := Fin.lastCases c x.C
  D := Fin.lastCases d x.D

def appendRates {n : ℕ} (k : Rates n) (a α : ℝ) : Rates (n+1) where
  a := Fin.lastCases a k.a
  b := Fin.lastCases 1 k.b
  c := Fin.lastCases 1 k.c
  alpha := Fin.lastCases α k.alpha
  beta := Fin.lastCases 1 k.beta
  gamma := Fin.lastCases 1 k.gamma

@[simp] theorem kinase_old {n : ℕ} (k : Rates n) (x : State n)
    (a α c s d : ℝ) (i : Fin n) :
    kinaseNet (appendRates k a α) (appendState x c s d) i.castSucc =
      kinaseNet k x i := by
  simp [kinaseNet, appendRates, appendState]

@[simp] theorem phosphatase_old {n : ℕ} (k : Rates n) (x : State n)
    (a α c s d : ℝ) (i : Fin n) :
    phosphataseNet (appendRates k a α) (appendState x c s d) i.castSucc =
      phosphataseNet k x i := by
  simp [phosphataseNet, appendRates, appendState, ← Fin.castSucc_succ]

theorem append_field_enzymes_complexes {n : ℕ} (k : Rates n) (x : State n)
    (a α c s d : ℝ) :
    let f := field (appendRates k a α) (appendState x c s d)
    f.E = (field k x).E - a*x.S (Fin.last n)*x.E + 2*c ∧
    f.F = (field k x).F - α*s*x.F + 2*d ∧
    (∀ i : Fin n, f.C i.castSucc = (field k x).C i) ∧
    (∀ i : Fin n, f.D i.castSucc = (field k x).D i) ∧
    f.C (Fin.last n) = a*x.S (Fin.last n)*x.E - 2*c ∧
    f.D (Fin.last n) = α*s*x.F - 2*d := by
  dsimp
  simp [field, Fin.sum_univ_castSucc, appendRates, appendState,
    kinaseNet, phosphataseNet, ← Fin.castSucc_succ]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring_nf
  simp
  constructor <;> simp only [mul_comm, mul_left_comm, mul_assoc] <;> ring

theorem append_field_substrate_old {n : ℕ} (k : Rates n) (x : State n)
    (a α c s d : ℝ) (j : Fin (n+1)) :
    (field (appendRates k a α) (appendState x c s d)).S j.castSucc =
      (field k x).S j +
        if Fin.last n = j then -a*x.S (Fin.last n)*x.E+c+d else 0 := by
  have hj : Fin.last (n+1) ≠ j.castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  simp [field, Fin.sum_univ_castSucc, appendRates, appendState,
    kinaseNet, phosphataseNet, ← Fin.castSucc_succ, hj]
  split_ifs <;> ring

theorem append_field_substrate_new {n : ℕ} (k : Rates n) (x : State n)
    (a α c s d : ℝ) :
    (field (appendRates k a α) (appendState x c s d)).S (Fin.last (n+1)) =
      c-α*s*x.F+d := by
  simp [field, Fin.sum_univ_castSucc, appendRates, appendState,
    kinaseNet, phosphataseNet, ← Fin.castSucc_succ]
  ring

theorem zero_load_face {n : ℕ} (k : Rates n) (x : State n) (α : ℝ) :
    field (appendRates k 0 α) (appendState x 0 0 0) =
      appendState (field k x) 0 0 0 := by
  have h := append_field_enzymes_complexes k x 0 α 0 0 0
  dsimp at h
  have hs : (field (appendRates k 0 α) (appendState x 0 0 0)).S =
      (appendState (field k x) 0 0 0).S := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa [appendState] using append_field_substrate_new k x 0 α 0 0 0
    · simpa [appendState] using append_field_substrate_old k x 0 α 0 0 0 i
  have hc : (field (appendRates k 0 α) (appendState x 0 0 0)).C =
      (appendState (field k x) 0 0 0).C := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa [appendState] using h.2.2.2.2.1
    · simpa [appendState] using h.2.2.1 i
  have hd : (field (appendRates k 0 α) (appendState x 0 0 0)).D =
      (appendState (field k x) 0 0 0).D := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa [appendState] using h.2.2.2.2.2
    · simpa [appendState] using h.2.2.2.1 i
  have he := h.1
  have hf := h.2.1
  simp only [zero_mul, sub_zero] at he hf
  cases hleft : field (appendRates k 0 α) (appendState x 0 0 0)
  cases hright : appendState (field k x) 0 0 0
  simp_all [appendState]

theorem append_totals {n : ℕ} (x : State n) (c s d : ℝ) :
    totalE (appendState x c s d) = totalE x + c ∧
    totalF (appendState x c s d) = totalF x + d ∧
    totalS (appendState x c s d) = totalS x + c+s+d := by
  simp [totalE, totalF, totalS, appendState, Fin.sum_univ_castSucc]
  ring_nf
  simp

theorem append_positive {n : ℕ} (x : State n) (hx : x.Positive)
    (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hd : 0 < d) :
    (appendState x c s d).Positive := by
  refine ⟨?_, hx.2.1, hx.2.2.1, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [appendState] using hs
    · simpa [appendState] using hx.1 j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [appendState] using hc
    · simpa [appendState] using hx.2.2.2.1 j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [appendState] using hd
    · simpa [appendState] using hx.2.2.2.2 j

theorem append_rates_positive {n : ℕ} (k : Rates n) (hk : k.Positive)
    (a α : ℝ) (ha : 0 < a) (hα : 0 < α) :
    (appendRates k a α).Positive := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [appendRates] using
      (show 0 < a ∧ (0:ℝ) < 1 ∧ (0:ℝ) < 1 ∧ 0 < α ∧ (0:ℝ) < 1 ∧ (0:ℝ) < 1
        from ⟨ha, by norm_num, by norm_num, hα, by norm_num, by norm_num⟩)
  · simpa [appendRates] using hk j

theorem append_equilibrium {n : ℕ} (k : Rates n) (x : State n)
    (hx : Equilibrium k x) (hs : x.S (Fin.last n) ≠ 0)
    (he : x.E ≠ 0) (hf : x.F ≠ 0) (ε : ℝ) :
    Equilibrium (appendRates k (2*ε/(x.S (Fin.last n)*x.E)) (1/x.F))
      (appendState x ε (2*ε) ε) := by
  let a := 2*ε/(x.S (Fin.last n)*x.E)
  let α := 1/x.F
  have ha : a*x.S (Fin.last n)*x.E = 2*ε := by
    dsimp [a]
    field_simp
  have hα : α*(2*ε)*x.F = 2*ε := by
    dsimp [α]
    field_simp
  have h := append_field_enzymes_complexes k x a α ε (2*ε) ε
  dsimp at h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [append_field_substrate_new, hα]
      ring
    · rw [append_field_substrate_old, hx.1]
      split_ifs
      · field_simp
        ring
      · simp
  · rw [h.1, hx.2.1, ha]
    ring
  · rw [h.2.1, hx.2.2.1, hα]
    ring
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [h.2.2.2.2.1, ha]
      ring
    · rw [h.2.2.1, hx.2.2.2.1]
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [h.2.2.2.2.2, hα]
      ring
    · rw [h.2.2.2.1, hx.2.2.2.2]

/- The normal equations are exactly the local AddedSite field, uniformly in n. -/
theorem appended_normal_field {n : ℕ} (k : Rates n) (x : State n)
    (a α c s d : ℝ) :
    let v := field (appendRates k a α) (appendState x c s d)
    ![v.C (Fin.last n), v.S (Fin.last (n+1)), v.D (Fin.last n)] =
      let w := AddedSite.field a α ![x.S (Fin.last n),x.E,x.F,c,s,d]
      ![w 3,w 4,w 5] := by
  have h := append_field_enzymes_complexes k x a α c s d
  dsimp at h ⊢
  rw [h.2.2.2.2.1, h.2.2.2.2.2, append_field_substrate_new]
  simp [AddedSite.field]

theorem appended_normal_expansion {n : ℕ} (k : Rates n) (x : State n)
    (f df c s d t : ℝ) (hf : f ≠ 0) (hF : x.F = f+t*df) :
    let v := field (appendRates k 0 (1/f)) (appendState x (t*c) (t*s) (t*d))
    ![v.C (Fin.last n), v.S (Fin.last (n+1)), v.D (Fin.last n)] =
      t • (![-2*c,c-s+d,s-2*d] : Fin 3 → ℝ) +
      t^2 • (![0,-df*s/f,df*s/f] : Fin 3 → ℝ) := by
  dsimp only
  rw [appended_normal_field, hF]
  exact AddedSite.zero_load_expansion (x.S (Fin.last n)) x.E f df c s d t hf

/- Positive-cone weighted drift for the time-dependent transverse block.
This algebraic estimate alone is not an ODE contraction theorem. -/
theorem transverse_weighted_drift (a m c s d : ℝ)
    (hma : m ≤ a) (hc : 0 ≤ c) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hm1 : m ≤ 4) (hm2 : m ≤ 8/3) :
    (-2*c) + (c-a*s+d) + (3/4)*(a*s-2*d) ≤
      -(m/4)*(c+s+(3/4)*d) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hma) hs,
    mul_nonneg (sub_nonneg.mpr hm1) hc,
    mul_nonneg (sub_nonneg.mpr hm2) hd]

end
end ThreeSitePhosphorylation.MultisiteSource
