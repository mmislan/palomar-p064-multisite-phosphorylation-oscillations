import proofs.ThreeSitePhosphorylation.MultisiteSource

/-! Scaled new-site source algebra for the existential all-n construction.
This is not the manuscript's arbitrary-parent fixed-unit-rate inheritance
theorem, and makes no spectral or Hopf assertion. -/
namespace ThreeSitePhosphorylation.ScaledMultisiteSource
noncomputable section
open PhosphorylationSharpness
open MultisiteSource
open scoped BigOperators
set_option maxHeartbeats 500000

def appendScaledRates {n : ℕ} (k : Rates n) (κ a α : ℝ) : Rates (n+1) where
  a := Fin.lastCases a k.a
  b := Fin.lastCases κ k.b
  c := Fin.lastCases κ k.c
  alpha := Fin.lastCases α k.alpha
  beta := Fin.lastCases κ k.beta
  gamma := Fin.lastCases κ k.gamma

theorem scaled_enzymes_complexes {n : ℕ} (k : Rates n) (x : State n)
    (κ a α c s d : ℝ) :
    let f := field (appendScaledRates k κ a α) (appendState x c s d)
    f.E=(field k x).E-a*x.S (Fin.last n)*x.E+2*κ*c ∧
    f.F=(field k x).F-α*s*x.F+2*κ*d ∧
    (∀ i : Fin n, f.C i.castSucc=(field k x).C i) ∧
    (∀ i : Fin n, f.D i.castSucc=(field k x).D i) ∧
    f.C (Fin.last n)=a*x.S (Fin.last n)*x.E-2*κ*c ∧
    f.D (Fin.last n)=α*s*x.F-2*κ*d := by
  dsimp
  simp [field,Fin.sum_univ_castSucc,appendScaledRates,appendState,
    kinaseNet,phosphataseNet,← Fin.castSucc_succ]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  ring_nf
  simp
  constructor <;> simp only [mul_comm,mul_left_comm,mul_assoc] <;> ring

theorem scaled_substrate_old {n : ℕ} (k : Rates n) (x : State n)
    (κ a α c s d : ℝ) (j : Fin (n+1)) :
    (field (appendScaledRates k κ a α) (appendState x c s d)).S j.castSucc=
      (field k x).S j+
        if Fin.last n=j then -a*x.S (Fin.last n)*x.E+κ*c+κ*d else 0 := by
  have hj : Fin.last (n+1) ≠ j.castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  simp [field,Fin.sum_univ_castSucc,appendScaledRates,appendState,
    kinaseNet,phosphataseNet,← Fin.castSucc_succ,hj]
  split_ifs <;> ring

theorem scaled_substrate_new {n : ℕ} (k : Rates n) (x : State n)
    (κ a α c s d : ℝ) :
    (field (appendScaledRates k κ a α) (appendState x c s d)).S (Fin.last (n+1))=
      κ*c-α*s*x.F+κ*d := by
  simp [field,Fin.sum_univ_castSucc,appendScaledRates,appendState,
    kinaseNet,phosphataseNet,← Fin.castSucc_succ]
  ring

theorem scaled_zero_load_face {n : ℕ} (k : Rates n) (x : State n) (κ α : ℝ) :
    field (appendScaledRates k κ 0 α) (appendState x 0 0 0)=
      appendState (field k x) 0 0 0 := by
  have h := scaled_enzymes_complexes k x κ 0 α 0 0 0
  dsimp at h
  have hs : (field (appendScaledRates k κ 0 α) (appendState x 0 0 0)).S=
      (appendState (field k x) 0 0 0).S := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa [appendState] using scaled_substrate_new k x κ 0 α 0 0 0
    · simpa [appendState] using scaled_substrate_old k x κ 0 α 0 0 0 i
  have hc : (field (appendScaledRates k κ 0 α) (appendState x 0 0 0)).C=
      (appendState (field k x) 0 0 0).C := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa [appendState] using h.2.2.2.2.1
    · simpa [appendState] using h.2.2.1 i
  have hd : (field (appendScaledRates k κ 0 α) (appendState x 0 0 0)).D=
      (appendState (field k x) 0 0 0).D := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa [appendState] using h.2.2.2.2.2
    · simpa [appendState] using h.2.2.2.1 i
  have he := h.1
  have hf := h.2.1
  simp only [zero_mul,mul_zero,sub_zero,add_zero] at he hf
  cases hleft : field (appendScaledRates k κ 0 α) (appendState x 0 0 0)
  cases hright : appendState (field k x) 0 0 0
  simp_all [appendState]

theorem appendScaledRates_positive {n : ℕ} (k : Rates n) (hk : k.Positive)
    (κ a α : ℝ) (hκ : 0<κ) (ha : 0<a) (hα : 0<α) :
    (appendScaledRates k κ a α).Positive := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [appendScaledRates] using
      (show 0<a ∧ 0<κ ∧ 0<κ ∧ 0<α ∧ 0<κ ∧ 0<κ from ⟨ha,hκ,hκ,hα,hκ,hκ⟩)
  · simpa [appendScaledRates] using hk j

theorem scaled_append_equilibrium {n : ℕ} (k : Rates n) (x : State n)
    (hx : Equilibrium k x) (hs : x.S (Fin.last n) ≠ 0)
    (he : x.E ≠ 0) (hf : x.F ≠ 0) (κ ε : ℝ) :
    Equilibrium (appendScaledRates k κ (2*κ*ε/(x.S (Fin.last n)*x.E)) (κ/x.F))
      (appendState x ε (2*ε) ε) := by
  let a := 2*κ*ε/(x.S (Fin.last n)*x.E)
  let α := κ/x.F
  have ha : a*x.S (Fin.last n)*x.E=2*κ*ε := by
    dsimp [a]
    field_simp [hs,he]
  have hα : α*(2*ε)*x.F=2*κ*ε := by
    dsimp [α]
    field_simp [hf]
  have h := scaled_enzymes_complexes k x κ a α ε (2*ε) ε
  dsimp at h
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [scaled_substrate_new,hα]
      ring
    · rw [scaled_substrate_old,hx.1]
      split_ifs
      · field_simp [hs,he]
        ring
      · simp
  · rw [h.1,hx.2.1,ha]
    ring
  · rw [h.2.1,hx.2.2.1,hα]
    ring
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [h.2.2.2.2.1,ha]
      ring
    · rw [h.2.2.1,hx.2.2.2.1]
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [h.2.2.2.2.2,hα]
      ring
    · rw [h.2.2.2.1,hx.2.2.2.2]

theorem scaled_append_positive {n : ℕ} (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive) (κ ε : ℝ) (hκ : 0<κ) (hε : 0<ε) :
    (appendScaledRates k κ (2*κ*ε/(x.S (Fin.last n)*x.E)) (κ/x.F)).Positive ∧
      (appendState x ε (2*ε) ε).Positive := by
  constructor
  · apply appendScaledRates_positive k hk κ _ _ hκ
    · exact div_pos (mul_pos (mul_pos (by norm_num) hκ) hε) (mul_pos (hx.1 _) hx.2.1)
    · exact div_pos hκ hx.2.2.1
  · exact append_positive x hx ε (2*ε) ε hε (mul_pos (by norm_num) hε) hε

/-- The actual transverse expansion has linear block κK and a quadratic
term involving the derived old free-phosphatase variation. -/
theorem scaled_normal_expansion {n : ℕ} (k : Rates n) (x : State n)
    (κ f df c s d t : ℝ) (hf : f ≠ 0) (hF : x.F=f+t*df) :
    let v := field (appendScaledRates k κ 0 (κ/f)) (appendState x (t*c) (t*s) (t*d))
    ![v.C (Fin.last n),v.S (Fin.last (n+1)),v.D (Fin.last n)]=
      t • (κ • (![-2*c,c-s+d,s-2*d] : Fin 3 → ℝ))+
      t^2 • (κ • (![0,-df*s/f,df*s/f] : Fin 3 → ℝ)) := by
  have h := scaled_enzymes_complexes k x κ 0 (κ/f) (t*c) (t*s) (t*d)
  dsimp only at h ⊢
  rw [h.2.2.2.2.1,h.2.2.2.2.2,scaled_substrate_new,hF]
  ext i
  fin_cases i <;> simp <;> field_simp [hf] <;> ring

end
end ThreeSitePhosphorylation.ScaledMultisiteSource
