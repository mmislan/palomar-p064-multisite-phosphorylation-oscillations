import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace ThreeSitePhosphorylation.NonZenoReturns
noncomputable section
open Filter
open scoped Topology

def elapsed (τ : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, τ i

@[simp] theorem elapsed_zero (τ : ℕ → ℝ) : elapsed τ 0=0 := by simp [elapsed]

@[simp] theorem elapsed_succ (τ : ℕ → ℝ) (n : ℕ) :
    elapsed τ (n+1)=elapsed τ n+τ n := by simp [elapsed,Finset.sum_range_succ]

theorem elapsed_strictMono (τ : ℕ → ℝ) (c : ℝ) (hc : 0<c) (hτ : ∀ n, c≤τ n) :
    StrictMono (elapsed τ) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [elapsed_succ]
  linarith [hτ n]

theorem elapsed_lower (τ : ℕ → ℝ) (c : ℝ) (hτ : ∀ n, c≤τ n) (n : ℕ) :
    (n:ℝ)*c≤elapsed τ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [elapsed_succ,Nat.cast_add,Nat.cast_one]
    linarith [hτ n]

theorem exists_elapsed_above (τ : ℕ → ℝ) (c : ℝ) (hc : 0<c)
    (hτ : ∀ n, c≤τ n) (t : ℝ) : ∃ n : ℕ, t<elapsed τ (n+1) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (t/c)
  refine ⟨n,?_⟩
  have hh : t<(n:ℝ)*c := (div_lt_iff₀ hc).mp hn
  have hl := elapsed_lower τ c hτ (n+1)
  push_cast at hl
  linarith

theorem elapsed_tendsto_atTop (τ : ℕ → ℝ) (c : ℝ) (hc : 0<c)
    (hτ : ∀ n, c≤τ n) : Tendsto (elapsed τ) atTop atTop := by
  apply tendsto_atTop.2
  intro t
  obtain ⟨n,hn⟩ := exists_elapsed_above τ c hc hτ t
  exact eventually_atTop.2 ⟨n+1,fun m hm =>
    hn.le.trans ((elapsed_strictMono τ c hc hτ).monotone hm)⟩

def count (τ : ℕ → ℝ) (c : ℝ) (hc : 0<c) (hτ : ∀ n, c≤τ n) (t : ℝ) : ℕ :=
  Nat.find (exists_elapsed_above τ c hc hτ t)

theorem count_upper (τ : ℕ → ℝ) (c : ℝ) (hc : 0<c) (hτ : ∀ n, c≤τ n) (t : ℝ) :
    t<elapsed τ (count τ c hc hτ t+1) := Nat.find_spec (exists_elapsed_above τ c hc hτ t)

theorem count_lower (τ : ℕ → ℝ) (c : ℝ) (hc : 0<c) (hτ : ∀ n, c≤τ n)
    (t : ℝ) (ht : 0≤t) : elapsed τ (count τ c hc hτ t)≤t := by
  cases hn : count τ c hc hτ t with
  | zero => simpa using ht
  | succ n =>
    have hlt : n<count τ c hc hτ t := by rw [hn]; exact Nat.lt_succ_self n
    exact le_of_not_gt (Nat.find_min (exists_elapsed_above τ c hc hτ t) hlt)

theorem count_eq_of_mem (τ : ℕ → ℝ) (c : ℝ) (hc : 0<c) (hτ : ∀ n, c≤τ n)
    (t : ℝ) (n : ℕ)
    (hl : elapsed τ n≤t) (hu : t<elapsed τ (n+1)) : count τ c hc hτ t=n := by
  apply le_antisymm
  · exact Nat.find_min' _ hu
  · by_contra hh
    have hn : count τ c hc hτ t+1≤n := Nat.succ_le_of_lt (lt_of_not_ge hh)
    have hm := (elapsed_strictMono τ c hc hτ).monotone hn
    exact (not_lt_of_ge (hm.trans hl)) (count_upper τ c hc hτ t)

theorem exists_unique_interval (τ : ℕ → ℝ) (c : ℝ) (hc : 0<c)
    (hτ : ∀ n, c≤τ n) (t : ℝ) (ht : 0≤t) :
    ∃! n : ℕ, elapsed τ n≤t ∧ t<elapsed τ (n+1) := by
  refine ⟨count τ c hc hτ t,⟨count_lower τ c hc hτ t ht,count_upper τ c hc hτ t⟩,?_⟩
  intro n hn
  exact (count_eq_of_mem τ c hc hτ t n hn.1 hn.2).symm

theorem count_tendsto_atTop (τ : ℕ → ℝ) (c : ℝ) (hc : 0<c)
    (hτ : ∀ n, c≤τ n) : Tendsto (count τ c hc hτ) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop (elapsed τ n)] with t ht
  by_contra hh
  have hn : count τ c hc hτ t+1≤n := Nat.succ_le_of_lt (lt_of_not_ge hh)
  have hm := (elapsed_strictMono τ c hc hτ).monotone hn
  exact (not_lt_of_ge (hm.trans ht)) (count_upper τ c hc hτ t)

end
end ThreeSitePhosphorylation.NonZenoReturns
