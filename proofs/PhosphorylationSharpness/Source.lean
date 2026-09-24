import Mathlib

namespace PhosphorylationSharpness
noncomputable section
open scoped BigOperators

/-- Literal species S_0,...,S_n,E,F,C_0,...,C_{n-1},D_0,...,D_{n-1}. -/
structure State (n : ℕ) where
  S : Fin (n+1) → ℝ
  E : ℝ
  F : ℝ
  C : Fin n → ℝ
  D : Fin n → ℝ

/-- Six strictly positive constants per site: forward/reverse binding and catalysis. -/
structure Rates (n : ℕ) where
  a : Fin n → ℝ
  b : Fin n → ℝ
  c : Fin n → ℝ
  alpha : Fin n → ℝ
  beta : Fin n → ℝ
  gamma : Fin n → ℝ

def Rates.Positive {n : ℕ} (k : Rates n) : Prop :=
  ∀ i, 0 < k.a i ∧ 0 < k.b i ∧ 0 < k.c i ∧
    0 < k.alpha i ∧ 0 < k.beta i ∧ 0 < k.gamma i

def State.Positive {n : ℕ} (x : State n) : Prop :=
  (∀ i, 0 < x.S i) ∧ 0 < x.E ∧ 0 < x.F ∧ (∀ i, 0 < x.C i) ∧ (∀ i, 0 < x.D i)

def kinaseNet {n : ℕ} (k : Rates n) (x : State n) (i : Fin n) : ℝ :=
  k.a i*x.S i.castSucc*x.E-k.b i*x.C i
def phosphataseNet {n : ℕ} (k : Rates n) (x : State n) (i : Fin n) : ℝ :=
  k.alpha i*x.S i.succ*x.F-k.beta i*x.D i

/-- Mass-action derivative, with each reaction contributing to its literal species. -/
def field {n : ℕ} (k : Rates n) (x : State n) : State n where
  S j := ∑ i : Fin n, (
    (if i.castSucc = j then -kinaseNet k x i+k.gamma i*x.D i else 0) +
    (if i.succ = j then k.c i*x.C i-phosphataseNet k x i else 0))
  E := ∑ i, (-kinaseNet k x i+k.c i*x.C i)
  F := ∑ i, (-phosphataseNet k x i+k.gamma i*x.D i)
  C i := kinaseNet k x i-k.c i*x.C i
  D i := phosphataseNet k x i-k.gamma i*x.D i

def Equilibrium {n : ℕ} (k : Rates n) (x : State n) : Prop :=
  (∀ i, (field k x).S i=0) ∧ (field k x).E=0 ∧ (field k x).F=0 ∧
    (∀ i, (field k x).C i=0) ∧ (∀ i, (field k x).D i=0)

def totalE {n : ℕ} (x : State n) : ℝ := x.E+∑ i, x.C i
def totalF {n : ℕ} (x : State n) : ℝ := x.F+∑ i, x.D i
def totalS {n : ℕ} (x : State n) : ℝ := (∑ i, x.S i)+(∑ i, x.C i)+(∑ i, x.D i)

theorem equilibrium_of_currents {n : ℕ} (k : Rates n) (x : State n)
    (hE : ∀ i, kinaseNet k x i=k.c i*x.C i)
    (hF : ∀ i, phosphataseNet k x i=k.gamma i*x.D i)
    (hC : ∀ i, k.c i*x.C i=k.gamma i*x.D i) : Equilibrium k x := by
  simp [Equilibrium, field, hE, hF, hC]

def realize {n : ℕ} (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ) : Rates n where
  a i := 2*D i/t i.castSucc
  b i := D i/B i
  c i := D i/B i
  alpha i := 2*D i/t i.succ
  beta _ := 1
  gamma _ := 1

def reconstruct {n : ℕ} (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (u s f : ℝ) : State n where
  S i := t i*u^i.val*s
  E := u*f
  F := f
  C i := B i*u^(i.val+1)*s*f
  D i := D i*u^(i.val+1)*s*f

theorem realize_positive {n : ℕ} (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (ht : ∀ i, 0 < t i) (hB : ∀ i, 0 < B i) (hD : ∀ i, 0 < D i) :
    (realize t B D).Positive := by
  intro i
  dsimp [realize]
  exact ⟨div_pos (mul_pos (by norm_num) (hD i)) (ht _), div_pos (hD _) (hB _),
    div_pos (hD _) (hB _), div_pos (mul_pos (by norm_num) (hD i)) (ht _), by norm_num, by norm_num⟩

theorem reconstruct_positive {n : ℕ} (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (ht : ∀ i, 0 < t i) (hB : ∀ i, 0 < B i) (hD : ∀ i, 0 < D i)
    {u s f : ℝ} (hu : 0 < u) (hs : 0 < s) (hf : 0 < f) :
    (reconstruct t B D u s f).Positive := by
  refine ⟨?_, mul_pos hu hf, hf, ?_, ?_⟩
  · intro i
    exact mul_pos (mul_pos (ht _) (pow_pos hu _)) hs
  · intro i
    exact mul_pos (mul_pos (mul_pos (hB _) (pow_pos hu _)) hs) hf
  · intro i
    exact mul_pos (mul_pos (mul_pos (hD _) (pow_pos hu _)) hs) hf

theorem reconstruct_equilibrium {n : ℕ} (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (ht : ∀ i, 0 < t i) (hB : ∀ i, 0 < B i) (u s f : ℝ) :
    Equilibrium (realize t B D) (reconstruct t B D u s f) := by
  apply equilibrium_of_currents
  · intro i
    dsimp [kinaseNet, realize, reconstruct]
    rw [pow_succ]
    field_simp [ne_of_gt (ht i.castSucc), ne_of_gt (hB i)]
    ring
  · intro i
    dsimp [phosphataseNet, realize, reconstruct]
    field_simp [ne_of_gt (ht i.succ)]
    ring
  · intro i
    dsimp [realize, reconstruct]
    field_simp [ne_of_gt (hB i)]

def inventory {n : ℕ} (t : Fin n → ℝ) (u : ℝ) : ℝ := ∑ i, t i*u^i.val

theorem reconstruct_totals {n : ℕ} (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (u s f : ℝ) :
    totalE (reconstruct t B D u s f)=u*f*(1+s*inventory B u) ∧
    totalF (reconstruct t B D u s f)=f*(1+s*u*inventory D u) ∧
    totalS (reconstruct t B D u s f)=s*inventory t u+u*s*f*(inventory B u+inventory D u) := by
  have hc (v : Fin n → ℝ) : (∑ i, v i*u^(i.val+1)*s*f) = u*s*f*inventory v u := by
    simp only [inventory, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]
    ring
  have hs : (∑ i, t i*u^i.val*s) = s*inventory t u := by
    simp only [inventory, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [totalE, totalF, totalS, reconstruct, hc, hs]
  constructor
  · ring
  constructor <;> ring

theorem reconstruct_ratio {n : ℕ} (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (u s f : ℝ) (hf : f ≠ 0) :
    (reconstruct t B D u s f).E/(reconstruct t B D u s f).F=u := by
  simp [reconstruct, hf]

end
end PhosphorylationSharpness
