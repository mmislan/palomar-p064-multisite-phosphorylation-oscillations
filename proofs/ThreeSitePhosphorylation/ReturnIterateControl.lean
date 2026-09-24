import proofs.ThreeSitePhosphorylation.ReturnMapContraction

namespace ThreeSitePhosphorylation.ReturnIterateControl
noncomputable section
open Filter
open scoped Topology
variable {E : Type*} [MetricSpace E]

omit [MetricSpace E] in
theorem iterate_remainder (P : E → E) (N k : ℕ) (x : E) :
    P^[k] x=P^[k%N] ((P^[N])^[k/N] x) := by
  rw [← Function.iterate_mul,← Function.iterate_add_apply]
  rw [Nat.mod_add_div]

theorem finite_iterates_control (P : E → E) (p : E) (hp : P p=p) (N : ℕ)
    (hcont : ∀ j : Fin N, ContinuousAt (P^[j.val]) p) (ε : ℝ) (hε : 0<ε) :
    ∃ η>0, ∀ x, dist x p<η → ∀ j : Fin N, dist (P^[j.val] x) p<ε := by
  have hev : ∀ᶠ x in 𝓝 p, ∀ j : Fin N, dist (P^[j.val] x) p<ε := by
    apply Filter.eventually_all.mpr
    intro j
    have hh := (hcont j).tendsto.eventually (Metric.ball_mem_nhds (P^[j.val] p) hε)
    simpa only [Metric.mem_ball,Function.iterate_fixed hp] using hh
  exact Metric.eventually_nhds_iff.mp hev

theorem all_iterates_tendsto (P : E → E) (p x : E) (hp : P p=p)
    (N : ℕ) (hN : 0<N) (hcont : ∀ j : Fin N, ContinuousAt (P^[j.val]) p)
    (q : ℝ) (hq : 0≤q) (hq1 : q<1)
    (hblock : ∀ n, dist ((P^[N])^[n] x) p≤q^n*dist x p) :
    Tendsto (fun k : ℕ => P^[k] x) atTop (𝓝 p) := by
  have hzero : Tendsto (fun n : ℕ => q^n*dist x p) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const (dist x p)
  have hb : Tendsto (fun n : ℕ => dist ((P^[N])^[n] x) p) atTop (𝓝 0) :=
    squeeze_zero (fun _ => dist_nonneg) hblock hzero
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨η,hη,hfinite⟩ := finite_iterates_control P p hp N hcont ε hε
  have he := hb.eventually (Iio_mem_nhds hη)
  obtain ⟨M,hM⟩ := eventually_atTop.1 he
  refine eventually_atTop.2 ⟨M*N,?_⟩
  intro k hk
  have hdiv : M≤k/N := (Nat.le_div_iff_mul_le hN).2 hk
  rw [iterate_remainder P N k x]
  exact hfinite _ (hM (k/N) hdiv) ⟨k%N,Nat.mod_lt k hN⟩

/-- A smaller initial ball keeps every return, including intermediate returns
between contracting blocks, inside any prescribed ball and gives convergence. -/
theorem all_iterates_control (P : E → E) (p : E) (hp : P p=p)
    (N : ℕ) (hN : 0<N) (hcont : ∀ j : Fin N, ContinuousAt (P^[j.val]) p)
    (q δ : ℝ) (hq : 0≤q) (hq1 : q<1) (hδ : 0<δ)
    (hblock : ∀ x, dist x p<δ → ∀ n, dist ((P^[N])^[n] x) p≤q^n*dist x p)
    (ε : ℝ) (hε : 0<ε) :
    ∃ η>0, η≤δ ∧ ∀ x, dist x p<η →
      (∀ k : ℕ, dist (P^[k] x) p<ε) ∧ Tendsto (fun k : ℕ => P^[k] x) atTop (𝓝 p) := by
  obtain ⟨ρ,hρ,hfinite⟩ := finite_iterates_control P p hp N hcont ε hε
  refine ⟨min δ ρ,lt_min hδ hρ,min_le_left _ _,?_⟩
  intro x hx
  have hxδ := hx.trans_le (min_le_left δ ρ)
  have hxρ := hx.trans_le (min_le_right δ ρ)
  refine ⟨?_,all_iterates_tendsto P p x hp N hN hcont q hq hq1 (hblock x hxδ)⟩
  intro k
  have hb : dist ((P^[N])^[k/N] x) p<ρ :=
    ((hblock x hxδ (k/N)).trans
      (mul_le_of_le_one_left dist_nonneg (pow_le_one₀ hq hq1.le))).trans_lt hxρ
  rw [iterate_remainder P N k x]
  exact hfinite _ hb ⟨k%N,Nat.mod_lt k hN⟩

end
end ThreeSitePhosphorylation.ReturnIterateControl
