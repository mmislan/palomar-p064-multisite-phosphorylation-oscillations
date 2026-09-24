import proofs.ThreeSitePhosphorylation.ReturnMapContraction
import Mathlib

/-! A real eigenbasis whose eigenvalues lie strictly inside the unit interval
gives a contracting power. No complexification or spectrum identification is
required. Applications still have to supply the actual derivative eigenbasis. -/
namespace ThreeSitePhosphorylation.RealEigenbasisContraction
noncomputable section
open Filter
open scoped Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

omit [FiniteDimensional ℝ E] [Fintype ι] in
theorem power_eigenvector (A : E →L[ℝ] E) (v : E) (eig : ℝ)
    (hv : A v=eig • v) (n : ℕ) : (A^n) v=eig^n • v := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ',ContinuousLinearMap.mul_apply,ih,hv,smul_smul,mul_comm]

theorem eigenbasis_power_bound (A : E →L[ℝ] E) (b : Module.Basis ι ℝ E)
    (eig : ι → ℝ) (he : ∀ i, A (b i)=eig i • b i) (n : ℕ) :
    ‖A^n‖ ≤ ∑ i, |eig i|^n * ‖(b.coord i).toContinuousLinearMap‖ * ‖b i‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun i _ => by positivity))
  intro x
  have hx : (A^n) x=∑ i, b.repr x i • ((A^n) (b i)) := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum,map_smul]
  rw [hx,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [power_eigenvector A (b i) (eig i) (he i) n,norm_smul,norm_smul,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_pow]
  have hc : |b.repr x i| ≤ ‖(b.coord i).toContinuousLinearMap‖ * ‖x‖ :=
    (b.coord i).toContinuousLinearMap.le_opNorm x
  calc
    _ ≤ (‖(b.coord i).toContinuousLinearMap‖ * ‖x‖) * (|eig i|^n * ‖b i‖) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

theorem exists_contracting_power (A : E →L[ℝ] E) (b : Module.Basis ι ℝ E)
    (eig : ι → ℝ) (he : ∀ i, A (b i)=eig i • b i)
    (heig : ∀ i, |eig i|<1) : ∃ n : ℕ, 0<n ∧ ‖A^n‖<1 := by
  have ht : Tendsto (fun n : ℕ => ∑ i,
      |eig i|^n * ‖(b.coord i).toContinuousLinearMap‖ * ‖b i‖) atTop (𝓝 0) := by
    convert tendsto_finsetSum Finset.univ (fun i _ =>
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg (eig i)) (heig i)).mul_const
        ‖(b.coord i).toContinuousLinearMap‖).mul_const ‖b i‖) using 1
    simp
  have hh := ht.eventually (isOpen_Iio.mem_nhds (show (0:ℝ)<1 by norm_num))
  obtain ⟨n,hn,hb⟩ := ((Filter.eventually_gt_atTop 0).and hh).exists
  exact ⟨n,hn,(eigenbasis_power_bound A b eig he n).trans_lt hb⟩

/-- A contracting power also supplies the inverse needed to persist the
return-map fixed point by the implicit function theorem. -/
theorem isUnit_one_sub_of_contracting_power (A : E →L[ℝ] E)
    (n : ℕ) (hn : ‖A^n‖<1) : IsUnit (1-A) := by
  have hu : IsUnit (1-A^n) :=
    isUnit_one_sub_of_norm_lt_one (R := E →L[ℝ] E) hn
  let S := ∑ i ∈ Finset.range n, A^i
  have hc : Commute (1-A) S := by
    change (1-A)*S=S*(1-A)
    dsimp [S]
    rw [mul_neg_geom_sum,geom_sum_mul_neg]
  apply (hc.isUnit_mul_iff.mp ?_).1
  dsimp [S]
  rwa [mul_neg_geom_sum]

theorem eigenbasis_return_bound (P : E → E) (p : E) (A : E →L[ℝ] E)
    (b : Module.Basis ι ℝ E) (eig : ι → ℝ) (hp : P p=p)
    (hD : HasFDerivAt P A p) (he : ∀ i, A (b i)=eig i • b i)
    (heig : ∀ i, |eig i|<1) :
    ∃ N : ℕ, 0<N ∧ ∃ q : ℝ, 0≤q ∧ q<1 ∧ ∃ δ>0,
      ∀ x, dist x p<δ → ∀ n : ℕ,
        dist ((P^[N])^[n] x) p ≤ q^n*dist x p ∧ dist ((P^[N])^[n] x) p<δ := by
  obtain ⟨N,hN,hb⟩ := exists_contracting_power A b eig he heig
  have hpN := Function.iterate_fixed hp N
  obtain ⟨q,hq,hq1,δ,hδ,hbound⟩ :=
    OrbitalStability.derivative_return_bound (P^[N]) p (A^N) hpN (hD.iterate hp N) hb
  exact ⟨N,hN,q,hq,hq1,δ,hδ,hbound⟩

end
end ThreeSitePhosphorylation.RealEigenbasisContraction
