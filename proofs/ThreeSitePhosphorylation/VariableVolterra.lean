import proofs.ThreeSitePhosphorylation.Volterra

/-! Full-interval variable-coefficient Volterra inversion. The operator is
linear in the path, while its coefficient is an arbitrary continuous path
of bounded linear maps. No small-time or small-coefficient assumption. -/
namespace ThreeSitePhosphorylation
noncomputable section
open scoped BigOperators
open MeasureTheory
set_option maxHeartbeats 400000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def variablePicardIntegrand (A : ContinuousPath (E →L[ℝ] E))
    (u : ContinuousPath E) : ℝ → E :=
  fun t => (pathExtension A t) (pathExtension u t)

theorem variablePicardIntegrand_continuous (A : ContinuousPath (E →L[ℝ] E))
    (u : ContinuousPath E) : Continuous (variablePicardIntegrand A u) :=
  (pathExtension_continuous A).clm_apply (pathExtension_continuous u)

theorem variablePicardIntegrand_norm (A : ContinuousPath (E →L[ℝ] E))
    (u : ContinuousPath E) (t : ℝ) :
    ‖variablePicardIntegrand A u t‖ ≤ ‖A‖*‖u‖ := by
  exact ((pathExtension A t).le_opNorm _).trans
    (mul_le_mul (ContinuousMap.norm_coe_le_norm A _) (ContinuousMap.norm_coe_le_norm u _)
      (norm_nonneg (pathExtension u t)) (norm_nonneg A))

def variablePicardPath (A : ContinuousPath (E →L[ℝ] E))
    (u : ContinuousPath E) : ContinuousPath E :=
  ⟨fun t => ∫ s in (0:ℝ)..(t:ℝ), variablePicardIntegrand A u s,
    (intervalIntegral.continuous_primitive
      (fun _ _ => (variablePicardIntegrand_continuous A u).intervalIntegrable _ _) 0).comp
      continuous_subtype_val⟩

theorem variablePicardPath_bound (A : ContinuousPath (E →L[ℝ] E))
    (u : ContinuousPath E) : ‖variablePicardPath A u‖ ≤ ‖A‖*‖u‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := (t:ℝ)) (C := ‖A‖*‖u‖)
    (f := variablePicardIntegrand A u) (fun s _ => variablePicardIntegrand_norm A u s)
  have ht : |(t:ℝ)| ≤ 1 := by rw [abs_of_nonneg t.2.1]; exact t.2.2
  change ‖∫ s in (0:ℝ)..(t:ℝ), variablePicardIntegrand A u s‖ ≤ _
  apply hb.trans
  calc
    ‖A‖*‖u‖*|(t:ℝ)-0| ≤ ‖A‖*‖u‖*1 :=
      mul_le_mul_of_nonneg_left (by simpa only [sub_zero] using ht) (by positivity)
    _ = _ := mul_one _

def variablePicardLinear (A : ContinuousPath (E →L[ℝ] E)) :
    ContinuousPath E →ₗ[ℝ] ContinuousPath E where
  toFun := variablePicardPath A
  map_add' u v := by
    ext t
    change (∫ s in (0:ℝ)..(t:ℝ), variablePicardIntegrand A (u+v) s) = _
    simp only [variablePicardIntegrand,pathExtension,ContinuousMap.add_apply,map_add]
    exact intervalIntegral.integral_add
      ((variablePicardIntegrand_continuous A u).intervalIntegrable _ _)
      ((variablePicardIntegrand_continuous A v).intervalIntegrable _ _)
  map_smul' c u := by
    ext t
    change (∫ s in (0:ℝ)..(t:ℝ), variablePicardIntegrand A (c • u) s) = _
    simp only [variablePicardIntegrand,pathExtension,ContinuousMap.smul_apply,map_smul]
    exact intervalIntegral.integral_smul c _

def variablePicard (A : ContinuousPath (E →L[ℝ] E)) :
    ContinuousPath E →L[ℝ] ContinuousPath E :=
  (variablePicardLinear A).mkContinuous ‖A‖ (variablePicardPath_bound A)

theorem variablePicard_pow_bound (A : ContinuousPath (E →L[ℝ] E))
    (u : ContinuousPath E) (n : ℕ) (t : UnitTime) :
    ‖(((variablePicard A)^n) u) t‖ ≤ ‖A‖^n*(t:ℝ)^n/(n.factorial:ℝ)*‖u‖ := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.norm_coe_le_norm u t
  | succ n hn =>
    have he : (((variablePicard A)^(n+1)) u) t =
        ∫ s in (0:ℝ)..(t:ℝ), variablePicardIntegrand A (((variablePicard A)^n) u) s := by
      rw [pow_succ']
      rfl
    rw [he]
    calc
      _ ≤ ∫ s in (0:ℝ)..(t:ℝ), ‖A‖^(n+1)*s^n/(n.factorial:ℝ)*‖u‖ := by
        apply intervalIntegral.norm_integral_le_of_norm_le t.2.1
        · apply Filter.Eventually.of_forall
          intro s hs
          have hs' : s ∈ Set.Icc (0:ℝ) 1 := ⟨hs.1.le,hs.2.trans t.2.2⟩
          simp only [variablePicardIntegrand,pathExtension,Set.projIcc_of_mem _ hs']
          calc
            _ ≤ ‖A ⟨s,hs'⟩‖*‖(((variablePicard A)^n) u) ⟨s,hs'⟩‖ :=
              (A ⟨s,hs'⟩).le_opNorm _
            _ ≤ ‖A‖*‖(((variablePicard A)^n) u) ⟨s,hs'⟩‖ :=
              mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm A _) (norm_nonneg _)
            _ ≤ ‖A‖*(‖A‖^n*s^n/(n.factorial:ℝ)*‖u‖) :=
              mul_le_mul_of_nonneg_left (hn ⟨s,hs'⟩) (norm_nonneg A)
            _ = _ := by ring
        · exact (by fun_prop : Continuous (fun s : ℝ =>
            ‖A‖^(n+1)*s^n/(n.factorial:ℝ)*‖u‖)).intervalIntegrable _ _
      _ = _ := by
        rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_div,
          intervalIntegral.integral_const_mul,integral_pow]
        simp only [zero_pow (Nat.succ_ne_zero n),sub_zero,Nat.factorial_succ,Nat.cast_mul,
          Nat.cast_add,Nat.cast_one]
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring

theorem variablePicard_pow_norm (A : ContinuousPath (E →L[ℝ] E)) (n : ℕ) :
    ‖(variablePicard A)^n‖ ≤ ‖A‖^n/(n.factorial:ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  calc
    _ ≤ ‖A‖^n*(t:ℝ)^n/(n.factorial:ℝ)*‖u‖ := variablePicard_pow_bound A u n t
    _ ≤ ‖A‖^n*1/(n.factorial:ℝ)*‖u‖ := by
      gcongr
      exact pow_le_one₀ t.2.1 t.2.2
    _ = _ := by ring

/-- An arbitrary continuous coefficient path gives an invertible
full-interval Volterra residual, with no small-time restriction. -/
theorem variablePicard_one_sub_isUnit [CompleteSpace E]
    (A : ContinuousPath (E →L[ℝ] E)) : IsUnit (1-variablePicard A) := by
  obtain ⟨n,hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop ‖A‖
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hs : ‖(variablePicard A)^n‖ < 1 := (variablePicard_pow_norm A n).trans_lt hn
  have hu : IsUnit (1-(variablePicard A)^n) :=
    isUnit_one_sub_of_norm_lt_one (R := ContinuousPath E →L[ℝ] ContinuousPath E) hs
  let S := ∑ i ∈ Finset.range n, (variablePicard A)^i
  have hc : Commute (1-variablePicard A) S := by
    change (1-variablePicard A)*S=S*(1-variablePicard A)
    dsimp [S]
    rw [mul_neg_geom_sum,geom_sum_mul_neg]
  apply (hc.isUnit_mul_iff.mp ?_).1
  dsimp [S]
  rwa [mul_neg_geom_sum]

end
end ThreeSitePhosphorylation
