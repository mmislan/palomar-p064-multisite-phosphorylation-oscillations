import Mathlib

/-! Full-interval linear Picard operator. The factorial estimate follows the
argument in Mathlib's PicardLindelof, on an unconstrained continuous path space.
This is intended for the derivative of the amplitude-rescaled shooting residual. -/
namespace ThreeSitePhosphorylation
noncomputable section
open scoped BigOperators
open MeasureTheory
set_option maxHeartbeats 200000

abbrev UnitTime := Set.Icc (0:ℝ) 1
abbrev ContinuousPath (E : Type*) [TopologicalSpace E] := C(UnitTime,E)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def pathExtension (u : ContinuousPath E) : ℝ → E :=
  fun t => u (Set.projIcc 0 1 (by norm_num) t)

omit [NormedSpace ℝ E] in
theorem pathExtension_continuous (u : ContinuousPath E) : Continuous (pathExtension u) :=
  u.continuous.comp continuous_projIcc

def linearPicardPath (A : E →L[ℝ] E) (u : ContinuousPath E) : ContinuousPath E :=
  ⟨fun t => ∫ s in (0:ℝ)..(t:ℝ), A (pathExtension u s),
    (intervalIntegral.continuous_primitive
      (fun _ _ => (A.continuous.comp (pathExtension_continuous u)).intervalIntegrable _ _) 0).comp
      continuous_subtype_val⟩

theorem linearPicardPath_bound (A : E →L[ℝ] E) (u : ContinuousPath E) :
    ‖linearPicardPath A u‖ ≤ ‖A‖*‖u‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := (t:ℝ)) (C := ‖A‖*‖u‖) (f := fun s => A (pathExtension u s))
    (fun s _ => (A.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm u _) (norm_nonneg A)))
  have ht : |(t:ℝ)| ≤ 1 := by rw [abs_of_nonneg t.2.1]; exact t.2.2
  change ‖∫ s in (0:ℝ)..(t:ℝ), A (pathExtension u s)‖ ≤ _
  apply hb.trans
  calc
    ‖A‖*‖u‖*|(t:ℝ)-0| ≤ ‖A‖*‖u‖*1 :=
      mul_le_mul_of_nonneg_left (by simpa only [sub_zero] using ht) (by positivity)
    _ = _ := mul_one _

def linearPicardLinear (A : E →L[ℝ] E) : ContinuousPath E →ₗ[ℝ] ContinuousPath E where
  toFun := linearPicardPath A
  map_add' u v := by
    ext t
    change (∫ s in (0:ℝ)..(t:ℝ), A (pathExtension (u+v) s)) = _
    simp only [pathExtension,ContinuousMap.add_apply,map_add]
    exact intervalIntegral.integral_add
      ((A.continuous.comp (pathExtension_continuous u)).intervalIntegrable _ _)
      ((A.continuous.comp (pathExtension_continuous v)).intervalIntegrable _ _)
  map_smul' c u := by
    ext t
    change (∫ s in (0:ℝ)..(t:ℝ), A (pathExtension (c • u) s)) = _
    simp only [pathExtension,ContinuousMap.smul_apply,map_smul]
    exact intervalIntegral.integral_smul c _

def linearPicard (A : E →L[ℝ] E) : ContinuousPath E →L[ℝ] ContinuousPath E :=
  (linearPicardLinear A).mkContinuous ‖A‖ (linearPicardPath_bound A)

theorem linearPicard_pow_bound (A : E →L[ℝ] E) (u : ContinuousPath E)
    (n : ℕ) (t : UnitTime) :
    ‖(((linearPicard A)^n) u) t‖ ≤ ‖A‖^n*(t:ℝ)^n/(n.factorial:ℝ)*‖u‖ := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.norm_coe_le_norm u t
  | succ n hn =>
    have he : (((linearPicard A)^(n+1)) u) t =
        ∫ s in (0:ℝ)..(t:ℝ), A (pathExtension (((linearPicard A)^n) u) s) := by
      rw [pow_succ']
      rfl
    rw [he]
    calc
      _ ≤ ∫ s in (0:ℝ)..(t:ℝ), ‖A‖^(n+1)*s^n/(n.factorial:ℝ)*‖u‖ := by
        apply intervalIntegral.norm_integral_le_of_norm_le t.2.1
        · apply Filter.Eventually.of_forall
          intro s hs
          have hs' : s ∈ Set.Icc (0:ℝ) 1 := ⟨hs.1.le,hs.2.trans t.2.2⟩
          simp only [pathExtension,Set.projIcc_of_mem _ hs']
          calc
            _ ≤ ‖A‖*‖(((linearPicard A)^n) u) ⟨s,hs'⟩‖ := A.le_opNorm _
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

theorem linearPicard_pow_norm (A : E →L[ℝ] E) (n : ℕ) :
    ‖(linearPicard A)^n‖ ≤ ‖A‖^n/(n.factorial:ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  calc
    _ ≤ ‖A‖^n*(t:ℝ)^n/(n.factorial:ℝ)*‖u‖ := linearPicard_pow_bound A u n t
    _ ≤ ‖A‖^n*1/(n.factorial:ℝ)*‖u‖ := by
      gcongr
      exact pow_le_one₀ t.2.1 t.2.2
    _ = _ := by ring

/-- The full-interval linear Picard residual is invertible, with no small-time
assumption. This is an analytic fact; no Picard iteration is executed. -/
theorem linearPicard_one_sub_isUnit [CompleteSpace E] (A : E →L[ℝ] E) :
    IsUnit (1-linearPicard A) := by
  obtain ⟨n,hn⟩ := FloorSemiring.tendsto_pow_div_factorial_atTop ‖A‖
    |>.eventually (gt_mem_nhds zero_lt_one) |>.exists
  have hs : ‖(linearPicard A)^n‖ < 1 := (linearPicard_pow_norm A n).trans_lt hn
  have hu : IsUnit (1-(linearPicard A)^n) :=
    isUnit_one_sub_of_norm_lt_one (R := ContinuousPath E →L[ℝ] ContinuousPath E) hs
  let S := ∑ i ∈ Finset.range n, (linearPicard A)^i
  have hc : Commute (1-linearPicard A) S := by
    change (1-linearPicard A)*S=S*(1-linearPicard A)
    dsimp [S]
    rw [mul_neg_geom_sum,geom_sum_mul_neg]
  apply (hc.isUnit_mul_iff.mp ?_).1
  dsimp [S]
  rwa [mul_neg_geom_sum]

end
end ThreeSitePhosphorylation
