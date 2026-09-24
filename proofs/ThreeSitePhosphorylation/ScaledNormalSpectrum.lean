import proofs.ThreeSitePhosphorylation.AddedSite
import Mathlib

/-! A uniform scale separating the three actual added-site normal roots
from any finite parent list. This does not construct a full source basis. -/
namespace ThreeSitePhosphorylation.ScaledNormalSpectrum
noncomputable section
set_option maxHeartbeats 500000

def scaledBlock (κ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (κ:ℂ) • AddedSite.limitingBlock

def normalRoots (κ : ℝ) : Fin 3 → ℝ :=
  ![-κ*(3+Real.sqrt 5)/2,-2*κ,-κ*(3-Real.sqrt 5)/2]

theorem scaled_characteristic (κ : ℝ) (z : ℂ) :
    Matrix.det (z • (1 : Matrix (Fin 3) (Fin 3) ℂ)-scaledBlock κ)=
      (z+2*(κ:ℂ))*(z^2+3*(κ:ℂ)*z+(κ:ℂ)^2) := by
  simp [scaledBlock,AddedSite.limitingBlock,Matrix.det_fin_three,
    Matrix.sub_apply,Matrix.smul_apply]
  ring

theorem scaled_characteristic_factors (κ : ℝ) (z : ℂ) :
    Matrix.det (z • (1 : Matrix (Fin 3) (Fin 3) ℂ)-scaledBlock κ)=
      (z-(normalRoots κ 1:ℂ))*(z-(normalRoots κ 0:ℂ))*(z-(normalRoots κ 2:ℂ)) := by
  have hs : ((Real.sqrt 5:ℝ):ℂ)^2=5 := by
    exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤5 by norm_num)
  have hq : z^2+3*(κ:ℂ)*z+(κ:ℂ)^2=
      (z+(κ:ℂ)*(3+(Real.sqrt 5:ℂ))/2)*(z+(κ:ℂ)*(3-(Real.sqrt 5:ℂ))/2) := by
    linear_combination (κ:ℂ)^2/4*hs
  rw [scaled_characteristic,hq]
  simp [normalRoots]
  ring

theorem scaled_characteristic_zero_iff (κ : ℝ) (z : ℂ) :
    Matrix.det (z • (1 : Matrix (Fin 3) (Fin 3) ℂ)-scaledBlock κ)=0 ↔
      ∃ i : Fin 3, z=(normalRoots κ i:ℂ) := by
  rw [scaled_characteristic_factors]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact ⟨1,sub_eq_zero.mp h⟩
      · exact ⟨0,sub_eq_zero.mp h⟩
    · exact ⟨2,sub_eq_zero.mp h⟩
  · rintro ⟨i,hi⟩
    fin_cases i <;> rw [hi] <;> simp

theorem normalRoots_order (κ : ℝ) (hκ : 0<κ) :
    normalRoots κ 0<normalRoots κ 1 ∧ normalRoots κ 1<normalRoots κ 2 ∧
      normalRoots κ 2< -κ/3 := by
  have hs0 : 0≤Real.sqrt (5:ℝ) := Real.sqrt_nonneg _
  have hs : (Real.sqrt (5:ℝ))^2=5 := Real.sq_sqrt (by norm_num)
  have hs1 : 1<Real.sqrt (5:ℝ) := by nlinarith
  have hs2 : Real.sqrt (5:ℝ)<7/3 := by nlinarith
  have h1 := mul_pos hκ (sub_pos.mpr hs1)
  have h2 := mul_pos hκ (sub_pos.mpr hs2)
  change -κ*(3+Real.sqrt 5)/2 < -2*κ ∧
    -2*κ < -κ*(3-Real.sqrt 5)/2 ∧ -κ*(3-Real.sqrt 5)/2 < -κ/3
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem normalRoots_negative (κ : ℝ) (hκ : 0<κ) (i : Fin 3) : normalRoots κ i<0 := by
  obtain ⟨h01,h12,h2⟩ := normalRoots_order κ hκ
  have hz : -κ/3<0 := by linarith
  fin_cases i
  · exact h01.trans (h12.trans (h2.trans hz))
  · exact h12.trans (h2.trans hz)
  · exact h2.trans hz

theorem normalRoots_injective (κ : ℝ) (hκ : 0<κ) : Function.Injective (normalRoots κ) := by
  obtain ⟨h01,h12,_⟩ := normalRoots_order κ hκ
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | exact (h01.ne hij).elim
    | exact (h01.ne hij.symm).elim
    | exact (h12.ne hij).elim
    | exact (h12.ne hij.symm).elim
    | exact ((h01.trans h12).ne hij).elim
    | exact ((h01.trans h12).ne hij.symm).elim

def separatingScale {ι : Type*} [Fintype ι] (roots : ι → ℝ) : ℝ := 3*(‖roots‖+1)

theorem separatingScale_positive {ι : Type*} [Fintype ι] (roots : ι → ℝ) :
    0<separatingScale roots := by
  unfold separatingScale
  positivity

/-- All normal roots lie strictly below every parent entry. Parent negativity
is not needed; the sup norm also covers unordered and empty finite lists. -/
theorem normalRoots_below_parent {ι : Type*} [Fintype ι]
    (roots : ι → ℝ) (i : Fin 3) (j : ι) :
    normalRoots (separatingScale roots) i<roots j := by
  let κ := separatingScale roots
  have hκ : 0<κ := separatingScale_positive roots
  obtain ⟨h01,h12,h2⟩ := normalRoots_order κ hκ
  have hb : -‖roots‖≤roots j := by
    have hh := norm_le_pi_norm roots j
    rw [Real.norm_eq_abs] at hh
    exact (abs_le.mp hh).1
  have hs : -κ/3<roots j := by
    dsimp [κ,separatingScale]
    linarith
  fin_cases i
  · exact h01.trans (h12.trans (h2.trans hs))
  · exact h12.trans (h2.trans hs)
  · exact h2.trans hs

theorem normalRoots_ne_parent {ι : Type*} [Fintype ι]
    (roots : ι → ℝ) (i : Fin 3) (j : ι) :
    normalRoots (separatingScale roots) i ≠ roots j :=
  ne_of_lt (normalRoots_below_parent roots i j)

end
end ThreeSitePhosphorylation.ScaledNormalSpectrum
