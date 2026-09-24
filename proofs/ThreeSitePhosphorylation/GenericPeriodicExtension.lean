import Mathlib

/-! Periodic extension in an arbitrary real normed space, including the
actual seam derivative and exact range after rescaling physical time. -/
namespace ThreeSitePhosphorylation.GenericPeriodicExtension
noncomputable section
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def periodicCurve (P : ℝ) (hP : 0 < P) (f : ℝ → E) (s : ℝ) : E :=
  f (toIcoMod hP 0 s)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem periodicCurve_periodic (P : ℝ) (hP : 0 < P) (f : ℝ → E) :
    Function.Periodic (periodicCurve P hP f) P := by
  intro s
  simp only [periodicCurve,toIcoMod_add_right]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem periodicCurve_eq (P : ℝ) (hP : 0 < P) (f : ℝ → E)
    (s : ℝ) (hs : s ∈ Set.Ico 0 P) : periodicCurve P hP f s = f s := by
  unfold periodicCurve
  congr 1
  apply (toIcoMod_eq_iff hP).mpr
  exact ⟨by simpa using hs,0,by simp⟩

theorem periodicCurve_source_zero (P : ℝ) (hP : 0 < P)
    (F : E → E) (f : ℝ → E)
    (he : f 0 = f P) (h0 : HasDerivAt f (F (f 0)) 0)
    (h1 : HasDerivAt f (F (f P)) P) :
    HasDerivAt (periodicCurve P hP f) (F (periodicCurve P hP f 0)) 0 := by
  let g := periodicCurve P hP f
  have hg0 : g 0 = f 0 := periodicCurve_eq P hP f 0 ⟨le_rfl,hP⟩
  have hper := periodicCurve_periodic P hP f
  have hr : HasDerivWithinAt g (F (f 0)) (Set.Ici 0) 0 := by
    apply h0.hasDerivWithinAt.congr_of_eventuallyEq _ hg0
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hP),self_mem_nhdsWithin]
      with s hs hnonneg
    change s < P at hs
    change 0 ≤ s at hnonneg
    exact periodicCurve_eq P hP f s ⟨hnonneg,hs⟩
  have hp : HasDerivAt (fun s => f (s+P)) (F (f 0)) 0 := by
    have hh := h1.scomp_of_eq 0 ((hasDerivAt_id (0:ℝ)).add_const P) (by simp)
    simpa only [id_eq,one_smul,← he] using hh
  have hl : HasDerivWithinAt g (F (f 0)) (Set.Iic 0) 0 := by
    apply hp.hasDerivWithinAt.congr_of_eventuallyEq _ (by simpa only [zero_add] using hg0.trans he)
    have hn : -P < (0:ℝ) := by linarith
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hn),self_mem_nhdsWithin]
      with s hs hnonpos
    change -P < s at hs
    change s ≤ 0 at hnonpos
    by_cases hz : s = 0
    · subst s
      simpa using hg0.trans he
    · have hlt : s < 0 := lt_of_le_of_ne hnonpos hz
      have hin : s+P ∈ Set.Ico 0 P := ⟨by linarith,by linarith⟩
      exact (hper s).symm.trans (periodicCurve_eq P hP f (s+P) hin)
  have hu : Set.Iic (0:ℝ) ∪ Set.Ici 0 = Set.univ := by
    ext s
    simp only [Set.mem_union,Set.mem_Iic,Set.mem_Ici,Set.mem_univ,iff_true]
    exact le_total s 0
  have hh := hl.union hr
  rw [hu,hasDerivWithinAt_univ] at hh
  change HasDerivAt g (F (g 0)) 0
  rw [hg0]
  exact hh

theorem periodicCurve_source (P : ℝ) (hP : 0 < P)
    (F : E → E) (f : ℝ → E)
    (he : f 0 = f P)
    (hf : ∀ s ∈ Set.Icc 0 P, HasDerivAt f (F (f s)) s) :
    ∀ s : ℝ, HasDerivAt (periodicCurve P hP f) (F (periodicCurve P hP f s)) s := by
  let g := periodicCurve P hP f
  have hper := periodicCurve_periodic P hP f
  have hlocal (s : ℝ) (hs : s ∈ Set.Ico 0 P) : HasDerivAt g (F (g s)) s := by
    by_cases hz : s = 0
    · subst s
      exact periodicCurve_source_zero P hP F f he (hf 0 ⟨le_rfl,hP.le⟩) (hf P ⟨hP.le,le_rfl⟩)
    · have hpos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hz)
      have heq : g =ᶠ[𝓝 s] f := by
        filter_upwards [Ioo_mem_nhds hpos hs.2] with t ht
        exact periodicCurve_eq P hP f t ⟨ht.1.le,ht.2⟩
      have hd := (hf s ⟨hs.1,hs.2.le⟩).congr_of_eventuallyEq heq
      rw [show g s = f s from periodicCurve_eq P hP f s hs]
      exact hd
  intro s
  let k := toIcoDiv hP 0 s
  let y := toIcoMod hP 0 s
  have hy : y ∈ Set.Ico 0 P := toIcoMod_mem_Ico' hP s
  have hyq : y = s-k • P := rfl
  have hd := (hlocal y hy).scomp_of_eq s ((hasDerivAt_id s).sub_const (k • P)) hyq
  have hpg : Function.Periodic g P := hper
  have hshift (t : ℝ) : g (t-k • P) = g t := hpg.sub_zsmul_eq k
  change HasDerivAt g (F (g s)) s
  simpa only [id_eq,one_smul,hyq,Function.comp_def,hshift] using hd


omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Globalizing a closed unit-time path and changing to physical time
preserves exactly its image, including the identified endpoint. -/
theorem periodicCurve_physical_range (T : ℝ) (hT : T ≠ 0)
    (f : ℝ → E) (he : f 0=f 1) :
    Set.range (fun t : ℝ => periodicCurve 1 (by norm_num) f (t/T))=
      Set.range (fun t : Set.Icc (0:ℝ) 1 => f t) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨t,rfl⟩
    have hh := toIcoMod_mem_Ico' (show (0:ℝ)<1 by norm_num) (t/T)
    exact ⟨⟨toIcoMod (show (0:ℝ)<1 by norm_num) 0 (t/T),hh.1,hh.2.le⟩,rfl⟩
  · rintro _ ⟨t,rfl⟩
    by_cases ht : (t:ℝ)=1
    · refine ⟨0,?_⟩
      dsimp only
      rw [zero_div,periodicCurve_eq 1 (by norm_num) f 0 (by norm_num),ht]
      exact he
    · refine ⟨(t:ℝ)*T,?_⟩
      dsimp only
      rw [mul_div_cancel_right₀ _ hT]
      exact periodicCurve_eq 1 (by norm_num) f t ⟨t.property.1,lt_of_le_of_ne t.property.2 ht⟩


end
end ThreeSitePhosphorylation.GenericPeriodicExtension
