import proofs.ThreeSitePhosphorylation.NonZenoReturns
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Joining source arcs over a non-Zeno partition. The source equations for
the individual arcs are explicit inputs; no phosphorylation result is assumed. -/
namespace ThreeSitePhosphorylation.ReturnArcConcatenation
noncomputable section
open Filter
open scoped Topology
open NonZenoReturns

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
def curve (τ : ℕ → ℝ) (c : ℝ) (hc : 0<c) (hτ : ∀ n, c≤τ n)
    (f : ℕ → ℝ → E) (t : ℝ) : E := f (count τ c hc hτ t) t

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem curve_eq_on_interval (τ : ℕ → ℝ) (c : ℝ) (hc : 0<c)
    (hτ : ∀ n, c≤τ n) (f : ℕ → ℝ → E)
    (hjoin : ∀ n, f (n+1) (elapsed τ (n+1))=f n (elapsed τ (n+1)))
    (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (elapsed τ n) (elapsed τ (n+1))) :
    curve τ c hc hτ f t=f n t := by
  by_cases he : t=elapsed τ (n+1)
  · subst t
    have hn := elapsed_strictMono τ c hc hτ (Nat.lt_succ_self (n+1))
    rw [curve,count_eq_of_mem τ c hc hτ _ (n+1) le_rfl hn]
    exact hjoin n
  · rw [curve,count_eq_of_mem τ c hc hτ t n ht.1 (lt_of_le_of_ne ht.2 he)]

/-- Matched endpoint values and the same autonomous equation make the seam
derivatives agree. The resulting curve is a forward solution, including a
right derivative at its initial time. -/
theorem curve_source (τ : ℕ → ℝ) (c : ℝ) (hc : 0<c)
    (hτ : ∀ n, c≤τ n) (f : ℕ → ℝ → E) (F : E → E)
    (hjoin : ∀ n, f (n+1) (elapsed τ (n+1))=f n (elapsed τ (n+1)))
    (hf : ∀ n t, t ∈ Set.Icc (elapsed τ n) (elapsed τ (n+1)) →
      HasDerivWithinAt (f n) (F (f n t))
        (Set.Icc (elapsed τ n) (elapsed τ (n+1))) t) :
    ∀ t, 0≤t → HasDerivWithinAt (curve τ c hc hτ f)
      (F (curve τ c hc hτ f t)) (Set.Ici 0) t := by
  let g := curve τ c hc hτ f
  have heq := curve_eq_on_interval τ c hc hτ f hjoin
  have hmono := elapsed_strictMono τ c hc hτ
  have hd (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (elapsed τ n) (elapsed τ (n+1))) :
      HasDerivWithinAt g (F (g t))
        (Set.Icc (elapsed τ n) (elapsed τ (n+1))) t := by
    rw [show g t=f n t from heq n t ht]
    apply (hf n t ht).congr_of_eventuallyEq _ (heq n t ht)
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact heq n s hs
  intro t ht
  let n := count τ c hc hτ t
  have hlo : elapsed τ n≤t := count_lower τ c hc hτ t ht
  have hup : t<elapsed τ (n+1) := count_upper τ c hc hτ t
  by_cases he : t=elapsed τ n
  · have hr : HasDerivWithinAt g (F (g t)) (Set.Ici t) t := by
      apply (hd n t ⟨hlo,hup.le⟩).mono_of_mem_nhdsWithin
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hup),
        self_mem_nhdsWithin] with s hs hs'
      exact ⟨he ▸ hs',hs.le⟩
    cases hn : n with
    | zero =>
      have ht0 : t=0 := by simpa [hn] using he
      simpa only [ht0] using hr
    | succ m =>
      have hlow : elapsed τ m<t := by rw [he,hn]; exact hmono (Nat.lt_succ_self m)
      have htend : t=elapsed τ (m+1) := by simpa only [hn] using he
      have hl : HasDerivWithinAt g (F (g t)) (Set.Iic t) t := by
        apply (hd m t ⟨hlow.le,htend.le⟩).mono_of_mem_nhdsWithin
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hlow),
          self_mem_nhdsWithin] with s hs hs'
        exact ⟨hs.le,hs'.trans htend.le⟩
      have hu : Set.Iic t ∪ Set.Ici t = Set.univ := by
        ext s
        simp only [Set.mem_union,Set.mem_Iic,Set.mem_Ici,Set.mem_univ,iff_true]
        exact le_total s t
      have hh := hl.union hr
      rw [hu,hasDerivWithinAt_univ] at hh
      exact hh.hasDerivWithinAt
  · have hlow : elapsed τ n<t := lt_of_le_of_ne hlo (Ne.symm he)
    exact ((hd n t ⟨hlo,hup.le⟩).hasDerivAt (Icc_mem_nhds hlow hup)).hasDerivWithinAt

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem curve_initial (τ : ℕ → ℝ) (c : ℝ) (hc : 0<c)
    (hτ : ∀ n, c≤τ n) (f : ℕ → ℝ → E) :
    curve τ c hc hτ f 0=f 0 0 := by
  have hh : 0<elapsed τ (0+1) := by
    simpa using elapsed_strictMono τ c hc hτ (Nat.lt_succ_self 0)
  rw [curve,count_eq_of_mem τ c hc hτ 0 0 (by simp) hh]

end
end ThreeSitePhosphorylation.ReturnArcConcatenation
