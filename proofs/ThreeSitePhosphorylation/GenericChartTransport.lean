import proofs.ThreeSitePhosphorylation.GenericWholeOrbit

/-! Transport of reduced-coordinate orbital attraction through an affine
injective compatibility chart `z ↦ e + L z` into full species coordinates.

Premises are the ones a chemical source must PROVE: smoothness of the full
field `F`, the exact conjugacy `F (e + L z) = L (G z)`, injectivity of `L`, and
a positive componentwise margin of the charted orbit. Conclusions: an open set
`O` of full species space containing the charted orbit such that every state of
the compatibility class `e + range L` in `O` has a global forward solution of
`F` that stays in the class, stays componentwise positive, stays in an
ε-tube of the charted orbit, converges to it in distance, and is the unique
forward solution of `F` from that state. -/
namespace ThreeSitePhosphorylation.GenericChartTransport
noncomputable section
open Filter
open scoped Topology

variable {ι S : Type*} [Fintype ι] [Fintype S]

theorem infDist_image_le {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    (Φ : E → F) (K : ℝ) (hK : 0 ≤ K) (hΦ : ∀ x y, dist (Φ x) (Φ y) ≤ K*dist x y)
    (Γ : Set E) (x : E) : Metric.infDist (Φ x) (Φ '' Γ) ≤ K*Metric.infDist x Γ := by
  rcases Γ.eq_empty_or_nonempty with hΓ | hΓ
  · simp [hΓ]
  · apply le_of_forall_pos_lt_add
    intro δ hδ
    have hK1 : 0<K+1 := by linarith
    obtain ⟨y,hy,hxy⟩ := (Metric.infDist_lt_iff hΓ).mp
      (show Metric.infDist x Γ<Metric.infDist x Γ+δ/(K+1) by
        linarith [div_pos hδ hK1])
    calc Metric.infDist (Φ x) (Φ '' Γ) ≤ dist (Φ x) (Φ y) :=
          Metric.infDist_le_dist_of_mem (Set.mem_image_of_mem Φ hy)
      _ ≤ K*dist x y := hΦ x y
      _ ≤ K*(Metric.infDist x Γ+δ/(K+1)) := mul_le_mul_of_nonneg_left hxy.le hK
      _ = K*Metric.infDist x Γ+(K/(K+1))*δ := by ring
      _ < K*Metric.infDist x Γ+δ := by
          have : K/(K+1)<1 := (div_lt_one hK1).mpr (by linarith)
          nlinarith

omit [Fintype ι] in
theorem positive_of_dist_lt_margin (v z : S → ℝ) (m : ℝ)
    (hz : ∀ i, m≤z i) (hv : dist v z< m) : ∀ i, 0<v i := by
  intro i
  have hv' : ‖v-z‖< m := by simpa only [dist_eq_norm] using hv
  have hn := (norm_le_pi_norm (v-z) i).trans_lt hv'
  have hlo := (abs_lt.mp hn).1
  change -m<v i-z i at hlo
  linarith [hz i]

theorem chart_dist_le (e : S → ℝ) (L : (ι → ℝ) →L[ℝ] (S → ℝ)) (x y : ι → ℝ) :
    dist (e+L x) (e+L y) ≤ ‖L‖*dist x y := by
  rw [dist_eq_norm,dist_eq_norm,add_sub_add_left_eq_sub,← map_sub]
  exact L.le_opNorm _

/-- **Chart transport of orbital attraction** into the positive compatibility
class of the full species space. -/
theorem chart_orbital_attraction
    (G : (ι → ℝ) → (ι → ℝ)) (F : (S → ℝ) → (S → ℝ)) (hF : ContDiff ℝ ⊤ F)
    (e : S → ℝ) (L : (ι → ℝ) →L[ℝ] (S → ℝ)) (hL : Function.Injective L)
    (hconj : ∀ z, F (e+L z)=L (G z))
    (Γ : Set (ι → ℝ)) (h : GenericWholeOrbit.OrbitalAttraction G Γ)
    (m : ℝ) (hm : 0< m) (hmargin : ∀ z∈Γ, ∀ i, m≤(e+L z) i) :
    ∀ ε>0, ∃ O : Set (S → ℝ), IsOpen O ∧ (fun z => e+L z) '' Γ ⊆ O ∧
      ∀ z, e+L z∈O → ∃ V : ℝ → (S → ℝ),
        V 0=e+L z ∧
        (∀ t, 0≤t → HasDerivWithinAt V (F (V t)) (Set.Ici 0) t) ∧
        (∀ t, 0≤t → ∃ y, V t=e+L y) ∧
        (∀ t, 0≤t → ∀ i, 0<V t i) ∧
        (∀ t, 0≤t → ∃ y∈Γ, dist (V t) (e+L y)<ε) ∧
        Tendsto (fun t => Metric.infDist (V t) ((fun y => e+L y) '' Γ)) atTop (𝓝 0) ∧
        (∀ W : ℝ → (S → ℝ), W 0=e+L z →
          (∀ t, 0≤t → HasDerivWithinAt W (F (W t)) (Set.Ici 0) t) →
          ∀ t, 0≤t → W t=V t) := by
  intro ε hε
  let Φ : (ι → ℝ) → (S → ℝ) := fun z => e+L z
  have hK : 0 ≤ ‖L‖ := norm_nonneg L
  let ζ := min ε m
  have hζ : 0<ζ := lt_min hε hm
  obtain ⟨U,hU,hΓU,hsol⟩ := h (ζ/(‖L‖+1)) (div_pos hζ (by linarith))
  -- the chart is an embedding, so U is the trace of an open set of species space
  have hemb : Topology.IsEmbedding Φ := by
    have hl : Topology.IsEmbedding L :=
      (LinearMap.isClosedEmbedding_of_injective (f := L.toLinearMap)
        (LinearMap.ker_eq_bot.mpr hL)).isEmbedding
    exact (Homeomorph.addLeft e).isEmbedding.comp hl
  obtain ⟨O,hO,hpre⟩ := hemb.isInducing.isOpen_iff.mp hU
  refine ⟨O,hO,?_,?_⟩
  · rintro _ ⟨z,hz,rfl⟩
    have : z ∈ Φ ⁻¹' O := by rw [hpre]; exact hΓU hz
    exact this
  intro z hzO
  have hzU : z∈U := by rw [← hpre]; exact hzO
  obtain ⟨v,hv0,hvd,hvt,hva,hvu⟩ := hsol z hzU
  have hfield (y : ι → ℝ) : F (Φ y)=L (G y) := hconj y
  have htube : ∀ t, 0≤t → ∃ y∈Γ, dist (Φ (v t)) (Φ y)<ζ := by
    intro t ht
    obtain ⟨y,hy,hyt⟩ := hvt t ht
    refine ⟨y,hy,(chart_dist_le e L _ _).trans_lt ?_⟩
    have hh := (lt_div_iff₀ (show 0<‖L‖+1 by linarith)).mp hyt
    have hd := dist_nonneg (x := v t) (y := y)
    nlinarith
  refine ⟨fun t => Φ (v t),by simp only [Φ,hv0],?_,?_,?_,?_,?_,?_⟩
  · intro t ht
    have hh := (L.hasFDerivAt.comp_hasDerivWithinAt t (hvd t ht)).const_add e
    rw [hfield]
    exact hh
  · intro t _
    exact ⟨v t,rfl⟩
  · intro t ht
    obtain ⟨y,hy,hyt⟩ := htube t ht
    exact positive_of_dist_lt_margin _ _ m (hmargin y hy) (hyt.trans_le (min_le_right _ _))
  · intro t ht
    obtain ⟨y,hy,hyt⟩ := htube t ht
    exact ⟨y,hy,hyt.trans_le (min_le_left _ _)⟩
  · have hb : ∀ t, Metric.infDist (Φ (v t)) (Φ '' Γ) ≤ ‖L‖*Metric.infDist (v t) Γ :=
      fun t => infDist_image_le Φ ‖L‖ hK (fun x y => chart_dist_le e L x y) Γ (v t)
    have hz : Tendsto (fun t => ‖L‖*Metric.infDist (v t) Γ) atTop (𝓝 0) := by
      simpa using hva.const_mul ‖L‖
    exact squeeze_zero (fun _ => Metric.infDist_nonneg) hb hz
  · intro W hW0 hWd t ht
    have hVd : ∀ s, 0 ≤ s → HasDerivWithinAt (fun s => Φ (v s)) (F (Φ (v s))) (Set.Ici 0) s := by
      intro s hs
      have hh := (L.hasFDerivAt.comp_hasDerivWithinAt s (hvd s hs)).const_add e
      rw [hfield]
      exact hh
    exact SmoothForwardUniqueness.forward_unique F hF W (fun s => Φ (v s)) hWd hVd
      (by simp only [Φ,hW0,hv0]) t ht

/-- The charted periodic solution is a positive, class-preserving, nonconstant
periodic solution of the full field. -/
theorem chart_periodic_orbit
    (G : (ι → ℝ) → (ι → ℝ)) (F : (S → ℝ) → (S → ℝ))
    (e : S → ℝ) (L : (ι → ℝ) →L[ℝ] (S → ℝ)) (hL : Function.Injective L)
    (hconj : ∀ z, F (e+L z)=L (G z))
    (γ : ℝ → (ι → ℝ)) (T : ℝ) (hper : Function.Periodic γ T)
    (hγ : ∀ t, HasDerivAt γ (G (γ t)) t) (hnc : ∃ t, γ t ≠ γ 0)
    (m : ℝ) (hm : 0< m) (hmargin : ∀ t, ∀ i, m≤(e+L (γ t)) i) :
    Function.Periodic (fun t => e+L (γ t)) T ∧
    (∀ t, HasDerivAt (fun t => e+L (γ t)) (F (e+L (γ t))) t) ∧
    (∃ t, e+L (γ t) ≠ e+L (γ 0)) ∧
    (∀ t i, 0<(e+L (γ t)) i) := by
  refine ⟨fun t => by simp only [hper t],?_,?_,?_⟩
  · intro t
    rw [hconj]
    exact (L.hasFDerivAt.comp_hasDerivAt t (hγ t)).const_add e
  · obtain ⟨t,ht⟩ := hnc
    exact ⟨t,fun h => ht (hL (add_left_cancel h))⟩
  · intro t i
    exact lt_of_lt_of_le hm (hmargin t i)

end
end ThreeSitePhosphorylation.GenericChartTransport
