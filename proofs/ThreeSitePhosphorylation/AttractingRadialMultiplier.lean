import proofs.ThreeSitePhosphorylation.AttractingScaling

namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section
open scoped Topology

/-- The exact branch vector identity and the actual left eigenfunctional
equation put the radial multiplier strictly inside the unit interval.
Source applications must supply these identities and the three base signs. -/
theorem radial_multiplier_eventually_abs_lt_one {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ → E →L[ℝ] E) (v z : ℝ → E) (l : ℝ → E →L[ℝ] ℝ)
    (μ r' : ℝ → ℝ)
    (hv : ContinuousAt v 0) (hz : ContinuousAt z 0)
    (hl : ContinuousAt l 0) (hμ : ContinuousAt μ 0)
    (hμ0 : μ 0=1) (hp0 : 0<l 0 (v 0)) (hn0 : l 0 (z 0)<0)
    (hvec : ∀ᶠ a in 𝓝 (0:ℝ), A a (v a)-v a=(-a*r' a) • z a)
    (hleft : ∀ᶠ a in 𝓝 (0:ℝ), ∀ x, l a (A a x)=μ a*l a x)
    (hr : ∀ᶠ a in 𝓝[>] (0:ℝ), r' a<0) :
    ∀ᶠ a in 𝓝[>] (0:ℝ), |μ a|<1 := by
  have hpos := (hl.clm_apply hv).tendsto.eventually (Ioi_mem_nhds hp0)
  have hneg := (hl.clm_apply hz).tendsto.eventually (Iio_mem_nhds hn0)
  have hlo : ∀ᶠ a in 𝓝 (0:ℝ), -1<μ a :=
    hμ.tendsto.eventually (Ioi_mem_nhds (by rw [hμ0]; norm_num))
  filter_upwards [hvec.filter_mono nhdsWithin_le_nhds,
    hleft.filter_mono nhdsWithin_le_nhds,hpos.filter_mono nhdsWithin_le_nhds,
    hneg.filter_mono nhdsWithin_le_nhds,hlo.filter_mono nhdsWithin_le_nhds,
    hr,self_mem_nhdsWithin] with a ha hla hpa hna hloa hra haa
  have ha0 : 0<a := haa
  have hh := congrArg (l a) ha
  simp only [map_sub,map_smul,smul_eq_mul,hla] at hh
  have hprod : (-a*r' a)*l a (z a)<0 :=
    mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg (by linarith) hra) hna
  have hupper : μ a<1 := by nlinarith
  exact abs_lt.mpr ⟨hloa,hupper⟩

/-- A finite stable complement remains strictly inside the unit interval by
continuity. The exceptional radial branch is handled by the exact identity. -/
theorem all_multipliers_eventually_abs_lt_one {ι : Type*} [Finite ι]
    (i₀ : ι) (μ : ℝ → ι → ℝ)
    (hμ : ∀ i, ContinuousAt (fun a => μ a i) 0)
    (hbase : ∀ i, i ≠ i₀ → |μ 0 i|<1)
    (hrad : ∀ᶠ a in 𝓝[>] (0:ℝ), |μ a i₀|<1) :
    ∀ᶠ a in 𝓝[>] (0:ℝ), ∀ i, |μ a i|<1 := by
  apply Filter.eventually_all.mpr
  intro i
  by_cases hi : i=i₀
  · simpa only [hi] using hrad
  · exact ((hμ i).abs.tendsto.eventually (Iio_mem_nhds (hbase i hi))).filter_mono
      nhdsWithin_le_nhds

end
end ThreeSitePhosphorylation.AttractingWitness
