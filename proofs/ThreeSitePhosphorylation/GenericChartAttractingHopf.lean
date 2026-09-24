import proofs.ThreeSitePhosphorylation.GenericAttractingHopf
import proofs.ThreeSitePhosphorylation.GenericChartTransport

/-! Full-species form of the dimension-independent attracting Hopf family.

In addition to the reduced source data of `attracting_hopf_family`, the chemical
source must supply: a full field `F r` smooth for every kinetic parameter, a
componentwise positive parameter-independent equilibrium `e`, an injective linear
compatibility chart `L`, and the exact conjugacy
`F r (e + L z) = L ((A0+rD)z + Q_r(z))`. The positive margin of the orbits is
DERIVED from uniform shrinking; it is not an input. -/
namespace ThreeSitePhosphorylation.GenericChartAttractingHopf
noncomputable section
open Filter
open scoped Topology Pointwise
open GenericClosedPaths GenericAttractingFamily

variable {ι σ S : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype S]

omit [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ] in
theorem exists_positive_lower (e : S → ℝ) (he : ∀ i, 0<e i) : ∃ c>0, ∀ i, c ≤ e i := by
  rcases isEmpty_or_nonempty S with hS | hS
  · exact ⟨1,one_pos,fun i => (IsEmpty.false i).elim⟩
  · obtain ⟨i0,-,hi0⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
    exact ⟨e i0,he i0,fun i => hi0 i (Finset.mem_univ i)⟩

omit [DecidableEq ι] [Fintype σ] [DecidableEq σ] in
theorem chart_component_lower (e : S → ℝ) (L : (ι → ℝ) →L[ℝ] (S → ℝ)) (c : ℝ)
    (hc : ∀ i, c ≤ e i) (y : ι → ℝ) (hy : ‖L‖*‖y‖ ≤ c/2) : ∀ i, c/2 ≤ (e+L y) i := by
  intro i
  have h1 := norm_le_pi_norm (L y) i
  have h2 := L.le_opNorm y
  have h3 := (abs_le.mp (Real.norm_eq_abs (L y i) ▸ h1.trans h2)).1
  change c/2 ≤ e i+L y i
  linarith [hc i]

/-- **Full-species dimension-independent attracting Hopf family.** -/
theorem chart_attracting_hopf_family
    (A0 D : Matrix ι ι ℝ) (K : ℝ → GenericQuadraticTensor.Tensor ι)
    (hK : ∀ i j k, ContDiff ℝ ⊤ (fun s => K s i j k))
    (r w : ℝ) (hw : 0<w) (roots : σ → ℝ) (hinj : Function.Injective roots)
    (hn : ∀ i, roots i<0) (b : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ))
    (hreal : ∀ i : σ, GenericComplexification.conjugateVector (b (Sum.inl i))=b (Sum.inl i))
    (hpair : b (Sum.inr 1)=GenericComplexification.conjugateVector (b (Sum.inr 0)))
    (he : ∀ i, (GenericComplexification.complexMatrix (A0+r • D)).mulVec (b i)=
      GenericPeriodicKernel.spectralValues roots w i • b i)
    (hcross : (b.coord (Sum.inr 0)
      ((GenericComplexification.complexMatrix D).mulVec (b (Sum.inr 0)))).re<0)
    (hsym : ∀ i j k, K r i j k=K r i k j)
    (hA : Function.Injective (GenericComplexification.complexMatrix (A0+r • D)).mulVecLin)
    (hS : Function.Injective ((2*Complex.I*(w:ℂ)) •
      (LinearMap.id : (ι → ℂ) →ₗ[ℂ] (ι → ℂ))-
        (GenericComplexification.complexMatrix (A0+r • D)).mulVecLin))
    (h11 h20 : ι → ℂ)
    (h11eq : (GenericComplexification.complexMatrix (A0+r • D)).mulVec h11=
      GenericTensorBilinear.complexBilinear (K r) (b (Sum.inr 0))
        (GenericComplexification.conjugateVector (b (Sum.inr 0))))
    (h20eq : (2*Complex.I*(w:ℂ)) • h20-
      (GenericComplexification.complexMatrix (A0+r • D)).mulVec h20=
        GenericTensorBilinear.complexBilinear (K r) (b (Sum.inr 0)) (b (Sum.inr 0)))
    (hG : (-2*b.coord (Sum.inr 0) (GenericTensorBilinear.complexBilinear (K r)
        (b (Sum.inr 0)) h11)+
      b.coord (Sum.inr 0) (GenericTensorBilinear.complexBilinear (K r)
        (GenericComplexification.conjugateVector (b (Sum.inr 0))) h20)).re<0)
    (F : ℝ → (S → ℝ) → (S → ℝ)) (hF : ∀ s, ContDiff ℝ ⊤ (F s))
    (e : S → ℝ) (hepos : ∀ i, 0<e i)
    (L : (ι → ℝ) →L[ℝ] (S → ℝ)) (hL : Function.Injective L)
    (hconj : ∀ s z, F s (e+L z)=L (GenericQuadraticDynamics.field A0 D K s z)) :
    ∃ C : ClosedPathFamily A0 D (GenericQuadraticTensor.pathField K) r w (b (Sum.inr 0)),
      Tendsto (fun a => (C.parameters a).2.re) (𝓝 0) (𝓝 r) ∧
      Tendsto (fun a => (C.parameters a).2.im) (𝓝 0) (𝓝 (2*Real.pi/w)) ∧
      (∀ ε>0, ∀ᶠ a in 𝓝 (0:ℝ), ∀ t, dist (e+L (periodicOrbit C a t)) e<ε) ∧
      ∀ᶠ a in 𝓝[>] (0:ℝ),
        (C.parameters a).2.re<r ∧ 0<(C.parameters a).2.im ∧
        Function.Periodic (fun t => e+L (periodicOrbit C a t)) (C.parameters a).2.im ∧
        (∀ t, HasDerivAt (fun t => e+L (periodicOrbit C a t))
          (F (C.parameters a).2.re (e+L (periodicOrbit C a t))) t) ∧
        (∃ t, e+L (periodicOrbit C a t) ≠ e+L (periodicOrbit C a 0)) ∧
        (∀ t i, 0<(e+L (periodicOrbit C a t)) i) ∧
        ∀ ε>0, ∃ O : Set (S → ℝ), IsOpen O ∧
          (fun z => e+L z) '' Set.range (periodicOrbit C a) ⊆ O ∧
          ∀ z, e+L z∈O → ∃ V : ℝ → (S → ℝ),
            V 0=e+L z ∧
            (∀ t, 0≤t → HasDerivWithinAt V (F (C.parameters a).2.re (V t)) (Set.Ici 0) t) ∧
            (∀ t, 0≤t → ∃ y, V t=e+L y) ∧
            (∀ t, 0≤t → ∀ i, 0<V t i) ∧
            (∀ t, 0≤t → ∃ y∈Set.range (periodicOrbit C a), dist (V t) (e+L y)<ε) ∧
            Tendsto (fun t => Metric.infDist (V t)
              ((fun y => e+L y) '' Set.range (periodicOrbit C a))) atTop (𝓝 0) ∧
            (∀ W : ℝ → (S → ℝ), W 0=e+L z →
              (∀ t, 0≤t → HasDerivWithinAt W (F (C.parameters a).2.re (W t)) (Set.Ici 0) t) →
              ∀ t, 0≤t → W t=V t) := by
  obtain ⟨C,hr,hT,hshrink,hfam⟩ := GenericAttractingHopf.attracting_hopf_family A0 D K hK r w hw
    roots hinj hn b hreal hpair he hcross hsym hA hS h11 h20 h11eq h20eq hG
  obtain ⟨c,hc,hce⟩ := exists_positive_lower e hepos
  have hL1 : 0<‖L‖+1 := by positivity
  have hmargin : ∀ᶠ a in 𝓝 (0:ℝ), ∀ t i, c/2 ≤ (e+L (periodicOrbit C a t)) i := by
    filter_upwards [hshrink ((c/2)/(‖L‖+1)) (div_pos (half_pos hc) hL1)] with a ha t
    apply chart_component_lower e L c hce
    have hh := ha t
    have hb : ‖L‖*‖periodicOrbit C a t‖ ≤ (‖L‖+1)*‖periodicOrbit C a t‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    have hh' := (lt_div_iff₀ hL1).mp hh
    nlinarith [norm_nonneg (periodicOrbit C a t)]
  refine ⟨C,hr,hT,?_,?_⟩
  · intro ε hε
    filter_upwards [hshrink (ε/(‖L‖+1)) (div_pos hε hL1)] with a ha t
    rw [dist_eq_norm,add_sub_cancel_left]
    calc ‖L (periodicOrbit C a t)‖ ≤ ‖L‖*‖periodicOrbit C a t‖ := L.le_opNorm _
      _ ≤ (‖L‖+1)*‖periodicOrbit C a t‖ :=
          mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (‖L‖+1)*(ε/(‖L‖+1)) := mul_lt_mul_of_pos_left (ha t) hL1
      _ = ε := by field_simp
  · filter_upwards [hfam,hmargin.filter_mono nhdsWithin_le_nhds] with a ha hm
    obtain ⟨hbelow,hTa,hper,hdyn,hnc,hattr⟩ := ha
    obtain ⟨hper',hdyn',hnc',hpos'⟩ := GenericChartTransport.chart_periodic_orbit
      (GenericQuadraticDynamics.field A0 D K (C.parameters a).2.re) (F (C.parameters a).2.re)
      e L hL (hconj _) (periodicOrbit C a) _ hper hdyn hnc (c/2) (half_pos hc) hm
    refine ⟨hbelow,hTa,hper',hdyn',hnc',hpos',?_⟩
    apply GenericChartTransport.chart_orbital_attraction
      (GenericQuadraticDynamics.field A0 D K (C.parameters a).2.re) (F (C.parameters a).2.re)
      (hF _) e L hL (hconj _) _ hattr (c/2) (half_pos hc)
    rintro _ ⟨t,rfl⟩
    exact hm t

end
end ThreeSitePhosphorylation.GenericChartAttractingHopf
