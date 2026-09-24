import proofs.ThreeSitePhosphorylation.AllSiteHopfInvariant
import proofs.ThreeSitePhosphorylation.GenericChartAttractingHopf

/-! Attracting Hopf families of the literal sequential distributive phosphorylation
cycle for every number of sites `n ≥ 3`.

The full species state `S_0..S_n, E, F, C_0..C_{n-1}, D_0..D_{n-1}` is written as a
real vector (`speciesVec`), and the literal mass-action field as `speciesField`.
The compatibility class of a positive equilibrium is the image of the injective
linear chart `chartLinear` (the zero-total tangent reconstruction of the reduced
coordinates); the literal field is exactly conjugate on it to the affine quadratic
source field `(A0+rD)z+Q_r(z)`. Each `AddedSiteHopfStep.HopfInvariant` therefore
supplies every input of `GenericChartAttractingHopf.chart_attracting_hopf_family`,
with genuine resolvents; `AllSiteHopfInvariant.all_site_hopf_invariant` supplies the
invariant for every `n ≥ 3`. -/
namespace ThreeSitePhosphorylation.AllSiteAttractingFamily
noncomputable section
open Filter
open scoped Topology
open MultisiteCoordinates MultisiteTensor CriticalSpectrum AddedSiteSpectralStep
open AddedSiteHopfStep ScaledAffineFamily GenericComplexification GenericTensorBilinear
open AddedSiteCoefficientContinuity AddedSiteCoefficientTransport
set_option maxHeartbeats 800000

/-! ### Full species vectors -/

/-- Literal species index: `S_0..S_n`, then `E,F`, then `C_0..C_{n-1}`, `D_0..D_{n-1}`. -/
abbrev Species (n : ℕ) := Fin (n+1) ⊕ (Fin 2 ⊕ (Fin n ⊕ Fin n))

def speciesVec {n : ℕ} (x : PhosphorylationSharpness.State n) : Species n → ℝ :=
  Sum.elim x.S (Sum.elim ![x.E,x.F] (Sum.elim x.C x.D))

def ofSpecies {n : ℕ} (v : Species n → ℝ) : PhosphorylationSharpness.State n where
  S i := v (Sum.inl i)
  E := v (Sum.inr (Sum.inl 0))
  F := v (Sum.inr (Sum.inl 1))
  C i := v (Sum.inr (Sum.inr (Sum.inl i)))
  D i := v (Sum.inr (Sum.inr (Sum.inr i)))

theorem ofSpecies_speciesVec {n : ℕ} (x : PhosphorylationSharpness.State n) :
    ofSpecies (speciesVec x)=x := by
  cases x
  rfl

theorem speciesVec_ofSpecies {n : ℕ} (v : Species n → ℝ) : speciesVec (ofSpecies v)=v := by
  funext i
  rcases i with i | (i | (i | i))
  · rfl
  · fin_cases i <;> rfl
  · rfl
  · rfl

/-- The literal mass-action field on full species vectors. -/
def speciesField {n : ℕ} (k : PhosphorylationSharpness.Rates n) (v : Species n → ℝ) :
    Species n → ℝ :=
  speciesVec (PhosphorylationSharpness.field k (ofSpecies v))

/-- The three conserved totals of a full state agree with those of `x`. -/
def SameTotals {n : ℕ} (y x : PhosphorylationSharpness.State n) : Prop :=
  PhosphorylationSharpness.totalE y=PhosphorylationSharpness.totalE x ∧
    PhosphorylationSharpness.totalF y=PhosphorylationSharpness.totalF x ∧
    PhosphorylationSharpness.totalS y=PhosphorylationSharpness.totalS x

theorem speciesVec_positive {n : ℕ} (x : PhosphorylationSharpness.State n) (hx : x.Positive) :
    ∀ i, 0<speciesVec x i := by
  intro i
  rcases i with i | (i | (i | i))
  · exact hx.1 i
  · fin_cases i
    · exact hx.2.1
    · exact hx.2.2.1
  · exact hx.2.2.2.1 i
  · exact hx.2.2.2.2 i

theorem speciesField_smooth {n : ℕ} (k : PhosphorylationSharpness.Rates n) :
    ContDiff ℝ ⊤ (speciesField k) := by
  have hk : MultisiteSmoothField.RatesSmooth (fun _ : Species n → ℝ => k) :=
    ⟨fun _ => contDiff_const,fun _ => contDiff_const,fun _ => contDiff_const,
      fun _ => contDiff_const,fun _ => contDiff_const,fun _ => contDiff_const⟩
  have hx : MultisiteSmoothField.StateSmooth (fun v : Species n → ℝ => ofSpecies v) :=
    ⟨fun _ => contDiff_apply ℝ ℝ _,contDiff_apply ℝ ℝ _,contDiff_apply ℝ ℝ _,
      fun _ => contDiff_apply ℝ ℝ _,fun _ => contDiff_apply ℝ ℝ _⟩
  obtain ⟨hS,hE,hF,hC,hD⟩ := MultisiteSmoothField.field_smooth_components _ _ hk hx
  apply contDiff_pi.mpr
  intro i
  rcases i with i | (i | (i | i))
  · exact hS i
  · fin_cases i
    · exact hE
    · exact hF
  · exact hC i
  · exact hD i

/-! ### The compatibility chart -/

theorem speciesVec_tangent_add_smul {n : ℕ} (u v : MultisiteChart.ReducedState n) (t : ℝ) :
    speciesVec (MultisiteChart.tangent (u+t • v))=
      speciesVec (MultisiteChart.tangent u)+t • speciesVec (MultisiteChart.tangent v) := by
  obtain ⟨hS,hE,hF,hC,hD⟩ := MultisiteTaylor.tangent_add_smul u v t
  funext i
  rcases i with i | (i | (i | i))
  · exact hS i
  · fin_cases i
    · exact hE
    · exact hF
  · exact hC i
  · exact hD i

/-- The linear compatibility chart: zero-total tangent reconstruction of the
reduced coordinates, as a full species vector. -/
def chartLinear (n : ℕ) : CoordinateState n →ₗ[ℝ] (Species n → ℝ) :=
  linearMapOfAddSmul (fun z => speciesVec (MultisiteChart.tangent (fromCoordinates n z)))
    (by
      intro u v t
      dsimp only
      rw [map_add,map_smul]
      exact speciesVec_tangent_add_smul _ _ t)

def chartCLM (n : ℕ) : CoordinateState n →L[ℝ] (Species n → ℝ) :=
  LinearMap.toContinuousLinearMap (chartLinear n)

theorem chartCLM_apply {n : ℕ} (z : CoordinateState n) :
    chartCLM n z=speciesVec (MultisiteChart.tangent (fromCoordinates n z)) := rfl

theorem chartCLM_injective (n : ℕ) : Function.Injective (chartCLM n) := by
  intro u v huv
  rw [chartCLM_apply,chartCLM_apply] at huv
  have h := congrArg (fun w => MultisiteChart.project (ofSpecies w)) huv
  simp only [ofSpecies_speciesVec,MultisiteChart.project_tangent] at h
  have h2 := congrArg (toCoordinates n) h
  simpa only [toCoordinates_fromCoordinates] using h2

theorem ofSpecies_chart {n : ℕ} (x : PhosphorylationSharpness.State n) (z : CoordinateState n) :
    ofSpecies (speciesVec x+chartCLM n z)=
      MultisiteChart.chart (PhosphorylationSharpness.totalE x) (PhosphorylationSharpness.totalF x)
        (PhosphorylationSharpness.totalS x) (MultisiteChart.project x+fromCoordinates n z) := by
  obtain ⟨hS,hE,hF,hC,hD⟩ := MultisiteTaylor.chart_translation x (fromCoordinates n z)
  apply MultisiteChart.state_ext
  · funext i
    exact (hS i).symm
  · exact hE.symm
  · exact hF.symm
  · funext i
    exact (hC i).symm
  · funext i
    exact (hD i).symm

theorem chart_sameTotals {n : ℕ} (x : PhosphorylationSharpness.State n) (z : CoordinateState n) :
    SameTotals (ofSpecies (speciesVec x+chartCLM n z)) x := by
  rw [ofSpecies_chart]
  exact MultisiteChart.chart_totals _ _ _ _

/-- Every full species vector with the totals of `x` lies in the chart image. -/
theorem chart_covers {n : ℕ} (x : PhosphorylationSharpness.State n) (v : Species n → ℝ)
    (hv : SameTotals (ofSpecies v) x) : ∃ z, v=speciesVec x+chartCLM n z := by
  refine ⟨toCoordinates n (MultisiteChart.project (ofSpecies v)-MultisiteChart.project x),?_⟩
  have h : ofSpecies (speciesVec x+chartCLM n (toCoordinates n
      (MultisiteChart.project (ofSpecies v)-MultisiteChart.project x)))=ofSpecies v := by
    rw [ofSpecies_chart,fromCoordinates_toCoordinates,add_sub_cancel]
    exact MultisiteChart.chart_project_of_totals _ _ _ _ hv.1 hv.2.1 hv.2.2
  have h2 := congrArg speciesVec h
  rw [speciesVec_ofSpecies,speciesVec_ofSpecies] at h2
  exact h2.symm

/-- Exact conjugacy of the literal mass-action field on the compatibility class
with the affine quadratic source field. -/
theorem speciesField_conjugacy {n : ℕ} (offset slope : PhosphorylationSharpness.Rates n)
    (x : PhosphorylationSharpness.State n)
    (heq : ∀ r, PhosphorylationSharpness.Equilibrium (affineRates offset slope r) x)
    (s : ℝ) (z : CoordinateState n) :
    speciesField (affineRates offset slope s) (speciesVec x+chartCLM n z)=
      chartCLM n (GenericQuadraticDynamics.field (MultisiteTensor.sourceMatrix offset x)
        (MultisiteTensor.sourceMatrix slope x)
        (fun r => sourceTensor offset+r • sourceTensor slope) s z) := by
  have hc := affine_coordinateField offset slope x heq s z
  have hg : GenericQuadraticDynamics.field (MultisiteTensor.sourceMatrix offset x)
      (MultisiteTensor.sourceMatrix slope x)
      (fun r => sourceTensor offset+r • sourceTensor slope) s z=
      coordinateField (affineRates offset slope s) x z := hc.symm
  rw [hg,speciesField,ofSpecies_chart,← MultisiteChart.reduced_field_tangent,chartCLM_apply]
  congr 2

/-! ### Consumption of the strengthened invariant -/

/-- **Attracting Hopf family from the strengthened invariant.** For an actual kinetic
family satisfying `HopfInvariant`, the literal mass-action field has, for every
sufficiently small positive amplitude, a positive nonconstant periodic solution at a
kinetic parameter where all rates are positive, and this orbit is orbitally
asymptotically stable relative to its compatibility class (conserved totals). -/
theorem hopf_attracting_family {n : ℕ} {σ : Type} [Fintype σ] [DecidableEq σ]
    (k : ℝ → PhosphorylationSharpness.Rates n) (x : PhosphorylationSharpness.State n)
    (h : HopfInvariant σ k x) :
    ∃ w : ℝ, 0<w ∧ ∃ (par per : ℝ → ℝ) (γ : ℝ → ℝ → Species n → ℝ),
      Tendsto par (𝓝 0) (𝓝 0) ∧ Tendsto per (𝓝 0) (𝓝 (2*Real.pi/w)) ∧
      (∀ ε>0, ∀ᶠ a in 𝓝 (0:ℝ), ∀ t, dist (γ a t) (speciesVec x)<ε) ∧
      ∀ᶠ a in 𝓝[>] (0:ℝ),
        (k (par a)).Positive ∧ par a<0 ∧ 0<per a ∧
        Function.Periodic (γ a) (per a) ∧
        (∀ t, HasDerivAt (γ a) (speciesField (k (par a)) (γ a t)) t) ∧
        (∃ t, γ a t ≠ γ a 0) ∧ (∀ t i, 0<γ a t i) ∧
        (∀ t, SameTotals (ofSpecies (γ a t)) x) ∧
        ∀ ε>0, ∃ O : Set (Species n → ℝ), IsOpen O ∧ Set.range (γ a) ⊆ O ∧
          ∀ v∈O, SameTotals (ofSpecies v) x → ∃ V : ℝ → Species n → ℝ,
            V 0=v ∧
            (∀ t, 0 ≤ t → HasDerivWithinAt V (speciesField (k (par a)) (V t)) (Set.Ici 0) t) ∧
            (∀ t, 0 ≤ t → SameTotals (ofSpecies (V t)) x) ∧
            (∀ t, 0 ≤ t → ∀ i, 0<V t i) ∧
            (∀ t, 0 ≤ t → ∃ y∈Set.range (γ a), dist (V t) y<ε) ∧
            Tendsto (fun t => Metric.infDist (V t) (Set.range (γ a))) atTop (𝓝 0) ∧
            (∀ W : ℝ → Species n → ℝ, W 0=v →
              (∀ t, 0 ≤ t → HasDerivWithinAt W (speciesField (k (par a)) (W t)) (Set.Ici 0) t) →
              ∀ t, 0 ≤ t → W t=V t) := by
  obtain ⟨-,⟨offset,slope,haff⟩,hx,heq,hpos,d,M1,hM1,hcross,hG⟩ := h
  set A0 := MultisiteTensor.sourceMatrix offset x
  set D := MultisiteTensor.sourceMatrix slope x
  let K : ℝ → GenericQuadraticTensor.Tensor (CoordinateIndex n) :=
    fun r => sourceTensor offset+r • sourceTensor slope
  have hkfun : k=affineRates offset slope := funext haff
  have heq' : ∀ r, PhosphorylationSharpness.Equilibrium (affineRates offset slope r) x := by
    intro r
    rw [← haff]
    exact heq r
  have hmat : MultisiteTensor.sourceMatrix (k 0) x=A0+(0:ℝ) • D := by
    rw [haff,sourceMatrix_affine]
  have hten : sourceTensor (k 0)=K 0 := by
    rw [haff,sourceTensor_affine]
  let dd := transport hmat d
  have hM1D : M1=D := by
    ext i j
    have hd : HasDerivAt (fun r => MultisiteTensor.sourceMatrix (k r) x i j) (D i j) 0 := by
      have hfun : (fun r => MultisiteTensor.sourceMatrix (k r) x i j)=
          fun r => A0 i j+r*D i j := by
        funext r
        rw [haff,sourceMatrix_affine]
        rfl
      rw [hfun]
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const (D i j)).const_add (A0 i j)
    exact (hM1 i j).unique hd
  have hcross' : (crossing dd D).re<0 := by
    rw [crossing_transport,← hM1D]
    exact hcross
  have hdet := data_det dd
  set q := dd.basis (Sum.inr 0)
  have h11eq := zeroResolvent_eq (A0+(0:ℝ) • D) (K 0) q hdet.1
  have h20eq := secondResolvent_eq (A0+(0:ℝ) • D) (K 0) q dd.freq hdet.2
  have hGd : (lyapunovValue dd (K 0)).re<0 := by
    rw [lyapunovValue_transport,← hten]
    exact hG
  rw [← lyapunovValue_eq_coefficient dd (K 0) _ _ h11eq h20eq] at hGd
  have hA : Function.Injective (complexMatrix (A0+(0:ℝ) • D)).mulVecLin := by
    have hi := shift_injective_of_data dd 0 (zero_not_eigenvalue dd)
    intro u v huv
    apply hi
    change (0:ℂ) • u-(complexMatrix (A0+(0:ℝ) • D)).mulVecLin u=
      (0:ℂ) • v-(complexMatrix (A0+(0:ℝ) • D)).mulVecLin v
    rw [huv,zero_smul ℂ u,zero_smul ℂ v]
  have hS : Function.Injective ((2*Complex.I*(dd.freq:ℂ)) •
      (LinearMap.id : (CoordinateIndex n → ℂ) →ₗ[ℂ] (CoordinateIndex n → ℂ))-
        (complexMatrix (A0+(0:ℝ) • D)).mulVecLin) := by
    have hi := shift_injective_of_data dd (2*Complex.I*(dd.freq:ℂ)) (double_freq_not_eigenvalue dd)
    intro u v huv
    apply hi
    simpa only [LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply] using huv
  have hsym : ∀ i j l, K 0 i j l=K 0 i l j := by
    intro i j l
    simp only [K,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [sourceTensor_symmetric offset i j l,sourceTensor_symmetric slope i j l]
  have hK : ∀ i j l, ContDiff ℝ ⊤ (fun s => K s i j l) :=
    fun i j l => affine_sourceTensor_smooth offset slope i j l
  have hconj : ∀ s z, speciesField (k s) (speciesVec x+chartCLM n z)=
      chartCLM n (GenericQuadraticDynamics.field A0 D K s z) := by
    intro s z
    rw [haff]
    exact speciesField_conjugacy offset slope x heq' s z
  obtain ⟨C,hr,hT,hshrink,hfam⟩ := GenericChartAttractingHopf.chart_attracting_hopf_family
    A0 D K hK 0 dd.freq dd.freq_pos dd.stable dd.stable_injective dd.stable_neg dd.basis
    dd.stable_real dd.critical_pair (fun i => eigen dd i) hcross' hsym hA hS _ _ h11eq h20eq hGd
    (fun s => speciesField (k s)) (fun s => speciesField_smooth (k s)) (speciesVec x)
    (speciesVec_positive x hx) (chartCLM n) (chartCLM_injective n) hconj
  let γ : ℝ → ℝ → Species n → ℝ := fun a t =>
    speciesVec x+chartCLM n (GenericAttractingFamily.periodicOrbit C a t)
  have hrange : ∀ a, Set.range (γ a)=(fun z => speciesVec x+chartCLM n z) ''
      Set.range (GenericAttractingFamily.periodicOrbit C a) := by
    intro a
    rw [← Set.range_comp]
    rfl
  have hkpos : ∀ᶠ a in 𝓝 (0:ℝ), (k (C.parameters a).2.re).Positive := hr.eventually hpos
  refine ⟨dd.freq,dd.freq_pos,fun a => (C.parameters a).2.re,fun a => (C.parameters a).2.im,γ,
    hr,hT,hshrink,?_⟩
  filter_upwards [hfam,nhdsWithin_le_nhds hkpos] with a ha hka
  obtain ⟨hbelow,hTa,hper,hdyn,hnc,hposγ,hattr⟩ := ha
  refine ⟨hka,hbelow,hTa,hper,hdyn,hnc,hposγ,fun t => chart_sameTotals x _,?_⟩
  intro ε hε
  obtain ⟨O,hO,hsub,hbasin⟩ := hattr ε hε
  refine ⟨O,hO,by rw [hrange]; exact hsub,?_⟩
  intro v hvO hv
  obtain ⟨z,rfl⟩ := chart_covers x v hv
  obtain ⟨V,hV0,hVode,hVcls,hVpos,hVtube,hVconv,hVuniq⟩ := hbasin z hvO
  refine ⟨V,hV0,hVode,?_,hVpos,?_,?_,hVuniq⟩
  · intro t ht
    obtain ⟨y,hy⟩ := hVcls t ht
    rw [hy]
    exact chart_sameTotals x y
  · intro t ht
    obtain ⟨y,⟨s,rfl⟩,hy⟩ := hVtube t ht
    exact ⟨γ a s,⟨s,rfl⟩,hy⟩
  · rw [hrange]
    exact hVconv

/-- **All-site attracting Hopf theorem.** For every number of sites `n ≥ 3` the literal
sequential distributive phosphorylation mass-action system has an actual affine positive
kinetic family with a positive parameter-independent equilibrium, and a one-parameter
family of positive nonconstant periodic solutions, at positive rates, born by a
supercritical Hopf bifurcation at the critical parameter `0` (period limit `2π/w`,
uniform shrinking to the equilibrium, onset on the side `par < 0`), each of which is
orbitally asymptotically stable relative to its compatibility class: an open
neighbourhood of the whole orbit in which every state with the same conserved totals
has a unique global forward solution that keeps its totals, stays positive, stays in
the ε-tube and converges to the orbit. -/
theorem all_site_attracting_hopf (n : ℕ) (hn : 3 ≤ n) :
    ∃ (k : ℝ → PhosphorylationSharpness.Rates n) (x : PhosphorylationSharpness.State n),
      ComponentwiseAffine k ∧ x.Positive ∧
      (∀ r, PhosphorylationSharpness.Equilibrium (k r) x) ∧
      (∀ᶠ r in 𝓝 (0:ℝ), (k r).Positive) ∧
      ∃ w : ℝ, 0<w ∧ ∃ (par per : ℝ → ℝ) (γ : ℝ → ℝ → Species n → ℝ),
      Tendsto par (𝓝 0) (𝓝 0) ∧ Tendsto per (𝓝 0) (𝓝 (2*Real.pi/w)) ∧
      (∀ ε>0, ∀ᶠ a in 𝓝 (0:ℝ), ∀ t, dist (γ a t) (speciesVec x)<ε) ∧
      ∀ᶠ a in 𝓝[>] (0:ℝ),
        (k (par a)).Positive ∧ par a<0 ∧ 0<per a ∧
        Function.Periodic (γ a) (per a) ∧
        (∀ t, HasDerivAt (γ a) (speciesField (k (par a)) (γ a t)) t) ∧
        (∃ t, γ a t ≠ γ a 0) ∧ (∀ t i, 0<γ a t i) ∧
        (∀ t, SameTotals (ofSpecies (γ a t)) x) ∧
        ∀ ε>0, ∃ O : Set (Species n → ℝ), IsOpen O ∧ Set.range (γ a) ⊆ O ∧
          ∀ v∈O, SameTotals (ofSpecies v) x → ∃ V : ℝ → Species n → ℝ,
            V 0=v ∧
            (∀ t, 0 ≤ t → HasDerivWithinAt V (speciesField (k (par a)) (V t)) (Set.Ici 0) t) ∧
            (∀ t, 0 ≤ t → SameTotals (ofSpecies (V t)) x) ∧
            (∀ t, 0 ≤ t → ∀ i, 0<V t i) ∧
            (∀ t, 0 ≤ t → ∃ y∈Set.range (γ a), dist (V t) y<ε) ∧
            Tendsto (fun t => Metric.infDist (V t) (Set.range (γ a))) atTop (𝓝 0) ∧
            (∀ W : ℝ → Species n → ℝ, W 0=v →
              (∀ t, 0 ≤ t → HasDerivWithinAt W (speciesField (k (par a)) (W t)) (Set.Ici 0) t) →
              ∀ t, 0 ≤ t → W t=V t) := by
  obtain ⟨σ,_,_,k,x,h⟩ := AllSiteHopfInvariant.all_site_hopf_invariant n hn
  have h' := h
  obtain ⟨-,haff,hx,heq,hpos,-⟩ := h'
  exact ⟨k,x,haff,hx,heq,hpos,hopf_attracting_family k x h⟩

end
end ThreeSitePhosphorylation.AllSiteAttractingFamily
