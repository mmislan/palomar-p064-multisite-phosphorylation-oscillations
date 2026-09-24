import proofs.ThreeSitePhosphorylation.AddedSiteCrossingTransport
import proofs.ThreeSitePhosphorylation.AddedSiteSpectralStep

/-! Docking of the coefficient transport onto B's actual critical continuation.

`HopfInvariant` strengthens B's `SpectralInvariant` by the sign of the
normalized Lyapunov value `Re G<0`, computed with GENUINE matrix resolvents,
the basis coordinate as normalized left functional, the critical basis vector
and the frequency of the SAME spectral data (convention of
`GenericClosedBranchCurvature`). `hopf_site_step` proves that this strengthened
invariant is inherited by the actual frozen-load (n+1)-site family along the
SAME critical curve, scale and continued data that B's `critical_continuation`
produces; `hopf_iterate` iterates it. -/
namespace ThreeSitePhosphorylation.AddedSiteHopfStep
noncomputable section
open Filter
open scoped Topology
open PhosphorylationSharpness MultisiteChart MultisiteSource MultisiteCoordinates
open MultisiteTensor ScaledMultisiteSource ScaledJointSource ScaledAffineFamily
open CriticalSpectrum AddedSiteSourceMatrix AddedSiteZeroLoadBasis
open AddedSiteCriticalContinuation AddedSiteSpectralStep
open GenericComplexification AddedSiteHessianTransport AddedSiteCoefficientTransport
open AddedSiteCoefficientContinuity

/-- The normalized Lyapunov value of spectral data with genuine resolvents. -/
def lyapunovValue {ι σ : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}
    (d : Data σ A) (T : GenericQuadraticTensor.Tensor ι) : ℂ :=
  resolventCoefficient (d.basis.coord (Sum.inr 0)).toContinuousLinearMap A T
    (d.basis (Sum.inr 0)) d.freq

theorem lyapunovValue_transport {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (h : A=B) (d : Data σ A) (T : GenericQuadraticTensor.Tensor ι) :
    lyapunovValue (transport h d) T=lyapunovValue d T := by
  subst h
  rfl

/-- Both genuine resolvent operators are invertible for full spectral data. -/
theorem data_det {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {A : Matrix ι ι ℝ} (d : Data σ A) :
    (complexMatrix A).det ≠ 0 ∧ (secondShift A d.freq).det ≠ 0 := by
  have h0 := shift_injective_of_data d 0 (zero_not_eigenvalue d)
  have h2 := shift_injective_of_data d (2*Complex.I*(d.freq:ℂ)) (double_freq_not_eigenvalue d)
  constructor
  · apply det_ne_zero_of_injective
    intro u v huv
    apply h0
    change (0:ℂ) • u-(complexMatrix A).mulVecLin u=(0:ℂ) • v-(complexMatrix A).mulVecLin v
    rw [huv,zero_smul,zero_smul]
  · apply secondShift_det_ne_zero_of_injective
    intro u v huv
    apply h2
    simpa only [LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply] using huv

/-- The Lyapunov value is the normalized coefficient `G` of ANY genuine
resolvent solutions (the form consumed by the curvature theorem). -/
theorem lyapunovValue_eq_coefficient {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]
    [DecidableEq σ] {A : Matrix ι ι ℝ} (d : Data σ A) (T : GenericQuadraticTensor.Tensor ι)
    (k11 k20 : ι → ℂ)
    (k11eq : (complexMatrix A).mulVec k11=
      GenericTensorBilinear.complexBilinear T (d.basis (Sum.inr 0))
        (conjugateVector (d.basis (Sum.inr 0))))
    (k20eq : (2*Complex.I*(d.freq:ℂ)) • k20-(complexMatrix A).mulVec k20=
      GenericTensorBilinear.complexBilinear T (d.basis (Sum.inr 0)) (d.basis (Sum.inr 0))) :
    coefficient (d.basis.coord (Sum.inr 0)) T (d.basis (Sum.inr 0)) k11 k20=lyapunovValue d T := by
  obtain ⟨h0,h2⟩ := data_det d
  exact coefficient_eq_resolventCoefficient (d.basis.coord (Sum.inr 0)).toContinuousLinearMap
    A T _ d.freq h0 h2 k11 k20 k11eq k20eq

/-- B's split embedding with zero normal part is the face matrix. -/
theorem siteEquiv_face {n : ℕ} (y : CoordinateIndex n → ℂ) :
    siteEquiv ℂ n (y,0)=(complexRect (faceMatrix n)).mulVec y := by
  funext i
  rcases i with i | (i | i) <;> refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [AddedSiteCrossingTransport.face_mulVec_normal _ _
      (by rintro (j | j | j) <;>
        simp [AddedSiteCrossingTransport.faceIndex,AddedSiteCrossingTransport.last_ne_castSucc])]
    simp [siteEmbedFun]
  · rw [show (Sum.inl j.castSucc : CoordinateIndex (n+1))=
        AddedSiteCrossingTransport.faceIndex n (Sum.inl j) from rfl,
      AddedSiteCrossingTransport.face_mulVec_index]
    simp [siteEmbedFun,AddedSiteCrossingTransport.faceIndex]
  · rw [AddedSiteCrossingTransport.face_mulVec_normal _ _
      (by rintro (j | j | j) <;>
        simp [AddedSiteCrossingTransport.faceIndex,AddedSiteCrossingTransport.last_ne_castSucc])]
    simp [siteEmbedFun]
  · rw [show (Sum.inr (Sum.inl j.castSucc) : CoordinateIndex (n+1))=
        AddedSiteCrossingTransport.faceIndex n (Sum.inr (Sum.inl j)) from rfl,
      AddedSiteCrossingTransport.face_mulVec_index]
    simp [siteEmbedFun,AddedSiteCrossingTransport.faceIndex]
  · rw [AddedSiteCrossingTransport.face_mulVec_normal _ _
      (by rintro (j | j | j) <;>
        simp [AddedSiteCrossingTransport.faceIndex,AddedSiteCrossingTransport.last_ne_castSucc])]
    simp [siteEmbedFun]
  · rw [show (Sum.inr (Sum.inr j.castSucc) : CoordinateIndex (n+1))=
        AddedSiteCrossingTransport.faceIndex n (Sum.inr (Sum.inr j)) from rfl,
      AddedSiteCrossingTransport.face_mulVec_index]
    simp [siteEmbedFun,AddedSiteCrossingTransport.faceIndex]

theorem jointRates_zero {n : ℕ} (k : ℝ → Rates n) (x : State n) (κ : ℝ) :
    jointRates k x κ (0,0)=zeroRates (k 0) κ (κ/x.F) := by
  simp [jointRates,zeroRates]

theorem jointMatrix_zero {n : ℕ} (k : ℝ → Rates n) (x : State n) (κ : ℝ) :
    jointMatrix k x κ (0,0)=sourceMatrix (zeroRates (k 0) κ (κ/x.F)) (zeroState x) := by
  rw [jointMatrix,jointRates_zero]
  simp [zeroState]

/-- Exact zero-load equality of the genuine-resolvent Lyapunov value for the
actual child source at the parent critical point, for any genuine child
normalized left functional restricting to the parent coordinate (step 4). -/
theorem zero_load_value {n : ℕ} {σ : Type*} [Fintype σ] [DecidableEq σ]
    (k : ℝ → Rates n) (x : State n) (κ : ℝ) (d : Data σ (sourceMatrix (k 0) x))
    (p0 : (CoordinateIndex (n+1) → ℂ) →L[ℂ] ℂ)
    (hp0 : ∀ y, p0 (siteEquiv ℂ n (y,0))=d.basis.coord (Sum.inr 0) y)
    (h0 : (complexMatrix (jointMatrix k x κ (0,0))).det ≠ 0)
    (h2 : (secondShift (jointMatrix k x κ (0,0)) d.freq).det ≠ 0) :
    resolventCoefficient p0 (jointMatrix k x κ (0,0)) (sourceTensor (jointRates k x κ (0,0)))
      (siteEquiv ℂ n (d.basis (Sum.inr 0),0)) d.freq=
      lyapunovValue d (sourceTensor (k 0)) := by
  have hA : jointMatrix k x κ (0,0)*faceMatrix n=faceMatrix n*sourceMatrix (k 0) x := by
    rw [jointMatrix_zero]; exact sourceMatrix_face (k 0) κ (κ/x.F) x
  have hT : ∀ u v : CoordinateIndex n → ℝ,
      GenericTensorBilinear.realBilinear (sourceTensor (jointRates k x κ (0,0)))
        ((faceMatrix n).mulVec u) ((faceMatrix n).mulVec v)=
        (faceMatrix n).mulVec (GenericTensorBilinear.realBilinear (sourceTensor (k 0)) u v) := by
    intro u v
    rw [jointRates_zero]
    exact sourceTensor_face (k 0) κ (κ/x.F) x u v
  obtain ⟨d0,d2⟩ := data_det d
  have e11 := zeroResolvent_eq _ (sourceTensor (k 0)) (d.basis (Sum.inr 0)) d0
  have e20 := secondResolvent_eq _ (sourceTensor (k 0)) (d.basis (Sum.inr 0)) d.freq d2
  obtain ⟨f11,f20⟩ := resolvent_equations_transport _ (jointMatrix k x κ (0,0)) (faceMatrix n) hA
    (sourceTensor (k 0)) (sourceTensor (jointRates k x κ (0,0))) hT d.freq
    (d.basis (Sum.inr 0)) _ _ e11 e20
  have hres : ∀ y, p0.toLinearMap ((complexRect (faceMatrix n)).mulVec y)=
      d.basis.coord (Sum.inr 0) y := by
    intro y
    rw [← siteEquiv_face]
    exact hp0 y
  rw [siteEquiv_face,← coefficient_eq_resolventCoefficient p0 _ _ _ d.freq h0 h2 _ _ f11 f20]
  exact coefficient_transport _ _ (faceMatrix n) hT (d.basis.coord (Sum.inr 0)) p0.toLinearMap
    hres _ _ _

/-- The strengthened site invariant: B's spectral invariant together with a
negative normalized Lyapunov value for the SAME spectral data. -/
def HopfInvariant {n : ℕ} (σ : Type*) [Fintype σ] [DecidableEq σ]
    (k : ℝ → Rates n) (x : State n) : Prop :=
  MultisiteSmoothField.RatesSmooth k ∧ ComponentwiseAffine k ∧ x.Positive ∧
    (∀ r, Equilibrium (k r) x) ∧ (∀ᶠ r in 𝓝 (0:ℝ), (k r).Positive) ∧
    ∃ d : Data σ (sourceMatrix (k 0) x),
      ∃ M1 : Matrix (CoordinateIndex n) (CoordinateIndex n) ℝ,
        (∀ i j, HasDerivAt (fun r => sourceMatrix (k r) x i j) (M1 i j) 0) ∧
          (crossing d M1).re<0 ∧ (lyapunovValue d (sourceTensor (k 0))).re<0

theorem HopfInvariant.spectral {n : ℕ} {σ : Type*} [Fintype σ] [DecidableEq σ]
    {k : ℝ → Rates n} {x : State n} (h : HopfInvariant σ k x) : SpectralInvariant σ k x := by
  obtain ⟨hk,ha,hx,he,hp,d,M1,hM1,hc,-⟩ := h
  exact ⟨hk,ha,hx,he,hp,d,M1,hM1,hc⟩

/-- Along B's continued critical data, the genuine Lyapunov value is eventually
negative (step 5). -/
theorem eventually_lyapunov_negative {n : ℕ} {σ : Type*} [Fintype σ] [DecidableEq σ]
    (k : ℝ → Rates n) (x : State n) (hk : MultisiteSmoothField.RatesSmooth k)
    (κ : ℝ) (d : Data σ (sourceMatrix (k 0) x))
    (hG : (lyapunovValue d (sourceTensor (k 0))).re<0)
    (R : ℝ → ℝ) (q : ℝ → CoordinateIndex (n+1) → ℂ)
    (p : ℝ → (CoordinateIndex (n+1) → ℂ) →L[ℂ] ℂ) (ω : ℝ → ℝ)
    (hR : ContinuousAt R 0) (hR0 : R 0=0) (hq : ContinuousAt q 0)
    (hq0 : q 0=siteEquiv ℂ n (d.basis (Sum.inr 0),0)) (hpc : ContinuousAt p 0)
    (hp0 : ∀ y, p 0 (siteEquiv ℂ n (y,0))=d.basis.coord (Sum.inr 0) y)
    (hω : ContinuousAt ω 0) (hω0 : ω 0=d.freq)
    (h0 : (complexMatrix (jointMatrix k x κ (0,0))).det ≠ 0)
    (h2 : (secondShift (jointMatrix k x κ (0,0)) d.freq).det ≠ 0) :
    ∀ᶠ ε in 𝓝 (0:ℝ), (resolventCoefficient (p ε) (jointMatrix k x κ (ε,R ε))
      (sourceTensor (jointRates k x κ (ε,R ε))) (q ε) (ω ε)).re<0 := by
  have hγc : ContinuousAt (fun ε : ℝ => ((ε,R ε) : ℝ × ℝ)) 0 := continuousAt_id.prodMk hR
  have hM : ContinuousAt (fun ε => jointMatrix k x κ (ε,R ε)) 0 :=
    (jointMatrix_smooth k x κ hk).continuous.continuousAt.comp hγc
  have hrates : AddedSiteCrossingTransport.RatesContinuousAt
      (fun ε => jointRates k x κ (ε,R ε)) 0 := by
    obtain ⟨ha,hb,hc,hα,hβ,hγ⟩ := jointRates_smooth k x κ hk
    intro i
    exact ⟨(ha i).continuous.continuousAt.comp hγc,(hb i).continuous.continuousAt.comp hγc,
      (hc i).continuous.continuousAt.comp hγc,(hα i).continuous.continuousAt.comp hγc,
      (hβ i).continuous.continuousAt.comp hγc,(hγ i).continuous.continuousAt.comp hγc⟩
  have hT := AddedSiteCrossingTransport.sourceTensor_continuousAt hrates
  have hM0 : jointMatrix k x κ (0,R 0)=jointMatrix k x κ (0,0) := by rw [hR0]
  have hJ0 : jointRates k x κ (0,R 0)=jointRates k x κ (0,0) := by rw [hR0]
  have h0' : (complexMatrix (jointMatrix k x κ (0,R 0))).det ≠ 0 := by rw [hM0]; exact h0
  have h2' : (secondShift (jointMatrix k x κ (0,R 0)) (ω 0)).det ≠ 0 := by
    rw [hM0,hω0]; exact h2
  have hG0 : (resolventCoefficient (p 0) (jointMatrix k x κ (0,R 0))
      (sourceTensor (jointRates k x κ (0,R 0))) (q 0) (ω 0)).re<0 := by
    rw [hM0,hJ0,hq0,hω0,zero_load_value k x κ d (p 0) hp0 h0 h2]
    exact hG
  exact eventually_coefficient_negative hpc hM hT hq hω h0' h2' hG0

/-- Hopf site step: the strengthened invariant (spectral data, negative crossing
and negative Lyapunov value) is inherited by the actual frozen-load family for
all sufficiently small positive loads, with B's scale and critical curve. -/
theorem hopf_site_step {n : ℕ} {σ : Type*} [Fintype σ] [DecidableEq σ]
    (k : ℝ → Rates n) (x : State n) (h : HopfInvariant σ k x) :
    ∃ κ : ℝ, 0<κ ∧ ∃ R : ℝ → ℝ, R 0=0 ∧ ContinuousAt R 0 ∧
      ∀ᶠ ε in 𝓝[>] (0:ℝ),
        HopfInvariant (σ ⊕ Fin 3) (frozenRates k x κ ε (R ε)) (appendState x ε (2*ε) ε) := by
  obtain ⟨hk,haff,hx,heq,hpos,d,M1,hM1,hcross,hG⟩ := h
  have hF : x.F ≠ 0 := ne_of_gt hx.2.2.1
  obtain ⟨R,q,p,ω,hR,hR0,hq,hq0,hpc,hp0,hω,hω0,hev⟩ :=
    critical_continuation k x hk hF d M1 hM1 hcross
  refine ⟨scale d,scale_pos k x d,R,hR0,hR.continuousAt,?_⟩
  -- genuine invertibility at the zero-load base point from the continued data
  obtain ⟨dz,-,-,hωz,-⟩ := hev.self_of_nhds
  obtain ⟨dz0,dz2⟩ := data_det dz
  have hM0 : jointMatrix k x (scale d) (0,R 0)=jointMatrix k x (scale d) (0,0) := by rw [hR0]
  have h0 : (complexMatrix (jointMatrix k x (scale d) (0,0))).det ≠ 0 := by rw [← hM0]; exact dz0
  have h2 : (secondShift (jointMatrix k x (scale d) (0,0)) d.freq).det ≠ 0 := by
    rw [← hM0,← hω0,← hωz]; exact dz2
  have hlyap := eventually_lyapunov_negative k x hk (scale d) d hG R q p ω hR.continuousAt hR0
    hq hq0 hpc hp0 hω hω0 h0 h2
  have hpos2 : ∀ᶠ ε in 𝓝 (0:ℝ), ∀ᶠ r in 𝓝 (0:ℝ), (k (R ε+r)).Positive := by
    have h1 : ContinuousAt (fun q : ℝ × ℝ => R q.1) ((0:ℝ),(0:ℝ)) :=
      ContinuousAt.comp_of_eq (g := R) (f := Prod.fst) hR.continuousAt continuousAt_fst rfl
    have hc : ContinuousAt (fun q : ℝ × ℝ => R q.1+q.2) ((0:ℝ),(0:ℝ)) :=
      h1.add continuousAt_snd
    have ht : Tendsto (fun q : ℝ × ℝ => R q.1+q.2) (𝓝 ((0:ℝ),(0:ℝ))) (𝓝 0) := by
      have h0 : R ((0:ℝ),(0:ℝ)).1+((0:ℝ),(0:ℝ)).2=0 := by simp [hR0]
      simpa only [h0] using hc.tendsto
    have h2 := ht.eventually hpos
    rw [nhds_prod_eq] at h2
    exact h2.curry
  have hall := (hev.and hlyap).and hpos2
  filter_upwards [nhdsWithin_le_nhds hall,self_mem_nhdsWithin] with ε hε hεpos
  obtain ⟨⟨⟨dε,hqε,hpε,hωε,hcr⟩,hLε⟩,hposε⟩ := hε
  have hε0 : (0:ℝ)<ε := hεpos
  have hmat : jointMatrix k x (scale d) (ε,R ε)=
      sourceMatrix (frozenRates k x (scale d) ε (R ε) 0) (appendState x ε (2*ε) ε) := by
    rw [frozen_matrix,add_zero]
  have hrates : frozenRates k x (scale d) ε (R ε) 0=jointRates k x (scale d) (ε,R ε) := by
    simp [frozenRates]
  refine ⟨frozen_smooth k x (scale d) ε (R ε) hk,frozen_affine k x (scale d) ε (R ε) haff,
    append_positive x hx ε (2*ε) ε hε0 (by linarith) hε0,
    frozen_equilibrium k x hx heq (scale d) ε (R ε),?_,
    transport hmat dε,kineticDerivative k x (scale d) (ε,R ε),?_,?_,?_⟩
  · filter_upwards [hposε] with r hr
    exact (extendedFamily_positive k x hx (scale d) ε (scale_pos k x d) hε0 (R ε+r) hr).1
  · intro i j
    exact kineticDerivative_hasDerivAt k x (scale d) hk ε (R ε) i j
  · rw [crossing_transport]
    exact hcr
  · rw [lyapunovValue_transport,hrates]
    have hv : lyapunovValue dε (sourceTensor (jointRates k x (scale d) (ε,R ε)))=
        resolventCoefficient (p ε) (jointMatrix k x (scale d) (ε,R ε))
          (sourceTensor (jointRates k x (scale d) (ε,R ε))) (q ε) (ω ε) := by
      unfold lyapunovValue
      rw [hpε,hqε,hωε]
    rw [hv]
    exact hLε

/-- The strengthened Hopf invariant iterates over any number of added sites. -/
theorem hopf_iterate {n : ℕ} {σ : Type} [Fintype σ] [DecidableEq σ]
    (k : ℝ → Rates n) (x : State n) (h : HopfInvariant σ k x) (m : ℕ) :
    ∃ (σ' : Type) (_ : Fintype σ') (_ : DecidableEq σ')
      (k' : ℝ → Rates (n+m)) (x' : State (n+m)), HopfInvariant σ' k' x' := by
  induction m with
  | zero => exact ⟨σ,inferInstance,inferInstance,k,x,h⟩
  | succ m ih =>
    obtain ⟨σ',hf,hd,k',x',h'⟩ := ih
    obtain ⟨κ,-,R,-,-,hev⟩ := hopf_site_step k' x' h'
    obtain ⟨ε,hε⟩ := hev.exists
    exact ⟨σ' ⊕ Fin 3,inferInstance,inferInstance,frozenRates k' x' κ ε (R ε),
      appendState x' ε (2*ε) ε,hε⟩

end
end ThreeSitePhosphorylation.AddedSiteHopfStep
