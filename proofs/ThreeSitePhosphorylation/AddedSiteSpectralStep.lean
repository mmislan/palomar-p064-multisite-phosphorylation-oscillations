import proofs.ThreeSitePhosphorylation.AddedSiteCriticalContinuation
import proofs.ThreeSitePhosphorylation.ScaledAffineFamily

/-! The spectral part of the uniform site-addition step for the actual
chemical family. Fix the separating scale, pick any sufficiently small
positive load, freeze it, and translate the kinetic parameter to the
continued critical value. The same spectral invariant, with affine rates,
fixed positive equilibrium, local rate positivity and negative actual
crossing, holds for the (n+1)-site family. The Lyapunov-coefficient sign
and the attraction theorem are not part of this invariant. -/
namespace ThreeSitePhosphorylation.AddedSiteSpectralStep
noncomputable section
open Filter
open scoped Topology
open PhosphorylationSharpness MultisiteChart MultisiteSource MultisiteCoordinates
open MultisiteTensor ScaledMultisiteSource ScaledJointSource ScaledAffineFamily
open CriticalSpectrum AddedSiteSourceMatrix AddedSiteZeroLoadBasis AddedSiteCriticalContinuation
open GenericComplexification

/-- Transport of spectral data along an equality of matrices. -/
def transport {ι σ : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℝ}
    (h : A = B) (d : Data σ A) : Data σ B := h ▸ d

theorem crossing_transport {ι σ : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℝ}
    (h : A = B) (d : Data σ A) (M : Matrix ι ι ℝ) :
    crossing (transport h d) M = crossing d M := by
  subst h
  rfl

theorem transport_basis {ι σ : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℝ}
    (h : A = B) (d : Data σ A) : (transport h d).basis = d.basis := by
  subst h
  rfl

theorem transport_freq {ι σ : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℝ}
    (h : A = B) (d : Data σ A) : (transport h d).freq = d.freq := by
  subst h
  rfl

/-- Spectral site invariant of an actual kinetic family, critical at parameter 0. -/
def SpectralInvariant {n : ℕ} (σ : Type*) [Fintype σ] [DecidableEq σ]
    (k : ℝ → Rates n) (x : State n) : Prop :=
  MultisiteSmoothField.RatesSmooth k ∧ ComponentwiseAffine k ∧ x.Positive ∧
    (∀ r, Equilibrium (k r) x) ∧ (∀ᶠ r in 𝓝 (0:ℝ), (k r).Positive) ∧
    ∃ d : Data σ (sourceMatrix (k 0) x),
      ∃ M1 : Matrix (CoordinateIndex n) (CoordinateIndex n) ℝ,
        (∀ i j, HasDerivAt (fun r => sourceMatrix (k r) x i j) (M1 i j) 0) ∧
          (crossing d M1).re < 0

/-- The frozen-load (n+1)-site family, translated to the kinetic value `rstar`. -/
def frozenRates {n : ℕ} (k : ℝ → Rates n) (x : State n) (κ ε rstar : ℝ) :
    ℝ → Rates (n+1) :=
  fun r => jointRates k x κ (ε,rstar+r)

theorem frozen_smooth {n : ℕ} (k : ℝ → Rates n) (x : State n) (κ ε rstar : ℝ)
    (hk : MultisiteSmoothField.RatesSmooth k) :
    MultisiteSmoothField.RatesSmooth (frozenRates k x κ ε rstar) := by
  obtain ⟨ha,hb,hc,hα,hβ,hγ⟩ := jointRates_smooth k x κ hk
  have hl : ContDiff ℝ ⊤ (fun r : ℝ => ((ε,rstar+r) : ℝ × ℝ)) :=
    contDiff_const.prodMk (contDiff_const.add contDiff_id)
  exact ⟨fun i => (ha i).comp hl,fun i => (hb i).comp hl,fun i => (hc i).comp hl,
    fun i => (hα i).comp hl,fun i => (hβ i).comp hl,fun i => (hγ i).comp hl⟩

theorem frozen_affine {n : ℕ} (k : ℝ → Rates n) (x : State n) (κ ε rstar : ℝ)
    (hk : ComponentwiseAffine k) : ComponentwiseAffine (frozenRates k x κ ε rstar) :=
  componentwiseAffine_translate _ (extendedFamily_affine k hk x κ ε) rstar

theorem frozen_equilibrium {n : ℕ} (k : ℝ → Rates n) (x : State n) (hx : x.Positive)
    (heq : ∀ r, Equilibrium (k r) x) (κ ε rstar : ℝ) (r : ℝ) :
    Equilibrium (frozenRates k x κ ε rstar r) (appendState x ε (2*ε) ε) :=
  extendedFamily_equilibrium k x hx heq κ ε (rstar+r)

theorem frozen_matrix {n : ℕ} (k : ℝ → Rates n) (x : State n) (κ ε rstar r : ℝ) :
    sourceMatrix (frozenRates k x κ ε rstar r) (appendState x ε (2*ε) ε) =
      jointMatrix k x κ (ε,rstar+r) := rfl

/-- Spectral site-addition step for the actual chemical family. The scale is
fixed by the parent spectrum; the critical curve `R` is fixed; every
sufficiently small positive load, frozen, gives the full invariant again. -/
theorem site_step {n : ℕ} {σ : Type*} [Fintype σ] [DecidableEq σ]
    (k : ℝ → Rates n) (x : State n) (h : SpectralInvariant σ k x) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ R : ℝ → ℝ, R 0 = 0 ∧ ContinuousAt R 0 ∧
      ∀ᶠ ε in 𝓝[>] (0:ℝ),
        SpectralInvariant (σ ⊕ Fin 3) (frozenRates k x κ ε (R ε)) (appendState x ε (2*ε) ε) := by
  obtain ⟨hk,haff,hx,heq,hpos,d,M1,hM1,hcross⟩ := h
  have hF : x.F ≠ 0 := ne_of_gt hx.2.2.1
  obtain ⟨R,q,p,ω,hR,hR0,-,-,-,-,-,-,hev⟩ := critical_continuation k x hk hF d M1 hM1 hcross
  refine ⟨scale d,scale_pos k x d,R,hR0,hR.continuousAt,?_⟩
  have hpos2 : ∀ᶠ ε in 𝓝 (0:ℝ), ∀ᶠ r in 𝓝 (0:ℝ), (k (R ε+r)).Positive := by
    have h1 : ContinuousAt (fun q : ℝ × ℝ => R q.1) ((0:ℝ),(0:ℝ)) :=
      ContinuousAt.comp_of_eq (g := R) (f := Prod.fst) hR.continuousAt continuousAt_fst rfl
    have hc : ContinuousAt (fun q : ℝ × ℝ => R q.1+q.2) ((0:ℝ),(0:ℝ)) :=
      h1.add continuousAt_snd
    have ht : Tendsto (fun q : ℝ × ℝ => R q.1+q.2) (𝓝 ((0:ℝ),(0:ℝ))) (𝓝 0) := by
      have h0 : R ((0:ℝ),(0:ℝ)).1+((0:ℝ),(0:ℝ)).2 = 0 := by simp [hR0]
      simpa only [h0] using hc.tendsto
    have h2 := ht.eventually hpos
    rw [nhds_prod_eq] at h2
    exact h2.curry
  have hboth := hev.and hpos2
  filter_upwards [nhdsWithin_le_nhds hboth,self_mem_nhdsWithin] with ε hε hεpos
  obtain ⟨⟨dε,-,-,-,hcr⟩,hposε⟩ := hε
  have hε0 : (0:ℝ) < ε := hεpos
  have hmat : jointMatrix k x (scale d) (ε,R ε) =
      sourceMatrix (frozenRates k x (scale d) ε (R ε) 0) (appendState x ε (2*ε) ε) := by
    rw [frozen_matrix,add_zero]
  refine ⟨frozen_smooth k x (scale d) ε (R ε) hk,frozen_affine k x (scale d) ε (R ε) haff,
    append_positive x hx ε (2*ε) ε hε0 (by linarith) hε0,
    frozen_equilibrium k x hx heq (scale d) ε (R ε),?_,
    transport hmat dε,kineticDerivative k x (scale d) (ε,R ε),?_,?_⟩
  · filter_upwards [hposε] with r hr
    exact (extendedFamily_positive k x hx (scale d) ε (scale_pos k x d) hε0 (R ε+r) hr).1
  · intro i j
    exact kineticDerivative_hasDerivAt k x (scale d) hk ε (R ε) i j
  · rw [crossing_transport]
    exact hcr

/-- Genuine resolvent injectivity from the full spectral data: every shift
avoiding the eigenvalue list is injective on the complexified state. -/
theorem shift_injective_of_data {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]
    [DecidableEq σ] {A : Matrix ι ι ℝ} (d : Data σ A) (z : ℂ)
    (hz : ∀ i, z ≠ eigenvalues d i) :
    Function.Injective (fun v => z • v - (complexMatrix A).mulVecLin v) :=
  AddedSiteZeroLoadBasis.shift_injective _ d.basis (eigenvalues d) (eigen_lin d) z hz

theorem zero_not_eigenvalue {ι σ : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}
    (d : Data σ A) (i : σ ⊕ Fin 2) : (0 : ℂ) ≠ eigenvalues d i := by
  intro h
  rcases i with s | a
  · have := d.stable_neg s
    have h' : (d.stable s : ℂ) = 0 := by simpa using h.symm
    exact absurd (by exact_mod_cast h') (ne_of_lt this)
  · have hw := d.freq_pos
    have him := congrArg Complex.im h
    fin_cases a <;> simp at him <;> linarith

theorem double_freq_not_eigenvalue {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (d : Data σ A) (i : σ ⊕ Fin 2) :
    2*Complex.I*(d.freq : ℂ) ≠ eigenvalues d i := by
  intro h
  have hw := d.freq_pos
  have him := congrArg Complex.im h
  rcases i with s | a
  · simp at him
    linarith
  · fin_cases a <;> simp at him <;> linarith

/-- The spectral invariant iterates over any number of added sites. The
Lyapunov-coefficient and attraction inputs are separate obligations. -/
theorem spectral_iterate {n : ℕ} {σ : Type} [Fintype σ] [DecidableEq σ]
    (k : ℝ → Rates n) (x : State n) (h : SpectralInvariant σ k x) (m : ℕ) :
    ∃ (σ' : Type) (_ : Fintype σ') (_ : DecidableEq σ')
      (k' : ℝ → Rates (n+m)) (x' : State (n+m)), SpectralInvariant σ' k' x' := by
  induction m with
  | zero => exact ⟨σ,inferInstance,inferInstance,k,x,h⟩
  | succ m ih =>
    obtain ⟨σ',hf,hd,k',x',h'⟩ := ih
    obtain ⟨κ,-,R,-,-,hev⟩ := site_step k' x' h'
    obtain ⟨ε,hε⟩ := hev.exists
    exact ⟨σ' ⊕ Fin 3,inferInstance,inferInstance,frozenRates k' x' κ ε (R ε),
      appendState x' ε (2*ε) ε,hε⟩

end
end ThreeSitePhosphorylation.AddedSiteSpectralStep
