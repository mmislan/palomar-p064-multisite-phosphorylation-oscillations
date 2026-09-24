import proofs.ThreeSitePhosphorylation.SimpleEigenpair
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Choose

namespace ThreeSitePhosphorylation.NearbyEigenbasis
noncomputable section
open Filter
open scoped Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]

/-- The endomorphism taking the fixed reference basis to the proposed columns. -/
def columnMap (b : Module.Basis ι ℝ E) (v : ι → E) : E →L[ℝ] E :=
  ∑ i, (b.coord i).toContinuousLinearMap.smulRight (v i)

theorem columnMap_basis (b : Module.Basis ι ℝ E) (v : ι → E) (i : ι) :
    columnMap b v (b i)=v i := by
  simp [columnMap,ContinuousLinearMap.sum_apply,Module.Basis.coord_apply,Finsupp.single_apply]

theorem columnMap_self (b : Module.Basis ι ℝ E) : columnMap b b=1 := by
  apply ContinuousLinearMap.coe_injective
  apply b.ext
  intro i
  simp [columnMap_basis]

theorem columnMap_continuousAt (b : Module.Basis ι ℝ E) (v : ℝ → ι → E)
    (hv : ∀ i, ContinuousAt (fun a => v a i) 0) :
    ContinuousAt (fun a => columnMap b (v a)) 0 := by
  have hterm (i : ι) : ContinuousAt
      (fun a => (b.coord i).toContinuousLinearMap.smulRight (v a i)) 0 :=
    (ContinuousLinearMap.smulRightL ℝ E E (b.coord i).toContinuousLinearMap).continuous.continuousAt.comp (hv i)
  have hs (s : Finset ι) : ContinuousAt
      (fun a => ∑ i ∈ s, (b.coord i).toContinuousLinearMap.smulRight (v a i)) 0 := by
    induction s using Finset.induction_on with
    | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : E →L[ℝ] E)) 0)
    | @insert i s hi ih => simpa only [Finset.sum_insert hi] using (hterm i).add ih
  exact hs Finset.univ

theorem eventually_columnMap_isUnit (b : Module.Basis ι ℝ E) (v : ℝ → ι → E)
    (hv : ∀ i, ContinuousAt (fun a => v a i) 0) (hzero : v 0=b) :
    ∀ᶠ a in 𝓝 (0:ℝ), IsUnit (columnMap b (v a)) := by
  have hunit : IsUnit (columnMap b (v 0)) := by rw [hzero,columnMap_self]; exact isUnit_one
  exact (columnMap_continuousAt b v hv).eventually (Units.isOpen.mem_nhds hunit)

/-- Inverse coordinates are defined for every parameter, and are genuine
basis coordinates whenever the column map is invertible. -/
def inverseCoordinate (b : Module.Basis ι ℝ E) (v : ι → E) (i : ι) : E →L[ℝ] ℝ :=
  (b.coord i).toContinuousLinearMap.comp (Ring.inverse (columnMap b v))

theorem inverseCoordinate_self (b : Module.Basis ι ℝ E) (i : ι) :
    inverseCoordinate b b i=(b.coord i).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  simp [inverseCoordinate,columnMap_self]

theorem inverseCoordinate_continuousAt (b : Module.Basis ι ℝ E) (v : ℝ → ι → E)
    (hv : ∀ i, ContinuousAt (fun a => v a i) 0) (hzero : v 0=b) (i : ι) :
    ContinuousAt (fun a => inverseCoordinate b (v a) i) 0 := by
  have hi : ContinuousAt (Ring.inverse : (E →L[ℝ] E) → (E →L[ℝ] E))
      (columnMap b (v 0)) := by
    rw [hzero,columnMap_self]
    simpa using NormedRing.inverse_continuousAt (1 : (E →L[ℝ] E)ˣ)
  have hcomp : ContinuousAt (fun a : ℝ => Ring.inverse (columnMap b (v a))) 0 :=
    ContinuousAt.comp (f := fun a : ℝ => columnMap b (v a)) hi (columnMap_continuousAt b v hv)
  exact ContinuousAt.comp (f := fun a : ℝ => Ring.inverse (columnMap b (v a)))
    (ContinuousLinearMap.compL ℝ E E ℝ (b.coord i).toContinuousLinearMap).continuous.continuousAt hcomp

theorem inverseCoordinate_columns (b : Module.Basis ι ℝ E) (v : ι → E)
    (hu : IsUnit (columnMap b v)) (i j : ι) :
    inverseCoordinate b v i (v j)=if i=j then 1 else 0 := by
  have hh := DFunLike.congr_fun (Ring.inverse_mul_cancel (columnMap b v) hu) (b j)
  have hinv : Ring.inverse (columnMap b v) (v j)=b j := by
    simpa only [ContinuousLinearMap.mul_apply,columnMap_basis,ContinuousLinearMap.one_apply] using hh
  simp [inverseCoordinate,hinv,Module.Basis.coord_apply,Finsupp.single_apply,eq_comm]

theorem exists_basis_of_columnMap_isUnit (b : Module.Basis ι ℝ E) (v : ι → E)
    (hu : IsUnit (columnMap b v)) :
    ∃ c : Module.Basis ι ℝ E, (∀ i, c i=v i) ∧
      ∀ i, (c.coord i).toContinuousLinearMap=inverseCoordinate b v i := by
  let e := LinearEquiv.ofBijective (columnMap b v).toLinearMap
    (ContinuousLinearMap.isUnit_iff_bijective.mp hu)
  let c := b.map e
  have hc (i : ι) : c i=v i := columnMap_basis b v i
  refine ⟨c,hc,?_⟩
  intro i
  apply ContinuousLinearMap.coe_injective
  apply c.ext
  intro j
  change c.coord i (c j)=inverseCoordinate b v i (c j)
  simp only [Module.Basis.coord_apply,Module.Basis.repr_self]
  rw [hc j,inverseCoordinate_columns b v hu]
  simp [Finsupp.single_apply,eq_comm]

theorem inverseCoordinate_left_eigen (b : Module.Basis ι ℝ E) (v : ι → E)
    (hu : IsUnit (columnMap b v)) (A : E →L[ℝ] E) (μ : ι → ℝ)
    (he : ∀ j, A (v j)=μ j • v j) (i : ι) (x : E) :
    inverseCoordinate b v i (A x)=μ i*inverseCoordinate b v i x := by
  obtain ⟨c,hc,_⟩ := exists_basis_of_columnMap_isUnit b v hu
  have hh : (inverseCoordinate b v i).toLinearMap.comp A.toLinearMap=
      μ i • (inverseCoordinate b v i).toLinearMap := by
    apply c.ext
    intro j
    simp only [LinearMap.comp_apply,ContinuousLinearMap.coe_coe,hc,he,map_smul,
      smul_eq_mul,LinearMap.smul_apply,inverseCoordinate_columns b v hu]
    by_cases hij : i=j
    · simp [hij]
    · simp [hij]
  exact DFunLike.congr_fun hh x

/-- A continuous family of proposed eigenvectors starting at a basis gives
actual nearby bases, continuous inverse coordinates, and left eigenfunctionals.
The eigen equations remain explicit hypotheses. -/
theorem nearby_eigenbasis (b : Module.Basis ι ℝ E) (v : ℝ → ι → E)
    (hv : ∀ i, ContinuousAt (fun a => v a i) 0) (hzero : v 0=b)
    (A : ℝ → E →L[ℝ] E) (μ : ℝ → ι → ℝ)
    (he : ∀ᶠ a in 𝓝 (0:ℝ), ∀ i, A a (v a i)=μ a i • v a i) :
    (∀ i, ContinuousAt (fun a => inverseCoordinate b (v a) i) 0) ∧
    ∀ᶠ a in 𝓝 (0:ℝ), ∃ c : Module.Basis ι ℝ E,
      (∀ i, c i=v a i) ∧
      (∀ i, (c.coord i).toContinuousLinearMap=inverseCoordinate b (v a) i) ∧
      ∀ i x, inverseCoordinate b (v a) i (A a x)=μ a i*inverseCoordinate b (v a) i x := by
  refine ⟨inverseCoordinate_continuousAt b v hv hzero,?_⟩
  filter_upwards [eventually_columnMap_isUnit b v hv hzero,he] with a ha hea
  obtain ⟨c,hc,hcoord⟩ := exists_basis_of_columnMap_isUnit b (v a) ha
  exact ⟨c,hc,hcoord,inverseCoordinate_left_eigen b (v a) ha (A a) (μ a) hea⟩

/-- A smooth real operator family with a supplied simple real eigenbasis has
smooth eigenvalue and eigenvector branches forming actual nearby eigenbases.
Their inverse coordinate functionals are continuous and satisfy the actual
left eigenfunctional equations. -/
theorem smooth_eigenbasis (A : ℝ → E →L[ℝ] E)
    (hA : ContDiffAt ℝ ⊤ A 0) (b : Module.Basis ι ℝ E)
    (eig : ι → ℝ) (he : ∀ i, A 0 (b i)=eig i • b i)
    (hi : Function.Injective eig) :
    ∃ (μ : ℝ → ι → ℝ) (v : ℝ → ι → E),
      (∀ i, ContDiffAt ℝ ⊤ (fun a => μ a i) 0) ∧
      (∀ i, ContDiffAt ℝ ⊤ (fun a => v a i) 0) ∧
      μ 0=eig ∧ v 0=b ∧
      (∀ i, ContinuousAt (fun a => inverseCoordinate b (v a) i) 0) ∧
      ∀ᶠ a in 𝓝 (0:ℝ),
        (∀ i, A a (v a i)=μ a i • v a i ∧ b.coord i (v a i)=1) ∧
        ∃ c : Module.Basis ι ℝ E, (∀ i, c i=v a i) ∧
          (∀ i, (c.coord i).toContinuousLinearMap=inverseCoordinate b (v a) i) ∧
          ∀ i x, inverseCoordinate b (v a) i (A a x)=
            μ a i*inverseCoordinate b (v a) i x := by
  have hex (i : ι) := SimpleEigenpair.smooth_normalized_eigenpair A hA b eig he hi i
  choose μ v hμ hv hμ0 hv0 hres using hex
  have hzero : (fun i => v i 0)=b := funext hv0
  have hall : ∀ᶠ a in 𝓝 (0:ℝ),
      ∀ i, A a (v i a)=μ i a • v i a ∧ b.coord i (v i a)=1 :=
    Filter.eventually_all.mpr hres
  have hb := nearby_eigenbasis b (fun a i => v i a)
    (fun i => (hv i).continuousAt) hzero A (fun a i => μ i a)
    (hall.mono (fun _ ha i => (ha i).1))
  refine ⟨fun a i => μ i a,fun a i => v i a,hμ,hv,funext hμ0,hzero,hb.1,?_⟩
  filter_upwards [hall,hb.2] with a ha hba
  exact ⟨ha,hba⟩

end
end ThreeSitePhosphorylation.NearbyEigenbasis
