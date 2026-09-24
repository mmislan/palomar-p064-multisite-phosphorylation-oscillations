import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

namespace ThreeSitePhosphorylation.SimpleComplexEigenpair
noncomputable section
open scoped Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℂ E] [Fintype ι] in
theorem basis_coordinate_eigen (A : E →ₗ[ℂ] E) (b : Module.Basis ι ℂ E)
    (eig : ι → ℂ) (he : ∀ i, A (b i)=eig i • b i) (i : ι) (v : E) :
    b.coord i (A v)=eig i*b.coord i v := by
  have hh : (b.coord i).comp A=eig i • b.coord i := by
    apply b.ext
    intro j
    by_cases hij : i=j
    · subst j
      simp [he,Module.Basis.coord_apply]
    · simp [he,Module.Basis.coord_apply,hij]
  exact DFunLike.congr_fun hh v

def eigenpairLinear (A : E →ₗ[ℂ] E) (b : Module.Basis ι ℂ E)
    (eig : ℂ) (i : ι) : (E × ℂ) →ₗ[ℂ] (E × ℂ) where
  toFun z := (A z.1-eig • z.1-z.2 • b i,b.coord i z.1)
  map_add' x y := by
    apply Prod.ext
    · simp only [Prod.fst_add,Prod.snd_add,map_add,smul_add,add_smul]
      module
    · simp
  map_smul' c z := by
    apply Prod.ext
    · change A (c • z.1)-eig • (c • z.1)-(c*z.2) • b i=
        c • (A z.1-eig • z.1-z.2 • b i)
      rw [map_smul]
      module
    · simp

omit [Fintype ι] in
/-- The normalized eigenpair derivative is invertible at a simple member of
a supplied complex eigenbasis. This is structural, with no determinant expansion. -/
theorem eigenpairLinear_bijective (A : E →ₗ[ℂ] E) (b : Module.Basis ι ℂ E)
    (eig : ι → ℂ) (he : ∀ i, A (b i)=eig i • b i)
    (i : ι) (hi : ∀ j, j≠i → eig j≠eig i) :
    Function.Bijective (eigenpairLinear A b (eig i) i) := by
  have hk : ∀ z, eigenpairLinear A b (eig i) i z=0 → z=0 := by
    intro z hz
    have hA : A z.1-eig i • z.1-z.2 • b i=0 := congrArg Prod.fst hz
    have hcoord : b.coord i z.1=0 := congrArg Prod.snd hz
    have hs : z.2=0 := by
      have hh := congrArg (b.coord i) hA
      simp only [map_sub,map_smul,map_zero,smul_eq_mul,
        basis_coordinate_eigen A b eig he] at hh
      simpa [Module.Basis.coord_apply] using hh
    have hv : z.1=0 := by
      apply b.repr.injective
      ext j
      change b.coord j z.1=b.coord j 0
      rw [map_zero]
      by_cases hji : j=i
      · simpa [hji] using hcoord
      · have hh := congrArg (b.coord j) hA
        simp only [map_sub,map_smul,map_zero,smul_eq_mul,
          basis_coordinate_eigen A b eig he,hs,zero_mul,sub_zero] at hh
        have hd : eig j-eig i ≠ 0 := sub_ne_zero.mpr (hi j hji)
        apply (mul_eq_zero.mp (show (eig j-eig i)*b.coord j z.1=0 by
          linear_combination hh)).resolve_left hd
    exact Prod.ext hv hs
  have hinj := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hk)
  exact ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

def eigenpairResidual (A : P → E →L[ℂ] E) (b : Module.Basis ι ℂ E)
    (i : ι) (d : P × (E × ℂ)) : E × ℂ :=
  (A d.1 d.2.1-d.2.2 • d.2.1,b.coord i d.2.1-1)

omit [Fintype ι] [DecidableEq ι] [CompleteSpace P] [FiniteDimensional ℝ E] in
theorem eigenpairResidual_smooth (A : P → E →L[ℂ] E)
    (hA : ContDiffAt ℝ ⊤ A 0) (b : Module.Basis ι ℂ E) (i : ι) (z : E × ℂ) :
    ContDiffAt ℝ ⊤ (eigenpairResidual A b i) (0,z) := by
  have ha : ContDiffAt ℝ ⊤ (fun d : P × (E × ℂ) => A d.1) (0,z) :=
    ContDiffAt.comp (f := fun d : P × (E × ℂ) => d.1) (g := A) (0,z) hA contDiffAt_fst
  have hc : ContDiffAt ℝ ⊤ (fun d : P × (E × ℂ) => b.coord i d.2.1) (0,z) :=
    ContDiffAt.comp (f := fun d : P × (E × ℂ) => d.2.1)
      (g := ((b.coord i).toContinuousLinearMap.restrictScalars ℝ)) (0,z)
      ((b.coord i).toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt (contDiffAt_snd.fst)
  have har : ContDiffAt ℝ ⊤ (fun d : P × (E × ℂ) => (A d.1).restrictScalars ℝ) (0,z) :=
    (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).contDiff.contDiffAt.comp (0,z) ha
  exact ((har.clm_apply contDiffAt_snd.fst).sub
    (contDiffAt_snd.snd.smul contDiffAt_snd.fst)).prodMk (hc.sub contDiffAt_const)

omit [Fintype ι] [DecidableEq ι] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] in
theorem eigenpairResidual_slice_derivative (A : P → E →L[ℂ] E)
    (b : Module.Basis ι ℂ E) (eig : ℂ) (i : ι) :
    HasFDerivAt (fun z : E × ℂ => eigenpairResidual A b i (0,z))
      (eigenpairLinear (A 0).toLinearMap b eig i).toContinuousLinearMap (b i,eig) := by
  let fstL := ContinuousLinearMap.fst ℂ E ℂ
  let sndL := ContinuousLinearMap.snd ℂ E ℂ
  have ha := (A 0).hasFDerivAt.comp (b i,eig) fstL.hasFDerivAt
  have hm := (sndL.hasFDerivAt (x := (b i,eig))).smul (fstL.hasFDerivAt (x := (b i,eig)))
  have hc := ((b.coord i).toContinuousLinearMap.hasFDerivAt.comp (b i,eig)
    fstL.hasFDerivAt).sub_const (1:ℂ)
  convert (ha.sub hm).prodMk hc using 1
  apply ContinuousLinearMap.ext
  intro y
  apply Prod.ext
  · change A 0 y.1-eig • y.1-y.2 • b i=
      A 0 y.1-(eig • y.1+y.2 • b i)
    module
  · rfl

omit [Fintype ι] in
/-- A simple eigenvalue from a supplied complex eigenbasis continues to an
actual normalized real-smooth complex eigenpair. No determinant expansion is used. -/
theorem smooth_normalized_eigenpair (A : P → E →L[ℂ] E)
    (hA : ContDiffAt ℝ ⊤ A 0) (b : Module.Basis ι ℂ E)
    (eig : ι → ℂ) (he : ∀ j, A 0 (b j)=eig j • b j)
    (i : ι) (hi : ∀ j, j≠i → eig j≠eig i) :
    ∃ (μ : P → ℂ) (v : P → E),
      ContDiffAt ℝ ⊤ μ 0 ∧ ContDiffAt ℝ ⊤ v 0 ∧
      μ 0=eig i ∧ v 0=b i ∧
      (∀ᶠ a in 𝓝 (0:P), A a (v a)=μ a • v a ∧ b.coord i (v a)=1) ∧
      ∀ᶠ d in 𝓝 ((0:P),(b i,eig i)),
        (A d.1 d.2.1=d.2.2 • d.2.1 ∧ b.coord i d.2.1=1) ↔
          (v d.1,μ d.1)=d.2 := by
  let F := eigenpairResidual A b i
  let z0 : E × ℂ := (b i,eig i)
  let L := (eigenpairLinear (A 0).toLinearMap b (eig i) i).toContinuousLinearMap.restrictScalars ℝ
  have hs : ContDiffAt ℝ ⊤ F (0,z0) := eigenpairResidual_smooth A hA b i z0
  have hpart : fderiv ℝ F (0,z0) ∘L ContinuousLinearMap.inr ℝ P (E × ℂ)=L := by
    have hd : HasFDerivAt (fun z : E × ℂ => ((0:P),z))
        (ContinuousLinearMap.inr ℝ P (E × ℂ)) z0 := by
      convert (hasFDerivAt_const (0:P) z0).prodMk (hasFDerivAt_id z0) using 1
    have hc := (hs.differentiableAt (by simp)).hasFDerivAt.comp z0 hd
    exact hc.unique ((eigenpairResidual_slice_derivative A b (eig i) i).restrictScalars ℝ)
  have hInv : (fderiv ℝ F (0,z0) ∘L ContinuousLinearMap.inr ℝ P (E × ℂ)).IsInvertible := by
    rw [hpart]
    have hb := eigenpairLinear_bijective (A 0).toLinearMap b eig he i hi
    obtain ⟨u,hu⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr (show Function.Bijective L from hb)
    exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ (E × ℂ) u,hu⟩
  have hzero : F (0,z0)=0 := by
    simp [F,z0,eigenpairResidual,he,Module.Basis.coord_apply]
  let g := hs.implicitFunction (by simp) hInv
  have hg : ContDiffAt ℝ ⊤ g 0 := hs.contDiffAt_implicitFunction (by simp) hInv
  have hg0 : g 0=z0 := hs.implicitFunction_apply_self (by simp) hInv
  have hge : ∀ᶠ a in 𝓝 (0:P), F (a,g a)=0 := by
    simpa only [hzero] using hs.eventually_apply_implicitFunction (by simp) hInv
  refine ⟨fun a => (g a).2,fun a => (g a).1,hg.snd,hg.fst,
    congrArg Prod.snd hg0,congrArg Prod.fst hg0,?_⟩
  constructor
  · filter_upwards [hge] with a ha
    exact ⟨sub_eq_zero.mp (congrArg Prod.fst ha),sub_eq_zero.mp (congrArg Prod.snd ha)⟩
  · have hloc := hs.eventually_apply_eq_iff_implicitFunction (by simp) hInv
    filter_upwards [hloc] with d hd
    simpa only [hzero,F,eigenpairResidual,Prod.mk_eq_zero,sub_eq_zero,Prod.eta] using hd

end
end ThreeSitePhosphorylation.SimpleComplexEigenpair
