import proofs.ThreeSitePhosphorylation.AddedSiteSourceMatrix
import proofs.ThreeSitePhosphorylation.CriticalSpectrum
import proofs.ThreeSitePhosphorylation.NormalEigenbasis
import proofs.ThreeSitePhosphorylation.UpperTriangularEigenbasis
import proofs.ThreeSitePhosphorylation.RealResolventSolution

/-! The complete complex eigenbasis of the actual zero-load added-site source
at the parent critical parameter. The complex upper-right coupling is the
actual derived block (no vanishing assumption); new columns are obtained from
the explicit parent-resolvent shear. Stable columns are proved real. -/
namespace ThreeSitePhosphorylation.AddedSiteZeroLoadBasis
noncomputable section
open PhosphorylationSharpness MultisiteChart MultisiteSource MultisiteCoordinates
open MultisiteTensor ScaledJointSource ScaledNormalJacobian ScaledNormalSpectrum
open GenericComplexification AddedSiteSourceMatrix CriticalSpectrum
set_option maxHeartbeats 800000

section Split
variable {n : ℕ}

theorem complexify_siteEquiv (u : CoordinateState n) (z : Fin 3 → ℝ) :
    complexify (siteEquiv ℝ n (u,z)) = siteEquiv ℂ n (complexify u,complexify z) := by
  funext i
  rcases i with i | i | i <;> refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [siteEmbedFun]

theorem conjugate_siteEquiv (u : CoordinateIndex n → ℂ) (z : Fin 3 → ℂ) :
    conjugateVector (siteEquiv ℂ n (u,z)) =
      siteEquiv ℂ n (conjugateVector u,conjugateVector z) := by
  funext i
  rcases i with i | i | i <;> refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [siteEmbedFun,conjugateVector]

theorem conjugate_siteEquiv_symm (v : CoordinateIndex (n+1) → ℂ) :
    (siteEquiv ℂ n).symm (conjugateVector v) =
      (conjugateVector ((siteEquiv ℂ n).symm v).1,
        conjugateVector ((siteEquiv ℂ n).symm v).2) := by
  apply (siteEquiv ℂ n).injective
  rw [LinearEquiv.apply_symm_apply,← conjugate_siteEquiv,Prod.mk.eta,LinearEquiv.apply_symm_apply]

theorem conjugate_zero {ι : Type*} : conjugateVector (0 : ι → ℂ) = 0 := by
  funext i
  simp [conjugateVector]

theorem complex_decomposition {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    v = complexify (GenericComplexification.realPart v) +
      Complex.I • complexify (imagPart v) := by
  funext i
  apply Complex.ext <;>
    simp [GenericComplexification.realPart,imagPart]

/-- Complex-linear maps on a complexified product are fixed by real vectors. -/
theorem ext_complexified {ι ν M : Type*} [Fintype ι] [Fintype ν] [AddCommGroup M]
    [Module ℂ M] (f g : ((ι → ℂ) × (ν → ℂ)) →ₗ[ℂ] M)
    (h : ∀ a b, f (complexify a,complexify b) = g (complexify a,complexify b)) : f = g := by
  apply LinearMap.ext
  rintro ⟨u,z⟩
  have hw : ((u,z) : (ι → ℂ) × (ν → ℂ)) =
      (complexify (GenericComplexification.realPart u),
        complexify (GenericComplexification.realPart z)) +
      Complex.I • (complexify (imagPart u),complexify (imagPart z)) := by
    apply Prod.ext
    · exact complex_decomposition u
    · exact complex_decomposition z
  rw [hw,map_add,map_add,map_smul,map_smul,h,h]

end Split

section Operators
variable {n : ℕ} (k : ℝ → Rates n) (x : State n) (κ : ℝ)

def parentOp (r : ℝ) : (CoordinateIndex n → ℂ) →ₗ[ℂ] (CoordinateIndex n → ℂ) :=
  (complexMatrix (sourceMatrix (k r) x)).mulVecLin

def loadedOp (p : ℝ × ℝ) :
    (CoordinateIndex (n+1) → ℂ) →ₗ[ℂ] (CoordinateIndex (n+1) → ℂ) :=
  (complexMatrix (jointMatrix k x κ p)).mulVecLin

def normalOp : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) := (scaledBlock κ).mulVecLin

/-- The actual complexified zero-load source in split coordinates. -/
def splitOp (r : ℝ) :
    ((CoordinateIndex n → ℂ) × (Fin 3 → ℂ)) →ₗ[ℂ]
      ((CoordinateIndex n → ℂ) × (Fin 3 → ℂ)) :=
  (siteEquiv ℂ n).symm.toLinearMap ∘ₗ loadedOp k x κ (0,r) ∘ₗ (siteEquiv ℂ n).toLinearMap

/-- The actual complex upper-right coupling. -/
def coupling (r : ℝ) : (Fin 3 → ℂ) →ₗ[ℂ] (CoordinateIndex n → ℂ) :=
  LinearMap.fst ℂ _ _ ∘ₗ splitOp k x κ r ∘ₗ LinearMap.inr ℂ _ _

theorem loadedOp_siteEquiv (r : ℝ) (w : (CoordinateIndex n → ℂ) × (Fin 3 → ℂ)) :
    loadedOp k x κ (0,r) (siteEquiv ℂ n w) = siteEquiv ℂ n (splitOp k x κ r w) := by
  simp [splitOp]

theorem splitOp_real (r : ℝ) (hx : x.F ≠ 0) (a : CoordinateState n) (b : Fin 3 → ℝ) :
    splitOp k x κ r (complexify a,complexify b) =
      (complexify ((sourceMatrix (k r) x).mulVec a+upperCouplingCoordinates k x κ r b),
        complexify (κ • normalBlock b)) := by
  have h1 : loadedOp k x κ (0,r) (siteEquiv ℂ n (complexify a,complexify b)) =
      siteEquiv ℂ n (complexify ((sourceMatrix (k r) x).mulVec a+
        upperCouplingCoordinates k x κ r b),complexify (κ • normalBlock b)) := by
    rw [← complexify_siteEquiv,loadedOp,Matrix.mulVecLin_apply,← complexify_action,
      jointMatrix_zero_block k x κ r hx,complexify_siteEquiv]
  change (siteEquiv ℂ n).symm (loadedOp k x κ (0,r) (siteEquiv ℂ n _)) = _
  rw [h1,LinearEquiv.symm_apply_apply]

theorem normalOp_real (b : Fin 3 → ℝ) :
    normalOp κ (complexify b) = complexify (κ • normalBlock b) := by
  rw [normalOp,Matrix.mulVecLin_apply]
  exact NormalEigenbasis.scaledBlock_mulVec_ofReal κ b

theorem coupling_real (r : ℝ) (hx : x.F ≠ 0) (b : Fin 3 → ℝ) :
    coupling k x κ r (complexify b) = complexify (upperCouplingCoordinates k x κ r b) := by
  have h := splitOp_real k x κ r hx 0 b
  simp only [map_zero,Matrix.mulVec_zero,zero_add] at h
  change (splitOp k x κ r (0,complexify b)).1 = _
  rw [h]

/-- The actual zero-load complex source is block upper triangular, with the
parent source, the actual coupling, and the scaled normal block. -/
theorem splitOp_block (r : ℝ) (hx : x.F ≠ 0) :
    splitOp k x κ r =
      UpperTriangularEigenbasis.block (parentOp k x r) (coupling k x κ r) (normalOp κ) := by
  apply ext_complexified
  intro a b
  rw [splitOp_real k x κ r hx a b]
  change _ = (parentOp k x r (complexify a)+coupling k x κ r (complexify b),
    normalOp κ (complexify b))
  rw [coupling_real k x κ r hx,normalOp_real,parentOp,Matrix.mulVecLin_apply,
    ← complexify_action,map_add]

theorem parentOp_conj (r : ℝ) (v : CoordinateIndex n → ℂ) :
    parentOp k x r (conjugateVector v) = conjugateVector (parentOp k x r v) := by
  simp only [parentOp,Matrix.mulVecLin_apply]
  exact conjugate_action _ v

theorem loadedOp_conj (p : ℝ × ℝ) (v : CoordinateIndex (n+1) → ℂ) :
    loadedOp k x κ p (conjugateVector v) = conjugateVector (loadedOp k x κ p v) := by
  simp only [loadedOp,Matrix.mulVecLin_apply]
  exact conjugate_action _ v

theorem coupling_conj (r : ℝ) (z : Fin 3 → ℂ) :
    coupling k x κ r (conjugateVector z) = conjugateVector (coupling k x κ r z) := by
  change ((siteEquiv ℂ n).symm (loadedOp k x κ (0,r) (siteEquiv ℂ n (0,conjugateVector z)))).1 =
    conjugateVector ((siteEquiv ℂ n).symm (loadedOp k x κ (0,r) (siteEquiv ℂ n (0,z)))).1
  have h0 : ((0 : CoordinateIndex n → ℂ),conjugateVector z) =
      (conjugateVector 0,conjugateVector z) := by rw [conjugate_zero]
  rw [h0,← conjugate_siteEquiv,loadedOp_conj,conjugate_siteEquiv_symm]

end Operators

/-- Injectivity of a shift away from every eigenvalue of a full eigenbasis. -/
theorem shift_injective {E η : Type*} [AddCommGroup E] [Module ℂ E] [Fintype η]
    [DecidableEq η] (A : E →ₗ[ℂ] E) (b : Module.Basis η ℂ E) (eig : η → ℂ)
    (he : ∀ i, A (b i) = eig i • b i) (μ : ℂ) (hμ : ∀ i, μ ≠ eig i) :
    Function.Injective (fun v => μ • v - A v) := by
  have hker : ∀ v, μ • v - A v = 0 → v = 0 := by
    intro v hv
    apply b.repr.injective
    ext i
    have hc := congrArg (b.coord i) hv
    rw [map_sub,map_smul,UpperTriangularEigenbasis.coordinate_eigen A b eig he i,map_zero,
      smul_eq_mul,← sub_mul] at hc
    have hz := (mul_eq_zero.mp hc).resolve_left (sub_ne_zero.mpr (hμ i))
    simpa [Module.Basis.coord_apply] using hz
  intro v w hvw
  have h := hker (v-w) (by
    simp only at hvw
    rw [smul_sub,map_sub]
    rw [sub_sub_sub_comm,hvw,sub_self])
  exact sub_eq_zero.mp h

section Basis
variable {n : ℕ} {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Reorder so that new stable roots join the stable block. -/
def reorder (σ : Type*) : (σ ⊕ Fin 3) ⊕ Fin 2 ≃ (σ ⊕ Fin 2) ⊕ Fin 3 where
  toFun := Sum.elim (Sum.elim (fun s => Sum.inl (Sum.inl s)) Sum.inr)
    (fun j => Sum.inl (Sum.inr j))
  invFun := Sum.elim (Sum.elim (fun s => Sum.inl (Sum.inl s)) Sum.inr)
    (fun j => Sum.inl (Sum.inr j))
  left_inv i := by rcases i with (s | j) | j <;> rfl
  right_inv i := by rcases i with (s | j) | j <;> rfl

/-- Separating scale chosen from the actual parent stable roots. -/
def scale {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} (d : Data σ A) : ℝ :=
  separatingScale d.stable

variable (k : ℝ → Rates n) (x : State n)

omit [DecidableEq σ] in
theorem scale_pos (d : Data σ (sourceMatrix (k 0) x)) : 0 < scale d :=
  separatingScale_positive d.stable

omit [DecidableEq σ] in
theorem normal_ne_parent (d : Data σ (sourceMatrix (k 0) x)) (i : σ ⊕ Fin 2) (j : Fin 3) :
    (normalRoots (scale d) j : ℂ) ≠ eigenvalues d i := by
  rcases i with s | a
  · simp only [eigenvalues_inl]
    exact_mod_cast normalRoots_ne_parent d.stable j s
  · intro h
    have him := congrArg Complex.im h
    have hw := d.freq_pos
    fin_cases a <;> simp at him <;> linarith

/-- The explicit coupled basis in split coordinates. -/
def splitBasis (d : Data σ (sourceMatrix (k 0) x)) :
    Module.Basis ((σ ⊕ Fin 2) ⊕ Fin 3) ℂ ((CoordinateIndex n → ℂ) × (Fin 3 → ℂ)) :=
  UpperTriangularEigenbasis.coupledBasis (coupling k x (scale d) 0) d.basis
    NormalEigenbasis.complexBasis (eigenvalues d) (fun j => (normalRoots (scale d) j : ℂ))

/-- The complete basis of the actual zero-load (n+1)-site source. -/
def zeroBasis (d : Data σ (sourceMatrix (k 0) x)) :
    Module.Basis ((σ ⊕ Fin 3) ⊕ Fin 2) ℂ (CoordinateIndex (n+1) → ℂ) :=
  ((splitBasis k x d).map (siteEquiv ℂ n)).reindex (reorder σ).symm

omit [DecidableEq σ] in
theorem zeroBasis_apply (d : Data σ (sourceMatrix (k 0) x)) (i : (σ ⊕ Fin 3) ⊕ Fin 2) :
    zeroBasis k x d i = siteEquiv ℂ n (splitBasis k x d (reorder σ i)) := by
  simp [zeroBasis]

def zeroStable (d : Data σ (sourceMatrix (k 0) x)) : σ ⊕ Fin 3 → ℝ :=
  Sum.elim d.stable (normalRoots (scale d))

theorem zeroBasis_eigen (d : Data σ (sourceMatrix (k 0) x)) (hx : x.F ≠ 0)
    (i : (σ ⊕ Fin 3) ⊕ Fin 2) :
    loadedOp k x (scale d) (0,0) (zeroBasis k x d i) =
      Sum.elim (eigenvalues d) (fun j => (normalRoots (scale d) j : ℂ)) (reorder σ i) •
        zeroBasis k x d i := by
  rw [zeroBasis_apply,loadedOp_siteEquiv,splitOp_block k x (scale d) 0 hx,
    splitBasis,UpperTriangularEigenbasis.coupledBasis_eigen (parentOp k x 0)
      (coupling k x (scale d) 0) (normalOp (scale d)) d.basis NormalEigenbasis.complexBasis
      (eigenvalues d) (fun j => (normalRoots (scale d) j : ℂ))
      (fun i => by rw [parentOp]; exact eigen_lin d i)
      (fun j => NormalEigenbasis.complexBasis_eigen (scale d) j)
      (fun i j => normal_ne_parent k x d i j),map_smul]

omit [DecidableEq σ] in
theorem zeroBasis_old (d : Data σ (sourceMatrix (k 0) x)) (i : σ ⊕ Fin 2) :
    splitBasis k x d (Sum.inl i) = (d.basis i,0) :=
  UpperTriangularEigenbasis.coupledBasis_old _ _ _ _ _ i

omit [DecidableEq σ] in
theorem zeroBasis_new (d : Data σ (sourceMatrix (k 0) x)) (j : Fin 3) :
    splitBasis k x d (Sum.inr j) =
      (UpperTriangularEigenbasis.newUpper (coupling k x (scale d) 0) d.basis
        NormalEigenbasis.complexBasis (eigenvalues d)
        (fun j => (normalRoots (scale d) j : ℂ)) j,NormalEigenbasis.complexBasis j) :=
  UpperTriangularEigenbasis.coupledBasis_new _ _ _ _ _ j

theorem complexBasis_real (j : Fin 3) :
    conjugateVector (NormalEigenbasis.complexBasis j) = NormalEigenbasis.complexBasis j := by
  funext i
  exact NormalEigenbasis.complexBasis_conj j i

theorem newUpper_real (d : Data σ (sourceMatrix (k 0) x)) (j : Fin 3) :
    conjugateVector (UpperTriangularEigenbasis.newUpper (coupling k x (scale d) 0) d.basis
      NormalEigenbasis.complexBasis (eigenvalues d)
      (fun j => (normalRoots (scale d) j : ℂ)) j) =
    UpperTriangularEigenbasis.newUpper (coupling k x (scale d) 0) d.basis
      NormalEigenbasis.complexBasis (eigenvalues d)
      (fun j => (normalRoots (scale d) j : ℂ)) j := by
  have hA : ∀ i, parentOp k x 0 (d.basis i) = eigenvalues d i • d.basis i := by
    intro i
    rw [parentOp]
    exact eigen_lin d i
  exact RealResolventSolution.real_upper_column (parentOp k x 0) (coupling k x (scale d) 0)
    (normalRoots (scale d) j : ℂ) _ (NormalEigenbasis.complexBasis j)
    (parentOp_conj k x 0) (coupling_conj k x (scale d) 0) (by simp) (complexBasis_real j)
    (shift_injective (parentOp k x 0) d.basis (eigenvalues d) hA _
      (fun i => normal_ne_parent k x d i j))
    (UpperTriangularEigenbasis.newUpper_equation (parentOp k x 0) (coupling k x (scale d) 0)
      d.basis NormalEigenbasis.complexBasis (eigenvalues d)
      (fun j => (normalRoots (scale d) j : ℂ)) hA (fun i j => normal_ne_parent k x d i j) j)

/-- Spectral data of the actual zero-load (n+1)-site source at the parent
critical parameter. Every field is derived; none is assumed. -/
def zeroData (d : Data σ (sourceMatrix (k 0) x)) (hx : x.F ≠ 0) :
    Data (σ ⊕ Fin 3) (jointMatrix k x (scale d) (0,0)) where
  basis := zeroBasis k x d
  stable := zeroStable k x d
  freq := d.freq
  freq_pos := d.freq_pos
  stable_neg := by
    intro s
    rcases s with s | j
    · exact d.stable_neg s
    · exact normalRoots_negative _ (scale_pos k x d) j
  stable_injective := by
    intro s t hst
    rcases s with s | j <;> rcases t with t | l
    · exact congrArg Sum.inl (d.stable_injective hst)
    · exact absurd (show normalRoots (separatingScale d.stable) l = d.stable s from hst.symm)
        (normalRoots_ne_parent d.stable l s)
    · exact absurd (show normalRoots (separatingScale d.stable) j = d.stable t from hst)
        (normalRoots_ne_parent d.stable j t)
    · exact congrArg Sum.inr (normalRoots_injective _ (scale_pos k x d) hst)
  stable_eigen := by
    intro s
    have h := zeroBasis_eigen k x d hx (Sum.inl s)
    rw [loadedOp,Matrix.mulVecLin_apply] at h
    rw [h]
    rcases s with s | j <;> rfl
  critical_eigen := by
    have h := zeroBasis_eigen k x d hx (Sum.inr 0)
    rw [loadedOp,Matrix.mulVecLin_apply] at h
    exact h
  stable_real := by
    intro s
    rcases s with s | j
    · change conjugateVector (zeroBasis k x d (Sum.inl (Sum.inl s))) = _
      rw [zeroBasis_apply]
      change conjugateVector (siteEquiv ℂ n (splitBasis k x d (Sum.inl (Sum.inl s)))) =
        siteEquiv ℂ n (splitBasis k x d (Sum.inl (Sum.inl s)))
      rw [zeroBasis_old,conjugate_siteEquiv,d.stable_real,conjugate_zero]
    · change conjugateVector (zeroBasis k x d (Sum.inl (Sum.inr j))) = _
      rw [zeroBasis_apply]
      change conjugateVector (siteEquiv ℂ n (splitBasis k x d (Sum.inr j))) =
        siteEquiv ℂ n (splitBasis k x d (Sum.inr j))
      rw [zeroBasis_new,conjugate_siteEquiv,newUpper_real k x d,complexBasis_real]
  critical_pair := by
    change zeroBasis k x d (Sum.inr 1) = conjugateVector (zeroBasis k x d (Sum.inr 0))
    rw [zeroBasis_apply,zeroBasis_apply]
    change siteEquiv ℂ n (splitBasis k x d (Sum.inl (Sum.inr 1))) =
      conjugateVector (siteEquiv ℂ n (splitBasis k x d (Sum.inl (Sum.inr 0))))
    rw [zeroBasis_old,zeroBasis_old,conjugate_siteEquiv,d.critical_pair,conjugate_zero]

@[simp] theorem zeroData_basis (d : Data σ (sourceMatrix (k 0) x)) (hx : x.F ≠ 0) :
    (zeroData k x d hx).basis = zeroBasis k x d := rfl

omit [DecidableEq σ] in
/-- The continued critical vector at zero load is the embedded parent vector. -/
theorem zeroBasis_critical (d : Data σ (sourceMatrix (k 0) x)) :
    zeroBasis k x d (Sum.inr 0) = siteEquiv ℂ n (d.basis (Sum.inr 0),0) := by
  rw [zeroBasis_apply]
  exact congrArg (siteEquiv ℂ n) (zeroBasis_old k x d (Sum.inr 0))

omit [DecidableEq σ] in
/-- The actual normalized left functional restricts on the invariant face to
the parent normalized left functional. Its normal components are not assumed
to vanish. -/
theorem zeroBasis_coord_face (d : Data σ (sourceMatrix (k 0) x))
    (y : CoordinateIndex n → ℂ) :
    (zeroBasis k x d).coord (Sum.inr 0) (siteEquiv ℂ n (y,0)) =
      d.basis.coord (Sum.inr 0) y := by
  have h1 : (zeroBasis k x d).coord (Sum.inr 0) (siteEquiv ℂ n (y,0)) =
      (splitBasis k x d).repr (y,0) (Sum.inl (Sum.inr 0)) := by
    rw [Module.Basis.coord_apply,zeroBasis,Module.Basis.repr_reindex_apply,
      Module.Basis.map_repr,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
    rfl
  have hs : (UpperTriangularEigenbasis.shear (UpperTriangularEigenbasis.sylvesterMap
      (coupling k x (scale d) 0) d.basis NormalEigenbasis.complexBasis (eigenvalues d)
      (fun j => (normalRoots (scale d) j : ℂ)))).symm (y,0) = (y,0) := by
    change (y - _ , (0 : Fin 3 → ℂ)) = (y,0)
    simp
  have h2 : (splitBasis k x d).repr (y,0) (Sum.inl (Sum.inr 0)) =
      d.basis.repr y (Sum.inr 0) := by
    rw [splitBasis,UpperTriangularEigenbasis.coupledBasis,Module.Basis.map_repr,
      LinearEquiv.trans_apply,hs,Module.Basis.prod_repr_inl]
  rw [h1,h2,Module.Basis.coord_apply]

end Basis

end
end ThreeSitePhosphorylation.AddedSiteZeroLoadBasis
