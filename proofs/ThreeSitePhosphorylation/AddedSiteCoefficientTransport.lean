import proofs.ThreeSitePhosphorylation.GenericClosedBranchCurvature
import proofs.ThreeSitePhosphorylation.GenericResolvents
import proofs.ThreeSitePhosphorylation.AddedSiteInverseTransport

/-! Exact transport of the normalized resolvent coefficient and of the kinetic
crossing pairing through a real face embedding `P`.

Convention (as consumed by `GenericClosedBranchCurvature`): for the critical
vector `v` with `p v=1`,
`A h11=B(v,conj v)`, `(2iw-A) h20=B(v,v)`,
`G=-2 p(B(v,h11))+p(B(conj v,h20))`.
No alternative sign or scaling of `h11`, `v` or `G` is used.

The parent spectral data are an actual complex eigenbasis. The child data are
only its genuine normalized left eigenfunctional and genuine injectivity of the
two child resolvent operators; the left functional is NOT assumed to vanish on
normal directions. -/
namespace ThreeSitePhosphorylation.AddedSiteCoefficientTransport
noncomputable section
open GenericComplexification GenericPeriodicKernel GenericTensorBilinear
open scoped BigOperators

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

/-! ### Complexified real embeddings -/

/-- Complexification of a rectangular real matrix. -/
def complexRect (P : Matrix ι' ι ℝ) : Matrix ι' ι ℂ := fun i j => (P i j : ℂ)

omit [DecidableEq ι] [DecidableEq ι'] [Fintype ι'] in
theorem complexRect_complexify (P : Matrix ι' ι ℝ) (y : ι → ℝ) :
    (complexRect P).mulVec (complexify y)=complexify (P.mulVec y) := by
  ext i
  simp [complexRect,Matrix.mulVec,dotProduct]

omit [DecidableEq ι] [DecidableEq ι'] [Fintype ι'] in
theorem complexRect_conjugate (P : Matrix ι' ι ℝ) (z : ι → ℂ) :
    (complexRect P).mulVec (conjugateVector z)=
      conjugateVector ((complexRect P).mulVec z) := by
  ext i
  simp [conjugateVector,complexRect,Matrix.mulVec,dotProduct]

omit [DecidableEq ι] [DecidableEq ι'] in
/-- A real matrix intertwining identity holds after complexification. -/
theorem complex_intertwining (A : Matrix ι ι ℝ) (A' : Matrix ι' ι' ℝ)
    (P : Matrix ι' ι ℝ) (h : A'*P=P*A) (z : ι → ℂ) :
    (complexMatrix A').mulVec ((complexRect P).mulVec z)=
      (complexRect P).mulVec ((complexMatrix A).mulVec z) := by
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]
  congr 1
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.mul_apply] at hij ⊢
  simp only [complexMatrix,complexRect]
  exact_mod_cast hij

omit [Fintype ι] in
theorem single_complexify (j : ι) :
    (Pi.single j (1:ℂ) : ι → ℂ)=complexify (Pi.single j (1:ℝ)) := by
  ext i
  by_cases h : i=j
  · subst h; simp
  · simp [h]

/-- A real bilinear intertwining identity holds for the complex bilinear
extensions, by complex bilinearity and agreement on the real standard basis. -/
theorem complex_tensor_intertwining (H : GenericQuadraticTensor.Tensor ι)
    (H' : GenericQuadraticTensor.Tensor ι') (P : Matrix ι' ι ℝ)
    (h : ∀ u v : ι → ℝ, realBilinear H' (P.mulVec u) (P.mulVec v)=
      P.mulVec (realBilinear H u v)) (u v : ι → ℂ) :
    complexBilinear H' ((complexRect P).mulVec u) ((complexRect P).mulVec v)=
      (complexRect P).mulVec (complexBilinear H u v) := by
  let j := (complexRect P).mulVecLin
  have hΦ : (complexBilinear H').compl₁₂ j j=(complexBilinear H).compr₂ j := by
    apply LinearMap.ext_basis (Pi.basisFun ℂ ι) (Pi.basisFun ℂ ι)
    intro a c
    simp only [LinearMap.compl₁₂_apply,LinearMap.compr₂_apply,Pi.basisFun_apply,
      Matrix.mulVecLin_apply,j,single_complexify,complexRect_complexify,
      ← complexify_realBilinear,h]
  exact DFunLike.congr_fun (DFunLike.congr_fun hΦ u) v

/-! ### Uniqueness of the normalized left eigenfunctional -/

variable {σ : Type*} [DecidableEq σ]

omit [DecidableEq ι] in
/-- For an actual complex eigenbasis with negative real stable roots and the
simple pair `±iw`, the normalized left eigenfunctional is unique. -/
theorem left_unique (A : Matrix ι ι ℝ) (w : ℝ) (hw : 0<w) (roots : σ → ℝ)
    (hn : ∀ i, roots i<0) (b : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ))
    (he : ∀ i, (complexMatrix A).mulVec (b i)=spectralValues roots w i • b i)
    (L : (ι → ℂ) →ₗ[ℂ] ℂ)
    (hL : ∀ y, L ((complexMatrix A).mulVec y)=(Complex.I*(w:ℂ))*L y)
    (hv : L (b (Sum.inr 0))=1) : L=b.coord (Sum.inr 0) := by
  apply b.ext
  intro i
  have h := hL (b i)
  rw [he i,map_smul,smul_eq_mul] at h
  have hz : (spectralValues roots w i-Complex.I*(w:ℂ))*L (b i)=0 := by
    linear_combination h
  rcases i with i | i
  · have hne : spectralValues roots w (Sum.inl i)-Complex.I*(w:ℂ) ≠ 0 := by
      intro h0
      have hr := congrArg Complex.re h0
      simp [spectralValues] at hr
      linarith [hn i]
    simp only [Module.Basis.coord_apply,Module.Basis.repr_self,Finsupp.single_apply,
      reduceCtorEq,if_false]
    exact (mul_eq_zero.mp hz).resolve_left hne
  · fin_cases i
    · simpa [Module.Basis.coord_apply,Module.Basis.repr_self] using hv
    · have hne : spectralValues roots w (Sum.inr 1)-Complex.I*(w:ℂ) ≠ 0 := by
        intro h0
        have hi := congrArg Complex.im h0
        simp [spectralValues] at hi
        linarith
      simp only [Fin.mk_one,Module.Basis.coord_apply,Module.Basis.repr_self,
        Finsupp.single_apply,Sum.inr.injEq,Fin.one_eq_zero_iff]
      simpa using (mul_eq_zero.mp hz).resolve_left hne

omit [DecidableEq ι] [DecidableEq ι'] in
/-- The actual child left functional restricts to the parent functional
(step 3). Its values on normal directions are unrestricted. -/
theorem left_restriction (A : Matrix ι ι ℝ) (A' : Matrix ι' ι' ℝ)
    (P : Matrix ι' ι ℝ) (hA : A'*P=P*A) (w : ℝ) (hw : 0<w) (roots : σ → ℝ)
    (hn : ∀ i, roots i<0) (b : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ))
    (he : ∀ i, (complexMatrix A).mulVec (b i)=spectralValues roots w i • b i)
    (p : (ι → ℂ) →ₗ[ℂ] ℂ)
    (hp : ∀ y, p ((complexMatrix A).mulVec y)=(Complex.I*(w:ℂ))*p y)
    (hpv : p (b (Sum.inr 0))=1)
    (p' : (ι' → ℂ) →ₗ[ℂ] ℂ)
    (hp' : ∀ y, p' ((complexMatrix A').mulVec y)=(Complex.I*(w:ℂ))*p' y)
    (hp'v : p' ((complexRect P).mulVec (b (Sum.inr 0)))=1) (y : ι → ℂ) :
    p' ((complexRect P).mulVec y)=p y := by
  let L := p'.comp (complexRect P).mulVecLin
  have hL : ∀ z, L ((complexMatrix A).mulVec z)=(Complex.I*(w:ℂ))*L z := by
    intro z
    simp only [L,LinearMap.comp_apply,Matrix.mulVecLin_apply]
    rw [← complex_intertwining A A' P hA,hp']
  have h1 := left_unique A w hw roots hn b he L hL hp'v
  have h2 := left_unique A w hw roots hn b he p hp hpv
  exact (LinearMap.congr_fun h1 y).trans (LinearMap.congr_fun h2 y).symm

/-! ### Coefficient, resolvent and crossing transport -/

/-- The normalized resolvent coefficient in the exact curvature convention. -/
def coefficient (p : (ι → ℂ) →ₗ[ℂ] ℂ) (T : GenericQuadraticTensor.Tensor ι)
    (v h11 h20 : ι → ℂ) : ℂ :=
  -2*p (complexBilinear T v h11)+p (complexBilinear T (conjugateVector v) h20)

omit [DecidableEq σ] in
theorem branchCoefficient_eq {A0 D : Matrix ι ι ℝ} {H : ℝ → GenericQuadraticTensor.Tensor ι}
    {r w : ℝ} {v : ι → ℂ}
    (C : GenericClosedPaths.ClosedPathFamily A0 D (GenericQuadraticTensor.pathField H) r w v)
    (h11 h20 : ι → ℂ) :
    GenericClosedBranchCurvature.branchCoefficient C h11 h20=coefficient C.left (H r) v h11 h20 :=
  rfl

omit [DecidableEq σ] in
theorem coefficient_transport (T : GenericQuadraticTensor.Tensor ι)
    (T' : GenericQuadraticTensor.Tensor ι') (P : Matrix ι' ι ℝ)
    (hT : ∀ u v : ι → ℝ, realBilinear T' (P.mulVec u) (P.mulVec v)=
      P.mulVec (realBilinear T u v))
    (p : (ι → ℂ) →ₗ[ℂ] ℂ) (p' : (ι' → ℂ) →ₗ[ℂ] ℂ)
    (hres : ∀ y, p' ((complexRect P).mulVec y)=p y) (v h11 h20 : ι → ℂ) :
    coefficient p' T' ((complexRect P).mulVec v) ((complexRect P).mulVec h11)
      ((complexRect P).mulVec h20)=coefficient p T v h11 h20 := by
  unfold coefficient
  rw [← complexRect_conjugate,complex_tensor_intertwining T T' P hT,
    complex_tensor_intertwining T T' P hT,hres,hres]

omit [DecidableEq σ] in
/-- The embedded parent resolvent solutions solve the child equations. -/
theorem resolvent_equations_transport (A : Matrix ι ι ℝ) (A' : Matrix ι' ι' ℝ)
    (P : Matrix ι' ι ℝ) (hA : A'*P=P*A) (T : GenericQuadraticTensor.Tensor ι)
    (T' : GenericQuadraticTensor.Tensor ι')
    (hT : ∀ u v : ι → ℝ, realBilinear T' (P.mulVec u) (P.mulVec v)=
      P.mulVec (realBilinear T u v))
    (w : ℝ) (v h11 h20 : ι → ℂ)
    (h11eq : (complexMatrix A).mulVec h11=complexBilinear T v (conjugateVector v))
    (h20eq : (2*Complex.I*(w:ℂ)) • h20-(complexMatrix A).mulVec h20=complexBilinear T v v) :
    (complexMatrix A').mulVec ((complexRect P).mulVec h11)=
      complexBilinear T' ((complexRect P).mulVec v)
        (conjugateVector ((complexRect P).mulVec v)) ∧
    (2*Complex.I*(w:ℂ)) • ((complexRect P).mulVec h20)-
      (complexMatrix A').mulVec ((complexRect P).mulVec h20)=
      complexBilinear T' ((complexRect P).mulVec v) ((complexRect P).mulVec v) := by
  constructor
  · rw [complex_intertwining A A' P hA,h11eq,← complexRect_conjugate,
      complex_tensor_intertwining T T' P hT]
  · rw [complex_intertwining A A' P hA,complex_tensor_intertwining T T' P hT,← h20eq,
      Matrix.mulVec_sub,Matrix.mulVec_smul]

omit [DecidableEq σ] in
/-- Any genuine child resolvent solution is the embedded parent solution. -/
theorem child_resolvents_unique (A : Matrix ι ι ℝ) (A' : Matrix ι' ι' ℝ)
    (P : Matrix ι' ι ℝ) (hA : A'*P=P*A) (T : GenericQuadraticTensor.Tensor ι)
    (T' : GenericQuadraticTensor.Tensor ι')
    (hT : ∀ u v : ι → ℝ, realBilinear T' (P.mulVec u) (P.mulVec v)=
      P.mulVec (realBilinear T u v))
    (w : ℝ) (v h11 h20 : ι → ℂ)
    (h11eq : (complexMatrix A).mulVec h11=complexBilinear T v (conjugateVector v))
    (h20eq : (2*Complex.I*(w:ℂ)) • h20-(complexMatrix A).mulVec h20=complexBilinear T v v)
    (hA' : Function.Injective (complexMatrix A').mulVecLin)
    (hS' : Function.Injective ((2*Complex.I*(w:ℂ)) •
      (LinearMap.id : (ι' → ℂ) →ₗ[ℂ] (ι' → ℂ))-(complexMatrix A').mulVecLin))
    (k11 k20 : ι' → ℂ)
    (k11eq : (complexMatrix A').mulVec k11=
      complexBilinear T' ((complexRect P).mulVec v) (conjugateVector ((complexRect P).mulVec v)))
    (k20eq : (2*Complex.I*(w:ℂ)) • k20-(complexMatrix A').mulVec k20=
      complexBilinear T' ((complexRect P).mulVec v) ((complexRect P).mulVec v)) :
    k11=(complexRect P).mulVec h11 ∧ k20=(complexRect P).mulVec h20 := by
  obtain ⟨e11,e20⟩ := resolvent_equations_transport A A' P hA T T' hT w v h11 h20 h11eq h20eq
  constructor
  · apply hA'
    simp only [Matrix.mulVecLin_apply]
    rw [k11eq,e11]
  · apply hS'
    simp only [LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,
      Matrix.mulVecLin_apply]
    rw [k20eq,e20]

omit [DecidableEq σ] [DecidableEq ι] [DecidableEq ι'] in
/-- Genuine inverse existence for the child from an actual child eigenbasis
(B's supplier), and restriction of the genuine inverses (step 2). -/
theorem genuine_resolvent_transport [Fintype σ] {σ' : Type*} [Fintype σ'] (A : Matrix ι ι ℝ) (A' : Matrix ι' ι' ℝ)
    (P : Matrix ι' ι ℝ) (hA : A'*P=P*A) (w : ℝ) (hw : 0<w)
    (roots : σ → ℝ) (hn : ∀ i, roots i<0) (b : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ))
    (he : ∀ i, (complexMatrix A).mulVec (b i)=spectralValues roots w i • b i)
    (roots' : σ' → ℝ) (hn' : ∀ i, roots' i<0)
    (b' : Module.Basis (σ' ⊕ Fin 2) ℂ (ι' → ℂ))
    (he' : ∀ i, (complexMatrix A').mulVec (b' i)=spectralValues roots' w i • b' i) :
    ∃ (I0 I2 : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)) (J0 J2 : (ι' → ℂ) ≃ₗ[ℂ] (ι' → ℂ)),
      (∀ u, (complexMatrix A).mulVec (I0 u)=u) ∧
      (∀ u, (2*Complex.I*(w:ℂ)) • I2 u-(complexMatrix A).mulVec (I2 u)=u) ∧
      (∀ u, (complexMatrix A').mulVec (J0 u)=u) ∧
      (∀ u, (2*Complex.I*(w:ℂ)) • J2 u-(complexMatrix A').mulVec (J2 u)=u) ∧
      (∀ u, J0 ((complexRect P).mulVec u)=(complexRect P).mulVec (I0 u)) ∧
      (∀ u, J2 ((complexRect P).mulVec u)=(complexRect P).mulVec (I2 u)) ∧
      Function.Injective (complexMatrix A').mulVecLin ∧
      Function.Injective ((2*Complex.I*(w:ℂ)) •
        (LinearMap.id : (ι' → ℂ) →ₗ[ℂ] (ι' → ℂ))-(complexMatrix A').mulVecLin) := by
  obtain ⟨hB0,hB2⟩ := GenericResolvents.resolvents_bijective (complexMatrix A).mulVecLin
    w roots b hn hw he
  obtain ⟨hC0,hC2⟩ := GenericResolvents.resolvents_bijective (complexMatrix A').mulVecLin
    w roots' b' hn' hw he'
  let e0 := LinearEquiv.ofBijective _ hB0
  let e2 := LinearEquiv.ofBijective _ hB2
  let f0 := LinearEquiv.ofBijective _ hC0
  let f2 := LinearEquiv.ofBijective _ hC2
  have hinter (u : ι → ℂ) : (complexMatrix A').mulVecLin ((complexRect P).mulVecLin u)=
      (complexRect P).mulVecLin ((complexMatrix A).mulVecLin u) :=
    complex_intertwining A A' P hA u
  refine ⟨e0.symm,e2.symm,f0.symm,f2.symm,?_,?_,?_,?_,?_,?_,hC0.1,hC2.1⟩
  · intro u; exact e0.apply_symm_apply u
  · intro u; exact e2.apply_symm_apply u
  · intro u; exact f0.apply_symm_apply u
  · intro u; exact f2.apply_symm_apply u
  · intro u
    exact AddedSiteInverseTransport.inverse_transport _ e0.symm _ f0.symm
      (complexRect P).mulVecLin hinter (fun x => e0.apply_symm_apply x)
      (fun y => f0.apply_symm_apply y) hC0.1 u
  · intro u
    exact AddedSiteInverseTransport.inverse_shift_transport (complexMatrix A).mulVecLin
      (complexMatrix A').mulVecLin (complexRect P).mulVecLin hinter (2*Complex.I*(w:ℂ))
      e2.symm f2.symm (fun x => e2.apply_symm_apply x) (fun y => f2.apply_symm_apply y)
      hC2.1 u

/-- Exact zero-load equality of the normalized coefficient and of the kinetic
crossing pairing (step 4), for the actual parent closed family `C` and ANY child
closed family `C'` on the embedded critical vector, with ANY genuine child
resolvent solutions. -/
theorem zero_load_transport {A0 D : Matrix ι ι ℝ} {H : ℝ → GenericQuadraticTensor.Tensor ι}
    {A0' D' : Matrix ι' ι' ℝ} {H' : ℝ → GenericQuadraticTensor.Tensor ι'}
    (P : Matrix ι' ι ℝ) {r w : ℝ} (hw : 0<w) (roots : σ → ℝ) (hn : ∀ i, roots i<0)
    (b : Module.Basis (σ ⊕ Fin 2) ℂ (ι → ℂ))
    (he : ∀ i, (complexMatrix (A0+r • D)).mulVec (b i)=spectralValues roots w i • b i)
    (hA : (A0'+r • D')*P=P*(A0+r • D)) (hD : D'*P=P*D)
    (hT : ∀ u v : ι → ℝ, realBilinear (H' r) (P.mulVec u) (P.mulVec v)=
      P.mulVec (realBilinear (H r) u v))
    (C : GenericClosedPaths.ClosedPathFamily A0 D (GenericQuadraticTensor.pathField H) r w
      (b (Sum.inr 0)))
    (C' : GenericClosedPaths.ClosedPathFamily A0' D' (GenericQuadraticTensor.pathField H') r w
      ((complexRect P).mulVec (b (Sum.inr 0))))
    (h11 h20 : ι → ℂ)
    (h11eq : (complexMatrix (A0+r • D)).mulVec h11=
      complexBilinear (H r) (b (Sum.inr 0)) (conjugateVector (b (Sum.inr 0))))
    (h20eq : (2*Complex.I*(w:ℂ)) • h20-(complexMatrix (A0+r • D)).mulVec h20=
      complexBilinear (H r) (b (Sum.inr 0)) (b (Sum.inr 0)))
    (hA' : Function.Injective (complexMatrix (A0'+r • D')).mulVecLin)
    (hS' : Function.Injective ((2*Complex.I*(w:ℂ)) •
      (LinearMap.id : (ι' → ℂ) →ₗ[ℂ] (ι' → ℂ))-(complexMatrix (A0'+r • D')).mulVecLin))
    (k11 k20 : ι' → ℂ)
    (k11eq : (complexMatrix (A0'+r • D')).mulVec k11=
      complexBilinear (H' r) ((complexRect P).mulVec (b (Sum.inr 0)))
        (conjugateVector ((complexRect P).mulVec (b (Sum.inr 0)))))
    (k20eq : (2*Complex.I*(w:ℂ)) • k20-(complexMatrix (A0'+r • D')).mulVec k20=
      complexBilinear (H' r) ((complexRect P).mulVec (b (Sum.inr 0)))
        ((complexRect P).mulVec (b (Sum.inr 0)))) :
    GenericClosedBranchCurvature.branchCoefficient C' k11 k20=
        GenericClosedBranchCurvature.branchCoefficient C h11 h20 ∧
      C'.left ((complexMatrix D').mulVec ((complexRect P).mulVec (b (Sum.inr 0))))=
        C.left ((complexMatrix D).mulVec (b (Sum.inr 0))) := by
  have hres (y : ι → ℂ) : C'.left ((complexRect P).mulVec y)=C.left y :=
    left_restriction (A0+r • D) (A0'+r • D') P hA w hw roots hn b he C.left C.left_eigen
      C.left_normalized C'.left C'.left_eigen C'.left_normalized y
  obtain ⟨hk11,hk20⟩ := child_resolvents_unique (A0+r • D) (A0'+r • D') P hA (H r) (H' r) hT
    w (b (Sum.inr 0)) h11 h20 h11eq h20eq hA' hS' k11 k20 k11eq k20eq
  refine ⟨?_,?_⟩
  · rw [branchCoefficient_eq,branchCoefficient_eq,hk11,hk20]
    exact coefficient_transport (H r) (H' r) P hT C.left C'.left hres _ _ _
  · rw [complex_intertwining D D' P hD,hres]

end
end ThreeSitePhosphorylation.AddedSiteCoefficientTransport
