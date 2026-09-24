import proofs.ThreeSitePhosphorylation.AddedSiteHopfStep
import proofs.ThreeSitePhosphorylation.MultisiteThreeSiteBridge
import proofs.ThreeSitePhosphorylation.AttractingLyapunovSource
import proofs.ThreeSitePhosphorylation.AttractingLeftUnique
import proofs.ThreeSitePhosphorylation.AttractingCrossing
import proofs.ThreeSitePhosphorylation.AttractingPairing

/-! Base case and induction for the strengthened all-site Hopf invariant.

The actual three-site witness A (`AttractingWitness.rates`, `AttractingWitness.state`)
is carried into the uniform `CoordinateIndex 3` chart by an explicit invertible real
matrix `chartMatrix`, which conjugates the literal centered chemical fields exactly.
Its verified Fin 9 eigenbasis, critical frequency, normalized left functional,
negative kinetic crossing and negative explicit Lyapunov coefficient are transported
through that conjugacy, giving `AddedSiteHopfStep.HopfInvariant` for the witness
family translated to its critical parameter. `AddedSiteHopfStep.hopf_iterate` then
gives the invariant for every number of sites `n ≥ 3`. -/
namespace ThreeSitePhosphorylation.AllSiteHopfInvariant
noncomputable section
open Filter
open scoped Topology
open MultisiteCoordinates MultisiteTensor CriticalSpectrum AddedSiteSpectralStep
open AddedSiteHopfStep GenericComplexification GenericTensorBilinear
open AddedSiteCoefficientTransport ScaledAffineFamily MultisiteThreeSiteBridge
set_option maxHeartbeats 1600000

/-! ### The witness family in the multisite record -/

/-- Witness-A rates in the multisite record, translated by the parameter `r0`. -/
def baseRates (r0 r : ℝ) : PhosphorylationSharpness.Rates 3 :=
  repackRates (AttractingWitness.rates (r0+r))

/-- The witness-A equilibrium in the multisite record. -/
def baseState : PhosphorylationSharpness.State 3 := repack AttractingWitness.state

theorem baseRates_zero (r0 : ℝ) : baseRates r0 0=repackRates (AttractingWitness.rates r0) := by
  rw [baseRates,add_zero]

/-- The kinetic slope of the witness family (only two entries move). -/
def baseSlope : PhosphorylationSharpness.Rates 3 :=
  repackRates (fun i => AttractingWitness.rates 1 i-AttractingWitness.rates 0 i)

theorem baseRates_affine (r0 r : ℝ) :
    baseRates r0 r=affineRates (repackRates (AttractingWitness.rates r0)) baseSlope r := by
  apply rates_ext <;> funext i <;> fin_cases i <;>
    simp [baseRates,baseSlope,affineRates,repackRates,AttractingWitness.rates] <;> ring

theorem affineRates_smooth {n : ℕ} (offset slope : PhosphorylationSharpness.Rates n) :
    MultisiteSmoothField.RatesSmooth (affineRates offset slope) := by
  refine ⟨fun i => ?_,fun i => ?_,fun i => ?_,fun i => ?_,fun i => ?_,fun i => ?_⟩
  · change ContDiff ℝ ⊤ fun p : ℝ => offset.a i+p*slope.a i
    fun_prop
  · change ContDiff ℝ ⊤ fun p : ℝ => offset.b i+p*slope.b i
    fun_prop
  · change ContDiff ℝ ⊤ fun p : ℝ => offset.c i+p*slope.c i
    fun_prop
  · change ContDiff ℝ ⊤ fun p : ℝ => offset.alpha i+p*slope.alpha i
    fun_prop
  · change ContDiff ℝ ⊤ fun p : ℝ => offset.beta i+p*slope.beta i
    fun_prop
  · change ContDiff ℝ ⊤ fun p : ℝ => offset.gamma i+p*slope.gamma i
    fun_prop

theorem base_equilibrium (s : ℝ) :
    PhosphorylationSharpness.Equilibrium (repackRates (AttractingWitness.rates s)) baseState := by
  have h := repack_field (AttractingWitness.rates s) AttractingWitness.state
  rw [AttractingWitness.equilibrium] at h
  refine ⟨fun i => ?_,?_,?_,fun i => ?_,fun i => ?_⟩
  · rw [baseState,← h]; fin_cases i <;> simp [repack]
  · rw [baseState,← h]; simp [repack]
  · rw [baseState,← h]; simp [repack]
  · rw [baseState,← h]; fin_cases i <;> simp [repack]
  · rw [baseState,← h]; fin_cases i <;> simp [repack]

/-! ### The explicit chart matrix between the two reduced coordinate systems -/

def rowS : Fin 3 → Fin 9 → ℝ :=
  ![![1,-1,0,0,-1,0,-1,0,0],![0,1,-1,0,0,-1,0,-1,0],![0,0,1,0,0,0,0,0,-1]]
def rowC : Fin 3 → Fin 9 → ℝ :=
  ![![0,0,0,1,0,0,0,0,0],![0,0,0,0,1,0,0,0,0],![0,0,0,0,0,1,0,0,0]]
def rowD : Fin 3 → Fin 9 → ℝ :=
  ![![0,0,0,0,0,0,1,0,0],![0,0,0,0,0,0,0,1,0],![0,0,0,0,0,0,0,0,1]]

/-- Witness reduced coordinates (cumulative substrate sums) to multisite coordinates. -/
def chartMatrix : Matrix (CoordinateIndex 3) (Fin 9) ℝ :=
  Matrix.of fun i j => Sum.elim rowS (Sum.elim rowC rowD) i j

def colRows : Fin 9 → CoordinateIndex 3 → ℝ :=
  ![Sum.elim ![1,1,1] (Sum.elim ![0,1,1] ![1,1,1]),
    Sum.elim ![0,1,1] (Sum.elim ![0,0,1] ![0,1,1]),
    Sum.elim ![0,0,1] (Sum.elim ![0,0,0] ![0,0,1]),
    Sum.elim ![0,0,0] (Sum.elim ![1,0,0] ![0,0,0]),
    Sum.elim ![0,0,0] (Sum.elim ![0,1,0] ![0,0,0]),
    Sum.elim ![0,0,0] (Sum.elim ![0,0,1] ![0,0,0]),
    Sum.elim ![0,0,0] (Sum.elim ![0,0,0] ![1,0,0]),
    Sum.elim ![0,0,0] (Sum.elim ![0,0,0] ![0,1,0]),
    Sum.elim ![0,0,0] (Sum.elim ![0,0,0] ![0,0,1])]

/-- The inverse chart matrix. -/
def inverseMatrix : Matrix (Fin 9) (CoordinateIndex 3) ℝ := Matrix.of fun j c => colRows j c

theorem chartMatrix_mul_inverse : chartMatrix*inverseMatrix=1 := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;> fin_cases i <;> fin_cases j <;>
    simp [chartMatrix,inverseMatrix,colRows,rowS,rowC,rowD,Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem inverse_mul_chartMatrix : inverseMatrix*chartMatrix=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartMatrix,inverseMatrix,colRows,rowS,rowC,rowD,Matrix.mul_apply,
      Fintype.sum_sum_type,Fin.sum_univ_succ]

theorem chartMatrix_mulVec (y : Fin 9 → ℝ) :
    chartMatrix.mulVec y=Sum.elim ![y 0-y 1-y 4-y 6,y 1-y 2-y 5-y 7,y 2-y 8]
      (Sum.elim ![y 3,y 4,y 5] ![y 6,y 7,y 8]) := by
  funext i
  rcases i with i | i | i <;> fin_cases i <;>
    simp [chartMatrix,rowS,rowC,rowD,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

/-- Multisite projection of a repacked state is the chart image of the witness projection. -/
theorem project_repack (Z : State) :
    toCoordinates 3 (MultisiteChart.project (repack Z))=chartMatrix.mulVec (project Z) := by
  rw [chartMatrix_mulVec]
  funext i
  rcases i with i | i | i <;> fin_cases i <;>
    simp [MultisiteChart.project,repack,project] <;> ring

theorem base_chart_point (y : Fin 9 → ℝ) :
    MultisiteChart.project baseState+fromCoordinates 3 (chartMatrix.mulVec y)=toMultisite y := by
  apply (coordinateEquiv 3).injective
  have h1 : coordinateEquiv 3 (toMultisite y)=
      chartMatrix.mulVec (project AttractingWitness.state+y) := by
    have hp := AttractingWitness.affineChart_project y
    rw [sub_eq_iff_eq_add'] at hp
    rw [← hp]
    exact project_repack _
  have h2 : coordinateEquiv 3 (MultisiteChart.project baseState)=
      chartMatrix.mulVec (project AttractingWitness.state) := project_repack _
  rw [h1,map_add,h2,Matrix.mulVec_add]
  congr 1
  exact (coordinateEquiv 3).apply_symm_apply _

theorem base_chart (y : Fin 9 → ℝ) :
    MultisiteChart.chart (PhosphorylationSharpness.totalE baseState)
      (PhosphorylationSharpness.totalF baseState) (PhosphorylationSharpness.totalS baseState)
      (MultisiteChart.project baseState+fromCoordinates 3 (chartMatrix.mulVec y))=
      repack (AttractingWitness.affineChart y) := by
  obtain ⟨he,hf,hs⟩ := repack_totals AttractingWitness.state
  rw [base_chart_point,baseState,he,hf,hs]
  exact chart_toMultisite y

/-- Exact conjugacy of the literal centered chemical fields in the two charts. -/
theorem base_conjugacy (s : ℝ) (y : Fin 9 → ℝ) :
    coordinateField (repackRates (AttractingWitness.rates s)) baseState (chartMatrix.mulVec y)=
      chartMatrix.mulVec (AttractingWitness.reduced s y) := by
  change toCoordinates 3 (MultisiteChart.project (PhosphorylationSharpness.field
      (repackRates (AttractingWitness.rates s))
      (MultisiteChart.chart (PhosphorylationSharpness.totalE baseState)
        (PhosphorylationSharpness.totalF baseState) (PhosphorylationSharpness.totalS baseState)
        (MultisiteChart.project baseState+fromCoordinates 3 (chartMatrix.mulVec y)))))=_
  rw [base_chart,← repack_field,project_repack]
  rfl

/-! ### Linear and quadratic parts -/

theorem hessian_add (r : ℝ) (x y : ReducedState) :
    AttractingWitness.hessian r (x+y)=AttractingWitness.hessian r x+AttractingWitness.hessian r y := by
  ext z i
  fin_cases i <;> simp [AttractingWitness.hessian,AttractingWitness.hessianRow] <;> ring

/-- The literal witness Hessian as a bilinear map. -/
def hessianBilinear (r : ℝ) : (Fin 9 → ℝ) →ₗ[ℝ] (Fin 9 → ℝ) →ₗ[ℝ] (Fin 9 → ℝ) :=
  LinearMap.mk₂ ℝ (fun x y => AttractingWitness.hessian r x y)
    (fun x y z => by dsimp only; rw [hessian_add,ContinuousLinearMap.add_apply])
    (fun c x y => by dsimp only; rw [AttractingWitness.hessian_smul,ContinuousLinearMap.smul_apply])
    (fun x y z => map_add _ y z)
    (fun c x y => map_smul _ c y)

@[simp] theorem hessianBilinear_apply (r : ℝ) (x y : Fin 9 → ℝ) :
    hessianBilinear r x y=AttractingWitness.hessian r x y := rfl

theorem base_separation (s : ℝ) (y : Fin 9 → ℝ) :
    (MultisiteTensor.sourceMatrix (repackRates (AttractingWitness.rates s)) baseState).mulVec
        (chartMatrix.mulVec y)=chartMatrix.mulVec (AttractingWitness.linearPart s y) ∧
      (1/2:ℝ) • realBilinear (sourceTensor (repackRates (AttractingWitness.rates s)))
        (chartMatrix.mulVec y) (chartMatrix.mulVec y)=
        chartMatrix.mulVec (AttractingWitness.quadraticPart s y) := by
  set A := MultisiteTensor.sourceMatrix (repackRates (AttractingWitness.rates s)) baseState
  set T := sourceTensor (repackRates (AttractingWitness.rates s))
  apply AddedSiteHessianTransport.quadratic_coefficients (0 : CoordinateState 3) _ _ 0
  intro t
  have h := base_conjugacy s (t • y)
  rw [coordinateField_equilibrium _ _ (base_equilibrium s),AttractingWitness.taylor_exact] at h
  have hq : AttractingWitness.quadraticPart s (t • y)=
      (t*t) • AttractingWitness.quadraticPart s y := by
    have h1 := AttractingWitness.hessian_diagonal s (t • y)
    rw [AttractingWitness.hessian_smul,ContinuousLinearMap.smul_apply,map_smul,
      AttractingWitness.hessian_diagonal,smul_smul,smul_comm (t*t) (2:ℝ)] at h1
    exact (smul_right_injective _ (two_ne_zero : (2:ℝ) ≠ 0) h1).symm
  have e1 : chartMatrix.mulVec (t • y)=t • chartMatrix.mulVec y := Matrix.mulVec_smul _ _ _
  have e2 : A.mulVec (t • chartMatrix.mulVec y)=t • A.mulVec (chartMatrix.mulVec y) :=
    Matrix.mulVec_smul _ _ _
  have e3 : realBilinear T (t • chartMatrix.mulVec y) (t • chartMatrix.mulVec y)=
      (t*t) • realBilinear T (chartMatrix.mulVec y) (chartMatrix.mulVec y) := by
    simp only [map_smul,LinearMap.smul_apply,smul_smul]
  have e4 : AttractingWitness.linearPart s (t • y)=t • AttractingWitness.linearPart s y :=
    map_smul _ _ _
  rw [e1,e2,e3,e4,hq,Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul] at h
  rw [zero_add,zero_add,smul_comm (t*t) (1/2:ℝ)]
  exact h

/-- Similarity of the actual source matrices through the chart matrix. -/
theorem base_similarity (s : ℝ) :
    MultisiteTensor.sourceMatrix (repackRates (AttractingWitness.rates s)) baseState*chartMatrix=
      chartMatrix*AttractingWitness.sourceMatrix s := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro y
  rw [Matrix.toLin'_apply,Matrix.toLin'_apply,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,
    AttractingWitness.sourceMatrix_action]
  exact (base_separation s y).1

theorem polarization {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (f g : V →ₗ[ℝ] V →ₗ[ℝ] W) (hf : ∀ u v, f u v=f v u) (hg : ∀ u v, g u v=g v u)
    (h : ∀ y, f y y=g y y) (u v : V) : f u v=g u v := by
  have hh := h (u+v)
  simp only [map_add,LinearMap.add_apply,h u,h v,hf v u,hg v u] at hh
  have e1 : g u u+f u v+(f u v+g v v)=(g u u+g v v)+(f u v+f u v) := by abel
  have e2 : g u u+g u v+(g u v+g v v)=(g u u+g v v)+(g u v+g u v) := by abel
  rw [e1,e2] at hh
  have h3 := add_left_cancel hh
  rw [← two_smul ℝ (f u v),← two_smul ℝ (g u v)] at h3
  exact smul_right_injective _ (two_ne_zero : (2:ℝ) ≠ 0) h3

/-- The actual multisite Hessian intertwines with the witness Hessian. -/
theorem base_tensor (s : ℝ) (u v : Fin 9 → ℝ) :
    realBilinear (sourceTensor (repackRates (AttractingWitness.rates s)))
      (chartMatrix.mulVec u) (chartMatrix.mulVec v)=
      chartMatrix.mulVec (AttractingWitness.hessian s u v) := by
  let f := (realBilinear (sourceTensor (repackRates (AttractingWitness.rates s)))).compl₁₂
    chartMatrix.mulVecLin chartMatrix.mulVecLin
  let g := (hessianBilinear s).compr₂ chartMatrix.mulVecLin
  have hf : ∀ a b, f a b=f b a := by
    intro a b
    simp only [f,LinearMap.compl₁₂_apply]
    exact realBilinear_symmetric _ (sourceTensor_symmetric _) _ _
  have hg : ∀ a b, g a b=g b a := by
    intro a b
    simp only [g,LinearMap.compr₂_apply,hessianBilinear_apply]
    rw [AttractingWitness.hessian_symmetric]
  have hd : ∀ y, f y y=g y y := by
    intro y
    simp only [f,g,LinearMap.compl₁₂_apply,LinearMap.compr₂_apply,Matrix.mulVecLin_apply,
      hessianBilinear_apply]
    have h := (base_separation s y).2
    rw [AttractingWitness.hessian_diagonal,Matrix.mulVec_smul,← h,smul_smul]
    norm_num
  exact polarization f g hf hg hd u v

/-- The witness Hessian as a coefficient tensor. -/
def witnessTensor (s : ℝ) : GenericQuadraticTensor.Tensor (Fin 9) :=
  fun i j l => hessianBilinear s (Pi.single j 1) (Pi.single l 1) i

theorem witnessTensor_real (s : ℝ) (u v : Fin 9 → ℝ) :
    realBilinear (witnessTensor s) u v=AttractingWitness.hessian s u v := by
  ext i
  exact (bilinear_coordinates (hessianBilinear s) u v i).symm

theorem witnessTensor_complex (s : ℝ) (x y : Fin 9 → ℂ) :
    complexBilinear (witnessTensor s) x y=AttractingWitness.complexHessian s x y := by
  have hΦ : complexBilinear (witnessTensor s)=AttractingWitness.complexHessianBilinear s := by
    apply LinearMap.ext_basis (Pi.basisFun ℂ (Fin 9)) (Pi.basisFun ℂ (Fin 9))
    intro a c
    rw [Pi.basisFun_apply,Pi.basisFun_apply,AttractingWitness.complexHessianBilinear_apply,
      single_complexify,single_complexify,← complexify_realBilinear,witnessTensor_real]
    exact (AttractingWitness.complexHessian_ofReal s _ _).symm
  rw [hΦ]
  rfl

theorem base_tensor_witness (s : ℝ) (u v : Fin 9 → ℝ) :
    realBilinear (sourceTensor (repackRates (AttractingWitness.rates s)))
      (chartMatrix.mulVec u) (chartMatrix.mulVec v)=
      chartMatrix.mulVec (realBilinear (witnessTensor s) u v) := by
  rw [witnessTensor_real]
  exact base_tensor s u v

/-! ### Complexified chart and eigenbasis transport -/

theorem complexRect_mul {ι κ μ : Type*} [Fintype κ] (P : Matrix ι κ ℝ) (Q : Matrix κ μ ℝ) :
    complexRect P*complexRect Q=complexRect (P*Q) := by
  ext i j
  simp [complexRect,Matrix.mul_apply]

theorem complexRect_one {ι : Type*} [DecidableEq ι] :
    complexRect (1 : Matrix ι ι ℝ)=1 := by
  ext i j
  by_cases h : i=j <;> simp [complexRect,Matrix.one_apply,h]

/-- The complexified chart as a complex linear equivalence. -/
def chartEquiv : (Fin 9 → ℂ) ≃ₗ[ℂ] (CoordinateIndex 3 → ℂ) :=
  LinearEquiv.ofLinear (complexRect chartMatrix).mulVecLin (complexRect inverseMatrix).mulVecLin
    (by
      apply LinearMap.ext
      intro v
      simp only [LinearMap.comp_apply,Matrix.mulVecLin_apply,Matrix.mulVec_mulVec,complexRect_mul,
        chartMatrix_mul_inverse,complexRect_one,Matrix.one_mulVec,LinearMap.id_apply])
    (by
      apply LinearMap.ext
      intro v
      simp only [LinearMap.comp_apply,Matrix.mulVecLin_apply,Matrix.mulVec_mulVec,complexRect_mul,
        inverse_mul_chartMatrix,complexRect_one,Matrix.one_mulVec,LinearMap.id_apply])

@[simp] theorem chartEquiv_apply (v : Fin 9 → ℂ) :
    chartEquiv v=(complexRect chartMatrix).mulVec v := rfl

theorem complexMatrix_witness (s : ℝ) :
    complexMatrix (AttractingWitness.sourceMatrix s)=AttractingWitness.complexSource s := by
  ext i j
  simp [complexMatrix,AttractingWitness.complexSource]

theorem complexMatrix_sub {ι : Type*} (A B : Matrix ι ι ℝ) :
    complexMatrix (A-B)=complexMatrix A-complexMatrix B := by
  ext i j
  simp [complexMatrix]

theorem adjugate_conjugate (z : ℂ) :
    conjugateVector (AttractingWitness.adjugateVector z)=
      AttractingWitness.adjugateVector (star z) := by
  funext i
  fin_cases i <;> simp [conjugateVector,AttractingWitness.adjugateVector]

/-- Spectral data of the actual multisite source matrix, transported from witness A. -/
def baseData (r w : ℝ) (hw : 0<w) (x : Fin 7 → ℝ) (hx : StrictMono x) (hn : ∀ i, x i<0)
    (b : Module.Basis AttractingWitness.SpectralIndex ℂ (Fin 9 → ℂ))
    (hb : ∀ i, b i=AttractingWitness.adjugateVector (AttractingWitness.spectralValues x w i))
    (he : ∀ i, (AttractingWitness.complexSource r).mulVec (b i)=
      AttractingWitness.spectralValues x w i • b i) :
    Data (Fin 7) (MultisiteTensor.sourceMatrix (repackRates (AttractingWitness.rates r)) baseState) where
  basis := b.map chartEquiv
  stable := x
  freq := w
  freq_pos := hw
  stable_neg := hn
  stable_injective := hx.injective
  stable_eigen := by
    intro s
    rw [Module.Basis.map_apply,chartEquiv_apply,
      complex_intertwining _ _ chartMatrix (base_similarity r),complexMatrix_witness,he,
      Matrix.mulVec_smul]
    rfl
  critical_eigen := by
    rw [Module.Basis.map_apply,chartEquiv_apply,
      complex_intertwining _ _ chartMatrix (base_similarity r),complexMatrix_witness,he,
      Matrix.mulVec_smul]
    simp [AttractingWitness.spectralValues]
  stable_real := by
    intro s
    rw [Module.Basis.map_apply,chartEquiv_apply,← complexRect_conjugate,hb,adjugate_conjugate]
    simp [AttractingWitness.spectralValues]
  critical_pair := by
    rw [Module.Basis.map_apply,Module.Basis.map_apply,chartEquiv_apply,chartEquiv_apply,
      ← complexRect_conjugate,hb,hb,adjugate_conjugate]
    congr 2
    simp [AttractingWitness.spectralValues]

theorem baseData_coord (r w : ℝ) (hw : 0<w) (x : Fin 7 → ℝ) (hx : StrictMono x)
    (hn : ∀ i, x i<0) (b : Module.Basis AttractingWitness.SpectralIndex ℂ (Fin 9 → ℂ))
    (hb : ∀ i, b i=AttractingWitness.adjugateVector (AttractingWitness.spectralValues x w i))
    (he : ∀ i, (AttractingWitness.complexSource r).mulVec (b i)=
      AttractingWitness.spectralValues x w i • b i) (i : Fin 7 ⊕ Fin 2) (y : Fin 9 → ℂ) :
    (baseData r w hw x hx hn b hb he).basis.coord i ((complexRect chartMatrix).mulVec y)=
      b.coord i y := by
  change (b.map chartEquiv).coord i (chartEquiv y)=b.coord i y
  rw [Module.Basis.coord_apply,Module.Basis.map_repr,LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply,Module.Basis.coord_apply]

/-! ### The strengthened invariant at the witness critical parameter -/

/-- **Base case.** The actual three-site witness-A family, translated to its critical
kinetic parameter `r0`, satisfies the strengthened Hopf invariant in the multisite chart:
the transported full eigenbasis, negative kinetic crossing and negative genuine-resolvent
Lyapunov value are those of the verified witness-A source data. -/
theorem base_hopf_invariant : ∃ r0 : ℝ, 0<r0 ∧
    HopfInvariant (Fin 7) (baseRates r0) baseState := by
  obtain ⟨r,w,x,hr,hw,-,-,hwl,hwu,hx,hn,b,hb,he⟩ := AttractingWitness.critical_source_eigenbasis
  have hq0 : b (Sum.inr 0)=AttractingWitness.adjugateVector (Complex.I*(w:ℂ)) := by
    rw [hb]
    simp [AttractingWitness.spectralValues]
  have hp : AttractingWitness.candidatePolynomial r (Complex.I*(w:ℂ))=0 := by
    apply AttractingWitness.source_root_of_adjugate
    rw [← hq0]
    have h := he (Sum.inr 0)
    simpa [AttractingWitness.spectralValues] using h
  have hleft : ∀ v, b.coord (Sum.inr 0) ((AttractingWitness.complexSource r).mulVec v)=
      (Complex.I*(w:ℂ))*b.coord (Sum.inr 0) v := by
    intro v
    rw [GenericPeriodicKernel.basis_coord_eigen b _ _ he]
    simp [AttractingWitness.spectralValues]
  have hnorm : b.coord (Sum.inr 0) (AttractingWitness.adjugateVector (Complex.I*(w:ℂ)))=1 := by
    rw [← hq0]
    simp
  let d0 := baseData r w hw x hx hn b hb he
  have hcoord := baseData_coord r w hw x hx hn b hb he (Sum.inr 0)
  have hd0q : d0.basis (Sum.inr 0)=(complexRect chartMatrix).mulVec (b (Sum.inr 0)) := by
    change (b.map chartEquiv) (Sum.inr 0)=_
    rw [Module.Basis.map_apply,chartEquiv_apply]
  have hsim := base_similarity r
  -- the kinetic slope and its intertwining
  have hA : ∀ t, MultisiteTensor.sourceMatrix (baseRates r t) baseState=
      MultisiteTensor.sourceMatrix (repackRates (AttractingWitness.rates r)) baseState+
        t • MultisiteTensor.sourceMatrix baseSlope baseState := by
    intro t
    rw [baseRates_affine,sourceMatrix_affine]
  have hslope : MultisiteTensor.sourceMatrix baseSlope baseState*chartMatrix=
      chartMatrix*(AttractingWitness.sourceMatrix (r+1)-AttractingWitness.sourceMatrix (r+0)) := by
    have hsimT : ∀ t, MultisiteTensor.sourceMatrix (baseRates r t) baseState*chartMatrix=
        chartMatrix*AttractingWitness.sourceMatrix (r+t) := fun t => base_similarity (r+t)
    have hsl : MultisiteTensor.sourceMatrix baseSlope baseState=
        MultisiteTensor.sourceMatrix (baseRates r 1) baseState-
          MultisiteTensor.sourceMatrix (baseRates r 0) baseState := by
      rw [hA 1,hA 0,one_smul,zero_smul,add_zero,add_sub_cancel_left]
    rw [hsl,Matrix.sub_mul,hsimT 1,hsimT 0,Matrix.mul_sub]
  have hΔ : complexMatrix (AttractingWitness.sourceMatrix (r+1)-AttractingWitness.sourceMatrix (r+0))=
      AttractingWitness.complexSource 1-AttractingWitness.complexSource 0 := by
    rw [complexMatrix_sub,complexMatrix_witness,complexMatrix_witness,
      AttractingWitness.complexSource_affine (r+1),AttractingWitness.complexSource_affine (r+0)]
    push_cast
    module
  -- crossing
  have hcross : (crossing d0 (MultisiteTensor.sourceMatrix baseSlope baseState)).re<0 := by
    unfold crossing
    rw [hd0q,complex_intertwining _ _ chartMatrix hslope,hΔ,hcoord,hq0]
    have h := AttractingWitness.source_parameter_pairing_negative r w (ne_of_gt hw) hp
      (b.coord (Sum.inr 0)) hleft hnorm
    simpa [AttractingWitness.sourceOperator_apply,Matrix.sub_mulVec] using h
  -- Lyapunov value
  have hlyap : (lyapunovValue d0 (sourceTensor (repackRates (AttractingWitness.rates r)))).re<0 := by
    obtain ⟨heven,hodd⟩ := AttractingWitness.frequency_equations_of_root r w (ne_of_gt hw) hp
    have hf : AttractingWitness.frequencyPolynomial (w^2)=0 := by
      rw [AttractingWitness.frequency_elimination_identity]
      linear_combination AttractingWitness.even1 (w^2)*hodd-AttractingWitness.odd1 (w^2)*heven
    have hne := ne_of_lt (AttractingWitness.frequency_even_signs (w^2) ⟨hwl,hwu⟩).2
    have hJ := AttractingWitness.source_h11_resolvent r w hf heven hne
    have hH := AttractingWitness.source_h20_resolvent r w hf heven hne
    set q := b (Sum.inr 0) with hqdef
    let h11 : Fin 9 → ℂ := fun i => (AttractingWitness.lyapunovH11 (w^2) i:ℂ)
    let h20 := AttractingWitness.h20Pilot w
    have h11eq : (complexMatrix (AttractingWitness.sourceMatrix r)).mulVec h11=
        complexBilinear (witnessTensor r) q (conjugateVector q) := by
      rw [complexMatrix_witness,witnessTensor_complex,hq0]
      exact hJ
    have h20eq : (2*Complex.I*(w:ℂ)) • h20-(complexMatrix (AttractingWitness.sourceMatrix r)).mulVec h20=
        complexBilinear (witnessTensor r) q q := by
      rw [complexMatrix_witness,witnessTensor_complex,hq0,← hH]
      rfl
    obtain ⟨f11,f20⟩ := resolvent_equations_transport _ _ chartMatrix hsim (witnessTensor r)
      (sourceTensor (repackRates (AttractingWitness.rates r))) (base_tensor_witness r) w q h11 h20
      h11eq h20eq
    rw [← hd0q] at f11 f20
    rw [← lyapunovValue_eq_coefficient d0 _ _ _ f11 f20,hd0q,
      coefficient_transport (witnessTensor r) _ chartMatrix (base_tensor_witness r)
        (b.coord (Sum.inr 0)) _ hcoord]
    have hL := AttractingWitness.normalized_left_eq_lyapunovLeft r w hw hp x b hb he
      (b.coord (Sum.inr 0)) hleft hnorm
    have hG := AttractingWitness.explicitSourceCoefficient_real_negative r w (ne_of_gt hw) hp
      ⟨hwl,hwu⟩
    unfold coefficient
    rw [hL,witnessTensor_complex,witnessTensor_complex,hq0]
    exact hG
  -- assemble
  have hmat : MultisiteTensor.sourceMatrix (repackRates (AttractingWitness.rates r)) baseState=
      MultisiteTensor.sourceMatrix (baseRates r 0) baseState := by rw [baseRates_zero]
  refine ⟨r,hr,?_,⟨repackRates (AttractingWitness.rates r),baseSlope,baseRates_affine r⟩,
    repack_positive _ AttractingWitness.state_positive,fun t => base_equilibrium (r+t),?_,
    transport hmat d0,MultisiteTensor.sourceMatrix baseSlope baseState,?_,?_,?_⟩
  · have hfun : baseRates r=affineRates (repackRates (AttractingWitness.rates r)) baseSlope :=
      funext (baseRates_affine r)
    rw [hfun]
    exact affineRates_smooth _ _
  · have ht : Tendsto (fun t : ℝ => r+t) (𝓝 0) (𝓝 r) := by
      simpa using (continuous_const.add continuous_id).tendsto' (0:ℝ) (r+0) rfl
    filter_upwards [ht.eventually (lt_mem_nhds hr)] with t htpos
    exact repack_rates_positive _ (AttractingWitness.rates_positive (r+t) htpos)
  · intro i j
    have hfun : (fun t => MultisiteTensor.sourceMatrix (baseRates r t) baseState i j)=
        fun t => MultisiteTensor.sourceMatrix (repackRates (AttractingWitness.rates r)) baseState i j+
          t*MultisiteTensor.sourceMatrix baseSlope baseState i j := by
      funext t
      rw [hA]
      rfl
    rw [hfun]
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const
      (MultisiteTensor.sourceMatrix baseSlope baseState i j)).const_add
      (MultisiteTensor.sourceMatrix (repackRates (AttractingWitness.rates r)) baseState i j)
  · rw [crossing_transport]
    exact hcross
  · rw [lyapunovValue_transport,baseRates_zero]
    exact hlyap

/-- **All-site strengthened invariant.** For every number of sites `n ≥ 3` there is an
actual affine positive kinetic family with a parameter-independent positive equilibrium
satisfying the full strengthened Hopf invariant (spectral data, negative crossing and
negative genuine-resolvent Lyapunov value) at the critical parameter `0`. -/
theorem all_site_hopf_invariant (n : ℕ) (hn : 3 ≤ n) :
    ∃ (σ : Type) (_ : Fintype σ) (_ : DecidableEq σ)
      (k : ℝ → PhosphorylationSharpness.Rates n) (x : PhosphorylationSharpness.State n),
      HopfInvariant σ k x := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨r0,-,h⟩ := base_hopf_invariant
  exact hopf_iterate (baseRates r0) baseState h m

end
end ThreeSitePhosphorylation.AllSiteHopfInvariant
