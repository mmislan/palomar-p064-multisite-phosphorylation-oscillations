import proofs.ThreeSitePhosphorylation.AttractingSpectral

/-! Full eigenbasis at witness A's critical point, by nine distinct roots.
A single dual-vector certificate proves all adjugate vectors nonzero; no
companion-matrix inverse or determinant enumeration is used. -/
namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section
set_option maxHeartbeats 1500000
open scoped Matrix

def adjugateDual : Fin 9 → ℂ :=
  ![(21106545520033901702752031206324372007320351679507042886330803245828150522139041150171984763671875000000/16180102516284144682942090071210564173649338375831505665014467895203384824802098552254973233942753524189733),(-331067718656333150739760104881321976108161709315999134667038297471699359578063651839900838043212890625/16180102516284144682942090071210564173649338375831505665014467895203384824802098552254973233942753524189733),(15225915402912571650758220834367632506772160663331347816605821614860092830269864702831245006250000000000/16180102516284144682942090071210564173649338375831505665014467895203384824802098552254973233942753524189733),(35120747912453744587507777125827186574550652895174012738896660677420087998775104071116346083593750000000000/1634190354144698612977151097192266981538583175958982072166461257415541867305011953777752296628218105943163033),(-87716431192633031288571163062177074748778004777451286791349144633342759264870386160146716528320312500000/1634190354144698612977151097192266981538583175958982072166461257415541867305011953777752296628218105943163033),(-184113238209877832620939596936595263937392057148560103639150996709924928969912206389180123066406250000000/1634190354144698612977151097192266981538583175958982072166461257415541867305011953777752296628218105943163033),(0),(33368276214995446597355219577880894477567261172879870773432905412537097744577055087663992015380859375000/1634190354144698612977151097192266981538583175958982072166461257415541867305011953777752296628218105943163033),(-23632718177410003135364599413031140312421557149368103013483922118915656925279509896889446210937500000000/233455764877814087568164442456038140219797596565568867452351608202220266757858850539678899518316872277594719)]

theorem adjugate_dual_identity (z : ℂ) :
    dotProduct adjugateDual (adjugateVector z) = 1 := by
  simp [adjugateDual,adjugateVector,dotProduct,Fin.sum_univ_succ]
  ring

theorem adjugate_ne_zero (z : ℂ) : adjugateVector z ≠ 0 := by
  intro hz
  have h := adjugate_dual_identity z
  rw [hz] at h
  simp at h

def complexSource (r : ℝ) : Matrix (Fin 9) (Fin 9) ℂ :=
  (sourceMatrix r).map (algebraMap ℝ ℂ)

theorem source_root_eigenvector (r : ℝ) (z : ℂ)
    (hp : candidatePolynomial r z = 0) :
    adjugateVector z ≠ 0 ∧ (complexSource r).mulVec (adjugateVector z) = z • adjugateVector z := by
  refine ⟨adjugate_ne_zero z,?_⟩
  ext i
  simp only [complexSource,adjugate_residual,hp,ite_self,sub_zero,Pi.smul_apply,smul_eq_mul]

theorem frequency_ratio_domain (t r : ℝ)
    (ht : frequencyLower ≤ t ∧ t ≤ frequencyUpper)
    (he : even0 t+r*even1 t=0) : (7/5:ℝ)<r ∧ r<(3/2:ℝ) := by
  have hs := (frequency_even_signs t ht).2
  have hl : (0:ℝ) ≤ frequencyLower := by norm_num [frequencyLower]
  have ht0 : 0 ≤ t := hl.trans ht.1
  have h2 : frequencyLower^2 ≤ t^2 ∧ t^2 ≤ frequencyUpper^2 := by
    constructor <;> gcongr
    · exact ht.1
    · exact ht.2
  have h3 : frequencyLower^3 ≤ t^3 ∧ t^3 ≤ frequencyUpper^3 := by
    constructor <;> gcongr
    · exact ht.1
    · exact ht.2
  have h4 : frequencyLower^4 ≤ t^4 ∧ t^4 ≤ frequencyUpper^4 := by
    constructor <;> gcongr
    · exact ht.1
    · exact ht.2
  norm_num [frequencyLower,frequencyUpper] at ht h2 h3 h4
  have hp : 0 < even0 t+(7/5:ℝ)*even1 t := by
    unfold even0 even1
    linarith only [ht.1,ht.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
  have hn : even0 t+(3/2:ℝ)*even1 t < 0 := by
    unfold even0 even1
    linarith only [ht.1,ht.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
  constructor <;> nlinarith

def realCandidate (r x : ℝ) : ℝ := (candidatePolynomial r (x:ℂ)).re

theorem realCandidate_continuous (r : ℝ) : Continuous (realCandidate r) := by
  unfold realCandidate candidatePolynomial
  fun_prop

def realRootLower : Fin 7 → ℝ := ![(-71),(-25),(-20),(-7),(-12/5),(-27/100),(-23/500)]
def realRootUpper : Fin 7 → ℝ := ![(-70),(-24),(-19),(-6),(-23/10),(-1/4),(-9/200)]

theorem real_root_box_signs (r : ℝ) (_hl : (7/5:ℝ) ≤ r) (_hu : r ≤ (3/2:ℝ))
    (i : Fin 7) :
    (-1:ℝ)^(i:ℕ)*realCandidate r (realRootLower i) < 0 ∧
      0 < (-1:ℝ)^(i:ℕ)*realCandidate r (realRootUpper i) := by
  fin_cases i <;> constructor <;>
    norm_num [realRootLower,realRootUpper,realCandidate,candidatePolynomial,
      pow_succ,Complex.mul_re,Complex.mul_im] <;> linarith

theorem real_root_in_box (r : ℝ) (hl : (7/5:ℝ) ≤ r) (hu : r ≤ (3/2:ℝ))
    (i : Fin 7) : ∃ x : ℝ, x ∈ Set.Icc (realRootLower i) (realRootUpper i) ∧
      realCandidate r x=0 := by
  have hb : realRootLower i ≤ realRootUpper i := by
    fin_cases i <;> norm_num [realRootLower,realRootUpper]
  have hc : Continuous (fun x => (-1:ℝ)^(i:ℕ)*realCandidate r x) :=
    continuous_const.mul (realCandidate_continuous r)
  have hs := real_root_box_signs r hl hu i
  obtain ⟨x,hx,hz⟩ := intermediate_value_Icc hb hc.continuousOn ⟨hs.1.le,hs.2.le⟩
  exact ⟨x,hx,(mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (by norm_num))⟩

theorem real_root_box_order (i j : Fin 7) (h : i<j) : realRootUpper i < realRootLower j := by
  fin_cases i <;> fin_cases j <;> norm_num [realRootLower,realRootUpper] at *

theorem seven_negative_roots (r : ℝ) (hl : (7/5:ℝ) ≤ r) (hu : r ≤ (3/2:ℝ)) :
    ∃ x : Fin 7 → ℝ, StrictMono x ∧ ∀ i, x i < 0 ∧ realCandidate r (x i)=0 := by
  choose x hx hz using real_root_in_box r hl hu
  refine ⟨x,?_,?_⟩
  · intro i j hij
    exact (hx i).2.trans_lt ((real_root_box_order i j hij).trans_le (hx j).1)
  · intro i
    refine ⟨(hx i).2.trans_lt ?_,hz i⟩
    fin_cases i <;> norm_num [realRootUpper]


abbrev SpectralIndex := Fin 7 ⊕ Fin 2

def spectralValues (x : Fin 7 → ℝ) (w : ℝ) : SpectralIndex → ℂ :=
  Sum.elim (fun i => (x i:ℂ)) (fun j => Complex.I*((![w,-w] j:ℝ):ℂ))

theorem spectralValues_injective (x : Fin 7 → ℝ) (hx : StrictMono x)
    (hn : ∀ i, x i<0) (w : ℝ) (hw : 0<w) : Function.Injective (spectralValues x w) := by
  intro i j hij
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      have he : x i=x j := Complex.ofReal_injective hij
      exact congrArg Sum.inl (hx.injective he)
    | inr j =>
      have he := congrArg Complex.re hij
      fin_cases j <;> simp [spectralValues] at he <;> linarith [hn i]
  | inr i =>
    cases j with
    | inl j =>
      have he := congrArg Complex.re hij
      fin_cases i <;> simp [spectralValues] at he <;> linarith [hn j]
    | inr j =>
      have he := congrArg Complex.im hij
      fin_cases i <;> fin_cases j <;> simp [spectralValues] at he ⊢ <;> linarith

theorem realCandidate_root (r x : ℝ) (hx : realCandidate r x=0) :
    candidatePolynomial r (x:ℂ)=0 := by
  apply Complex.ext
  · exact hx
  · simp [candidatePolynomial,pow_succ,Complex.mul_im,Complex.mul_re]

theorem critical_source_eigenbasis : ∃ r w : ℝ, ∃ x : Fin 7 → ℝ,
    0 < r ∧ 0 < w ∧ (7/5:ℝ)<r ∧ r<(3/2:ℝ) ∧
    frequencyLower ≤ w^2 ∧ w^2 ≤ frequencyUpper ∧ StrictMono x ∧ (∀ i, x i<0) ∧
    ∃ b : Module.Basis SpectralIndex ℂ (Fin 9 → ℂ),
      (∀ i, b i=adjugateVector (spectralValues x w i)) ∧
      ∀ i, (complexSource r).mulVec (b i)=spectralValues x w i • b i := by
  obtain ⟨t,r,ht,hr,hl,hu,he,ho⟩ := admissible_frequency_exists
  let w := Real.sqrt t
  have hw : 0 < w := Real.sqrt_pos.2 ht
  have hw2 : w^2=t := Real.sq_sqrt ht.le
  have hrb := frequency_ratio_domain t r ⟨hl,hu⟩ he
  obtain ⟨x,hx,hroots⟩ := seven_negative_roots r hrb.1.le hrb.2.le
  have hn : ∀ i, x i<0 := fun i => (hroots i).1
  have hi := spectralValues_injective x hx hn w hw
  have hroot : ∀ i : SpectralIndex, candidatePolynomial r (spectralValues x w i)=0 := by
    intro i
    cases i with
    | inl i => exact realCandidate_root r (x i) (hroots i).2
    | inr j =>
      fin_cases j
      · change candidatePolynomial r (Complex.I*(w:ℂ))=0
        rw [candidate_at_imaginary,hw2,he,ho]
        simp
      · change candidatePolynomial r (Complex.I*((-w:ℝ):ℂ))=0
        rw [candidate_at_imaginary,neg_sq,hw2,he,ho]
        simp
  have hev : ∀ i : SpectralIndex,
      Module.End.HasEigenvector (complexSource r).mulVecLin (spectralValues x w i)
        (adjugateVector (spectralValues x w i)) := by
    intro i
    obtain ⟨hv,he⟩ := source_root_eigenvector r (spectralValues x w i) (hroot i)
    exact ⟨by simpa only [Module.End.mem_eigenspace_iff] using he,hv⟩
  have hlin := Module.End.eigenvectors_linearIndependent' (complexSource r).mulVecLin
    (spectralValues x w) hi (fun i => adjugateVector (spectralValues x w i)) hev
  have hcard : Fintype.card SpectralIndex=Module.finrank ℂ (Fin 9 → ℂ) := by
    simp [SpectralIndex]
  let b := basisOfLinearIndependentOfCardEqFinrank hlin hcard
  have hb : ∀ i, b i=adjugateVector (spectralValues x w i) := by
    intro i
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hlin hcard) i
  refine ⟨r,w,x,hr,hw,hrb.1,hrb.2,by rwa [hw2],by rwa [hw2],hx,hn,b,hb,?_⟩
  intro i
  rw [hb]
  exact (source_root_eigenvector r (spectralValues x w i) (hroot i)).2

end
end ThreeSitePhosphorylation.AttractingWitness
