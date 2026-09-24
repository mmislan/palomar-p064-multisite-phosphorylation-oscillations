import proofs.ThreeSitePhosphorylation.AttractingSource
import proofs.ThreeSitePhosphorylation.AttractingFrequency

/-! Kernel-replayed imaginary eigenpair of the actual witness A Jacobian.
No claim of attraction, simplicity or complementary stability is made here. -/
namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section
set_option maxHeartbeats 3000000
open scoped Matrix

def sourceMatrix (r : ℝ) : Matrix (Fin 9) (Fin 9) ℝ :=
  !![(0) , (0) , (0) , (5/23) , (0) , (0) , (-1/230) , (0) , (0);
    (0) , (0) , (0) , (0) , (64/3) , (0) , (0) , (-320/9) , (0);
    (0) , (0) , (0) , (0) , (0) , (12/17) , (0) , (0) , (-3/10);
    (-101/2000) , (0) , (0) , (-14443/46000) , (-101/2300) , (-101/2300) , (0) , (0) , (0);
    (202/375) , (-202/375) , (0) , (-1616/575) , (-214726/8625) , (-1616/575) , (-202/375) , (0) , (0);
    (0) , (303/50) , (-303/50) , (-303/575) , (-303/575) , (-142713/19550) , (0) , (-303/50) , (0);
    (1/120)+r*(1/120) , (-1/120)+r*(-1/120) , (0) , (0) , (-1/120)+r*(-1/120) , (0) , (-145/552)+r*(-145/552) , (-1/4)+r*(-1/4) , (-1/4)+r*(-1/4);
    (0) , (808/25) , (-808/25) , (0) , (0) , (-808/25) , (-404/25) , (-18988/225) , (-404/25);
    (0) , (0) , (303/100) , (0) , (0) , (0) , (-303/100) , (-303/100) , (-6363/1000)]

theorem sourceMatrix_action (r : ℝ) (y : ReducedState) :
    (sourceMatrix r).mulVec y = linearPart r y := by
  ext i
  fin_cases i <;>
    simp [sourceMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
      linearPart,linearRows,complexRow,state,
      speciesVariation,coordinate,inputSpecies,enzymeSpecies,boundCoordinate,binding,exitRate] <;> ring

def adjugateVector (z : ℂ) : Fin 9 → ℂ :=
  ![(-1/230)*z^7 + (-867530309/1618740000)*z^6 + (-2232603095042737/111693060000000)*z^5 + (-24327251417784917747/83769795000000000)*z^4 + (-3234339710680749643637/2094244875000000000)*z^3 + (-8649541613431276430279/2908673437500000000)*z^2 + (-1560083472015808782397/727168359375000000)*z^1 + (-1606295455429684001/3787335205078125)*z^0,
    (633472/1125)*z^6 + (9631911021256/494859375)*z^5 + (75238310775966373/474240234375)*z^4 + (124972202676802015804/272688134765625)*z^3 + (12256871821467761029871/27268813476562500)*z^2 + (1553573015806460294689/15149340820312500)*z^1 + (4475519806406306853/1262445068359375)*z^0,
    (909/1000)*z^6 + (25164836699/156400000)*z^5 + (33571845329500981/4496500000000)*z^4 + (857980786307910136991/7756462500000000)*z^3 + (79423025018348455359733/290867343750000000)*z^2 + (1347546879748752097877/18179208984375000)*z^1 + (10036730451121592464/3787335205078125)*z^0,
    (164731/6900000)*z^6 + (-47744788687373/24281100000000)*z^5 + (-79137275284057979/404685000000000)*z^4 + (-66690939450028767337/18210825000000000)*z^3 + (-163779693496535852447/16495312500000000)*z^2 + (-83491023108573773881/31616015625000000)*z^1 + (-4469241566341733/164666748046875)*z^0,
    (-202/375)*z^7 + (-69926793793/1319625000)*z^6 + (-17579354618633777/10117125000000)*z^5 + (-360569529306719725633/17452040625000000)*z^4 + (-94397926389418060828267/1745204062500000000)*z^3 + (-25821322264129193578433/969557812500000000)*z^2 + (-1009546493618889789293/242389453125000000)*z^1 + (-37120813141290918/252489013671875)*z^0,
    (7059092/71875)*z^6 + (370632684819871/59512500000)*z^5 + (108601448383090537129/1026590625000000)*z^4 + (1757484444648581742301/5703281250000000)*z^3 + (8273284838437685348071/51329531250000000)*z^2 + (186296782115402851733/7129101562500000)*z^1 + (61549387185262713/74261474609375)*z^0,
    (1)*z^8 + (867530309/7038000)*z^7 + (2233182783431737/485622000000)*z^6 + (24291442826269387997/364216500000000)*z^5 + (1572655137993092208631/4552706250000000)*z^4 + (6706465405029117421141/13390312500000000)*z^3 + (-113663087911917642641/37939218750000000)*z^2 + (-109046388100369541213/3161601562500000)*z^1 + (-8938483132683466/6586669921875)*z^0,
    (-404/25)*z^7 + (-8492771143/14662500)*z^6 + (-618784435964001/112412500000)*z^5 + (-6395531629018484983/252928125000000)*z^4 + (-3279213546345533597947/72716835937500000)*z^3 + (-2438563304923885957/129274375000000)*z^2 + (-104982617187654655097/40398242187500000)*z^1 + (-111362439423872754/1262445068359375)*z^0,
    (-303/100)*z^7 + (-14322071387/46920000)*z^6 + (-41414306417323583/4046850000000)*z^5 + (-36361703686707905083/303513750000000)*z^4 + (-702329783086935332039/3793921875000000)*z^3 + (2883097319442676956563/21815050781250000)*z^2 + (478596502737235815487/9089604492187500)*z^1 + (492395097482101704/252489013671875)*z^0]

theorem adjugate_residual (r : ℝ) (z : ℂ) :
    ∀ i : Fin 9, ((sourceMatrix r).map (algebraMap ℝ ℂ)).mulVec (adjugateVector z) i =
      z*adjugateVector z i - (if i=6 then candidatePolynomial r z else 0) := by
  intro i
  fin_cases i <;>
    simp [sourceMatrix,adjugateVector,candidatePolynomial,Matrix.mulVec,
      dotProduct,Fin.sum_univ_succ] <;> ring

def adjugateReal0 (t : ℝ) : ℝ := (867530309/1618740000)*t^3 + (-24327251417784917747/83769795000000000)*t^2 + (8649541613431276430279/2908673437500000000)*t^1 + (-1606295455429684001/3787335205078125)*t^0

theorem adjugate_real0 (w : ℝ) :
    (adjugateVector (Complex.I*(w:ℂ)) 0).re = adjugateReal0 (w^2) := by
  simp [adjugateVector,adjugateReal0,pow_succ,Complex.mul_re,Complex.mul_im]
  ring

theorem adjugate_real0_negative (t : ℝ)
    (ht : frequencyLower ≤ t ∧ t ≤ frequencyUpper) : adjugateReal0 t < 0 := by
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
  norm_num [frequencyLower,frequencyUpper] at ht h2 h3
  unfold adjugateReal0
  linarith only [ht.1,ht.2,h2.1,h2.2,h3.1,h3.2]

theorem source_imaginary_eigenpair : ∃ r w : ℝ, ∃ v : Fin 9 → ℂ,
    0 < r ∧ 0 < w ∧ frequencyLower ≤ w^2 ∧ w^2 ≤ frequencyUpper ∧ v ≠ 0 ∧
    ((sourceMatrix r).map (algebraMap ℝ ℂ)).mulVec v = (Complex.I*(w:ℂ)) • v := by
  obtain ⟨t,r,ht,hr,hl,hu,he,ho⟩ := admissible_frequency_exists
  let w := Real.sqrt t
  have hw : 0 < w := Real.sqrt_pos.2 ht
  have hw2 : w^2=t := Real.sq_sqrt ht.le
  have hp : candidatePolynomial r (Complex.I*(w:ℂ)) = 0 := by
    rw [candidate_at_imaginary,hw2,he,ho]
    simp
  refine ⟨r,w,adjugateVector (Complex.I*(w:ℂ)),hr,hw,by rwa [hw2],by rwa [hw2],?_,?_⟩
  · intro hz
    have hzero := congrArg (fun v : Fin 9 → ℂ => (v 0).re) hz
    change (adjugateVector (Complex.I*(w:ℂ)) 0).re = 0 at hzero
    have hsign := adjugate_real0_negative t ⟨hl,hu⟩
    rw [adjugate_real0,hw2] at hzero
    linarith
  · ext i
    rw [adjugate_residual,hp]
    simp

end
end ThreeSitePhosphorylation.AttractingWitness
