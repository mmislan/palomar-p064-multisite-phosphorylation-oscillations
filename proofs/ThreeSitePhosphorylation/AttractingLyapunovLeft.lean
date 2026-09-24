import proofs.ThreeSitePhosphorylation.AttractingPairing

/-! Explicit normalized source left eigenfunctional, using the rank-one
parameter row. No h20 or source Lyapunov-scalar claim is made here. -/
namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section
open scoped Matrix
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000

def lyapunovFeedbackRow : Fin 9 → ℂ :=
  ![(1/120), (-1/120), (0), (0), (-1/120), (0), (-145/552), (-1/4), (-1/4)]

def lyapunovRawLeft (z : ℂ) : Fin 9 → ℂ :=
  ![(1/120)*z^8 + (863739173/844560000)*z^7 + (2201796054327233/58274640000000)*z^6 + (428983804068302971/971244000000000)*z^5 + (6054989460402985159/2697900000000000)*z^4 + (467095021105992020831/151756875000000000)*z^3 + (-5903087135411682689/3161601562500000)*z^2 + (-17046899547998954/10977783203125)*z^1,
    (-1/120)*z^8 + (-7687783973/844560000)*z^7 + (-15658973069664713/58274640000000)*z^6 + (-722371395116539931/582746400000000)*z^5 + (-37100197089856969093/18210825000000000)*z^4 + (-139849343020736984381/35707500000000000)*z^3 + (-53982978349696754107/50585625000000000)*z^2 + (-4045852677759449/105386718750000)*z^1,
    (2929/400)*z^7 + (261162307117/1689120000)*z^6 + (-259657927591392103/145686600000000)*z^5 + (-283772440071460938937/9105412500000000)*z^4 + (-11759440395385148529889/227635312500000000)*z^3 + (-119259812630173235443/9484804687500000)*z^2 + (-9939254902388686/19760009765625)*z^1,
    (1741/69000)*z^7 + (-304073369723/242811000000)*z^6 + (1174442113353473/2428110000000)*z^5 + (2261382889866881491/910541250000000)*z^4 + (118544763569063063/25292812500000)*z^3 + (1029691205019839/63232031250)*z^2 + (-27328758752224/52693359375)*z^1,
    (-1/120)*z^8 + (-842457893/844560000)*z^7 + (-12351325916154793/58274640000000)*z^6 + (-3298764096519889871/2913732000000000)*z^5 + (-32805461643896171969/18210825000000000)*z^4 + (-72368420655822991949/24281100000000000)*z^3 + (-1664336882747159327/2023425000000000)*z^2 + (-58232928822407/2107734375000)*z^1,
    (69892/8625)*z^7 + (27783561730307/121405500000)*z^6 + (148004699876131813/121405500000000)*z^5 + (161295010372622333/1011712500000000)*z^4 + (-37627553870416580947/2276353125000000)*z^3 + (-1935638369248164043/379392187500000)*z^2 + (-16180767993094/87822265625)*z^1,
    (-145/552)*z^8 + (-535682119897/19424880000)*z^7 + (-1328396252697850573/1340316720000000)*z^6 + (-383465940690669782329/27923265000000000)*z^5 + (-931837933283894317481801/16753959000000000000)*z^4 + (-10804886710795876287254177/139616325000000000000)*z^3 + (-1085025848693755537444247/34904081250000000000)*z^2 + (-390060029489815107481/90896044921875000)*z^1 + (-533510085136988654/3787335205078125)*z^0,
    (-1/4)*z^8 + (-731757587/84456000)*z^7 + (-393931376849981/5827464000000)*z^6 + (-322575421953237647/1456866000000000)*z^5 + (-946219845932454001/18210825000000000)*z^4 + (36614241855101172721/12140550000000000)*z^3 + (1887501490882195949/2023425000000000)*z^2 + (71105408546909/2107734375000)*z^1,
    (-1/4)*z^8 + (-141802687/5630400)*z^7 + (-413545015603283/485622000000)*z^6 + (-371834375197772983/36421650000000)*z^5 + (-15738333289107312733/910541250000000)*z^4 + (-2868236455779946399/569088281250000)*z^3 + (-13271264494599269/31616015625000)*z^2 + (-6832189688056/790400390625)*z^1]

def lyapunovPairing (z : ℂ) : ℂ :=
  dotProduct (lyapunovRawLeft z) (adjugateVector z)

theorem source_delta_rank_one (v : Fin 9 → ℂ) :
    (complexSource 1-complexSource 0).mulVec v =
      Pi.single 6 (dotProduct lyapunovFeedbackRow v) := by
  funext i
  fin_cases i <;> simp [complexSource,sourceMatrix,lyapunovFeedbackRow,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem lyapunovRawLeft_base_residual (z : ℂ) :
    Matrix.vecMul (lyapunovRawLeft z) (complexSource 0) =
      z • lyapunovRawLeft z - candidatePolynomial 0 z • lyapunovFeedbackRow := by
  funext i
  fin_cases i <;> simp [lyapunovRawLeft,complexSource,sourceMatrix,candidatePolynomial,
    lyapunovFeedbackRow,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]
  all_goals ring

theorem lyapunovRawLeft_feedback (z : ℂ) :
    lyapunovRawLeft z 6 = -candidateParameter z := by
  simp [lyapunovRawLeft,candidateParameter,candidatePolynomial]
  ring

theorem lyapunovPairing_identity (r : ℝ) (z : ℂ) :
    lyapunovPairing z = candidatePolynomial r z *
      (candidateSlope 1 z-candidateSlope 0 z) -
      candidateParameter z*candidateSlope r z := by
  simp [lyapunovPairing,lyapunovRawLeft,adjugateVector,dotProduct,Fin.sum_univ_succ,
    candidatePolynomial,candidateParameter,candidateSlope]
  ring

/-- Affine rank-one transport of the base residual; no expanded full-r certificate. -/
theorem lyapunovRawLeft_source_residual (r : ℝ) (z : ℂ) (v : Fin 9 → ℂ) :
    dotProduct (lyapunovRawLeft z) ((complexSource r).mulVec v) =
      z * dotProduct (lyapunovRawLeft z) v -
      candidatePolynomial r z * dotProduct lyapunovFeedbackRow v := by
  rw [complexSource_affine r,Matrix.add_mulVec,Matrix.smul_mulVec,
    dotProduct_add,dotProduct_smul,Matrix.dotProduct_mulVec,
    lyapunovRawLeft_base_residual,sub_dotProduct,smul_dotProduct,
    smul_dotProduct,source_delta_rank_one,dotProduct_single,lyapunovRawLeft_feedback]
  have hc := candidate_affine 0 r z
  simp only [sub_zero] at hc
  rw [hc]
  simp only [smul_eq_mul]
  ring

theorem candidateParameter_imaginary_ne_zero (r w : ℝ) (hw : w ≠ 0)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0) :
    candidateParameter (Complex.I*(w:ℂ)) ≠ 0 := by
  intro hz
  have h := candidate_crossing_negative r w hw hp
  simp [hz] at h

theorem lyapunovPairing_critical_ne_zero (r w : ℝ) (hw : w ≠ 0)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0) :
    lyapunovPairing (Complex.I*(w:ℂ)) ≠ 0 := by
  rw [lyapunovPairing_identity r, hp]
  simp only [zero_mul,zero_sub,neg_ne_zero]
  exact mul_ne_zero (candidateParameter_imaginary_ne_zero r w hw hp)
    (candidate_imaginary_root_simple r w hw hp)

def lyapunovLeft (z : ℂ) : (Fin 9 → ℂ) →ₗ[ℂ] ℂ :=
  (lyapunovPairing z)⁻¹ • dotProductEquiv ℂ (Fin 9) (lyapunovRawLeft z)

theorem lyapunovLeft_apply (z : ℂ) (v : Fin 9 → ℂ) :
    lyapunovLeft z v = (lyapunovPairing z)⁻¹ * dotProduct (lyapunovRawLeft z) v := rfl

theorem lyapunovLeft_normalized (z : ℂ) (hn : lyapunovPairing z ≠ 0) :
    lyapunovLeft z (adjugateVector z) = 1 := by
  rw [lyapunovLeft_apply]
  exact inv_mul_cancel₀ hn

theorem lyapunovLeft_eigen (r : ℝ) (z : ℂ) (hp : candidatePolynomial r z=0)
    (v : Fin 9 → ℂ) :
    lyapunovLeft z ((complexSource r).mulVec v) = z * lyapunovLeft z v := by
  rw [lyapunovLeft_apply,lyapunovRawLeft_source_residual,hp,zero_mul,sub_zero,
    lyapunovLeft_apply]
  ring

theorem critical_normalized_left (r w : ℝ) (hw : w ≠ 0)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0) :
    lyapunovLeft (Complex.I*(w:ℂ)) (adjugateVector (Complex.I*(w:ℂ))) = 1 ∧
    ∀ v, lyapunovLeft (Complex.I*(w:ℂ)) ((complexSource r).mulVec v) =
      (Complex.I*(w:ℂ))*lyapunovLeft (Complex.I*(w:ℂ)) v := by
  exact ⟨lyapunovLeft_normalized _ (lyapunovPairing_critical_ne_zero r w hw hp),
    lyapunovLeft_eigen r _ hp⟩

end
end ThreeSitePhosphorylation.AttractingWitness
