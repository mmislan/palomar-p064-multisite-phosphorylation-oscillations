import proofs.ThreeSitePhosphorylation.AttractingEigenbasis

/-! A simple imaginary eigenvalue of the literal witness A crosses transversely.
This remains a spectral theorem; it does not infer nonlinear orbit stability. -/
namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section
open scoped Topology
set_option maxHeartbeats 1500000

theorem eliminant_slope_at_root
    (E₀ O₀ E₁ O₁ dE₀ dO₀ dE₁ dO₁ r : ℝ)
    (he : E₀+r*E₁=0) (ho : O₀+r*O₁=0) :
    dO₀*E₁+O₀*dE₁-dE₀*O₁-E₀*dO₁ =
      E₁*(dO₀+r*dO₁)-O₁*(dE₀+r*dE₁) := by
  have he' : E₀ = -r*E₁ := by linarith
  have ho' : O₀ = -r*O₁ := by linarith
  rw [he',ho']
  ring

theorem crossing_quotient_negative (t E₁ O₁ dE dO slope : ℝ)
    (ht : 0 < t) (hs : 0 < slope) (he : slope=E₁*dO-O₁*dE) :
    0 < t*dO^2+dE^2 ∧ -slope/(2*(t*dO^2+dE^2)) < 0 := by
  have hz : dO ≠ 0 ∨ dE ≠ 0 := by
    by_contra h
    push Not at h
    rcases h with ⟨ho,heq⟩
    simp [ho,heq] at he
    linarith
  have hd : 0 < t*dO^2+dE^2 := by
    rcases hz with ho | heq
    · have hh : 0 < dO^2 := sq_pos_of_ne_zero ho
      nlinarith [mul_pos ht hh,sq_nonneg dE]
    · have hh : 0 < dE^2 := sq_pos_of_ne_zero heq
      have hn : 0 ≤ t*dO^2 := mul_nonneg ht.le (sq_nonneg dO)
      linarith
  exact ⟨hd,div_neg_of_neg_of_pos (neg_neg_of_pos hs) (by positivity)⟩


def frequencySlope (t : ℝ) : ℝ := (145/69)*t^7 + (1148561332730432240039/136712305440000000)*t^6 + (4986060771899292958761386733617/709027544880000000000000)*t^5 + (41628757430417616496911430476085897452841/24408273232494000000000000000000)*t^4 + (1115685484107323815962991600425072210111485743/38137926925771875000000000000000000)*t^3 + (889950332318024978194733139883387878601427701919/10593868590492187500000000000000000000)*t^2 + (11036156194634528287632349057623875778520661/13794099727203369140625000000000000)*t^1 + (-12116099996770782228713817865450069909559/114950831060028076171875000000000)*t^0

theorem frequency_slope_positive (t : ℝ) (ht : 0 < t)
    (hp : frequencyPolynomial t = 0) : 0 < frequencySlope t := by
  have h : t*frequencySlope t-frequencyPolynomial t =
    (1015/552)*t^8 + (164080190390061748577/22785384240000000)*t^7 + (4986060771899292958761386733617/850833053856000000000000)*t^6 + (41628757430417616496911430476085897452841/30510341540617500000000000000000)*t^5 + (1115685484107323815962991600425072210111485743/50850569234362500000000000000000000)*t^4 + (889950332318024978194733139883387878601427701919/15890802885738281250000000000000000000)*t^3 + (11036156194634528287632349057623875778520661/27588199454406738281250000000000000)*t^2 + (4768770897113492996902621415394764/24945926879346370697021484375)*t^0 := by
    unfold frequencySlope frequencyPolynomial
    ring
  have hpos : 0 < t*frequencySlope t-frequencyPolynomial t := by
    rw [h]
    positivity
  rw [hp,sub_zero] at hpos
  exact pos_of_mul_pos_right hpos ht.le

def even0Slope (t : ℝ) : ℝ := (869379059/1759500)*t^3 + (-2268022646334229960049/11169306000000000)*t^2 + (46614837240281630174067101/41884897500000000000)*t^1 + (118846275934324197547273/34904081250000000000)*t^0

def odd0Slope (t : ℝ) : ℝ := (4)*t^3 + (-1123287418214581/80937000000)*t^2 + (150436261805724529928987/209424487500000000)*t^1 + (-10386606547280019362335297/139616325000000000000)*t^0

def even1Slope (t : ℝ) : ℝ := (145/138)*t^3 + (-1328396252697850573/446772240000000)*t^2 + (931837933283894317481801/8376979500000000000)*t^1 + (-1085025848693755537444247/34904081250000000000)*t^0

def odd1Slope (t : ℝ) : ℝ := (-535682119897/6474960000)*t^2 + (383465940690669782329/13961632500000000)*t^1 + (-10804886710795876287254177/139616325000000000000)*t^0

theorem frequency_equations_of_root (r w : ℝ) (hw : w ≠ 0)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ)) = 0) :
    even0 (w^2)+r*even1 (w^2)=0 ∧ odd0 (w^2)+r*odd1 (w^2)=0 := by
  rw [candidate_at_imaginary] at hp
  have he := congrArg Complex.re hp
  have ho := congrArg Complex.im hp
  simp at he ho
  exact ⟨he,ho.resolve_left hw⟩



theorem frequency_orientation (t r : ℝ)
    (he : even0 t+r*even1 t=0) (ho : odd0 t+r*odd1 t=0) :
    frequencySlope t = even1 t*(odd0Slope t+r*odd1Slope t)-
      odd1 t*(even0Slope t+r*even1Slope t) := by
  have hd := eliminant_slope_at_root (even0 t) (odd0 t) (even1 t) (odd1 t)
    (even0Slope t) (odd0Slope t) (even1Slope t) (odd1Slope t) r he ho
  rw [← hd]
  unfold frequencySlope even0 odd0 even1 odd1 even0Slope odd0Slope even1Slope odd1Slope
  ring

theorem frequency_transverse (t r : ℝ) (ht : 0 < t)
    (he : even0 t+r*even1 t=0) (ho : odd0 t+r*odd1 t=0) :
    0 < t*(odd0Slope t+r*odd1Slope t)^2+(even0Slope t+r*even1Slope t)^2 ∧
    -frequencySlope t/(2*(t*(odd0Slope t+r*odd1Slope t)^2+
      (even0Slope t+r*even1Slope t)^2)) < 0 := by
  have hp : frequencyPolynomial t=0 := by
    rw [frequency_elimination_identity]
    linear_combination even1 t*ho-odd1 t*he
  exact crossing_quotient_negative t (even1 t) (odd1 t)
    (even0Slope t+r*even1Slope t) (odd0Slope t+r*odd1Slope t)
    (frequencySlope t) ht (frequency_slope_positive t ht hp) (frequency_orientation t r he ho)


def candidateSlope (r : ℝ) (z : ℂ) : ℂ :=
  (((1)+r*(0):ℝ):ℂ)*9*z^8 +
  (((869379059/7038000)+r*(145/552):ℝ):ℂ)*8*z^7 +
  (((1123287418214581/242811000000)+r*(535682119897/19424880000):ℝ):ℂ)*7*z^6 +
  (((2268022646334229960049/33507918000000000)+r*(1328396252697850573/1340316720000000):ℝ):ℂ)*6*z^5 +
  (((150436261805724529928987/418848975000000000)+r*(383465940690669782329/27923265000000000):ℝ):ℂ)*5*z^4 +
  (((46614837240281630174067101/83769795000000000000)+r*(931837933283894317481801/16753959000000000000):ℝ):ℂ)*4*z^3 +
  (((10386606547280019362335297/139616325000000000000)+r*(10804886710795876287254177/139616325000000000000):ℝ):ℂ)*3*z^2 +
  (((-118846275934324197547273/34904081250000000000)+r*(1085025848693755537444247/34904081250000000000):ℝ):ℂ)*2*z^1 +
  (((266708962258783276681/90896044921875000)+r*(390060029489815107481/90896044921875000):ℝ):ℂ)*1*z^0

theorem candidate_hasDerivAt (r : ℝ) (z : ℂ) :
    HasDerivAt (candidatePolynomial r) (candidateSlope r z) z := by
  convert (((((((((((hasDerivAt_pow 9 z).const_mul (((1)+r*(0):ℝ):ℂ)).add ((hasDerivAt_pow 8 z).const_mul (((869379059/7038000)+r*(145/552):ℝ):ℂ))).add ((hasDerivAt_pow 7 z).const_mul (((1123287418214581/242811000000)+r*(535682119897/19424880000):ℝ):ℂ))).add ((hasDerivAt_pow 6 z).const_mul (((2268022646334229960049/33507918000000000)+r*(1328396252697850573/1340316720000000):ℝ):ℂ))).add ((hasDerivAt_pow 5 z).const_mul (((150436261805724529928987/418848975000000000)+r*(383465940690669782329/27923265000000000):ℝ):ℂ))).add ((hasDerivAt_pow 4 z).const_mul (((46614837240281630174067101/83769795000000000000)+r*(931837933283894317481801/16753959000000000000):ℝ):ℂ))).add ((hasDerivAt_pow 3 z).const_mul (((10386606547280019362335297/139616325000000000000)+r*(10804886710795876287254177/139616325000000000000):ℝ):ℂ))).add ((hasDerivAt_pow 2 z).const_mul (((-118846275934324197547273/34904081250000000000)+r*(1085025848693755537444247/34904081250000000000):ℝ):ℂ))).add ((hasDerivAt_pow 1 z).const_mul (((266708962258783276681/90896044921875000)+r*(390060029489815107481/90896044921875000):ℝ):ℂ))).add ((hasDerivAt_pow 0 z).const_mul (((533510085136988654/3787335205078125)+r*(533510085136988654/3787335205078125):ℝ):ℂ))) using 1
  norm_num [candidatePolynomial,candidateSlope]
  ring

theorem candidate_slope_at_imaginary (r w : ℝ) :
    candidateSlope r (Complex.I*(w:ℂ)) =
      ((odd0 (w^2)+r*odd1 (w^2)+2*w^2*(odd0Slope (w^2)+r*odd1Slope (w^2)):ℝ):ℂ) -
      Complex.I*((2*w*(even0Slope (w^2)+r*even1Slope (w^2)):ℝ):ℂ) := by
  apply Complex.ext <;>
    simp [candidateSlope,odd0,odd1,odd0Slope,odd1Slope,even0Slope,even1Slope,
      pow_succ,Complex.mul_re,Complex.mul_im] <;> ring

theorem candidate_imaginary_root_simple (r w : ℝ) (hw : w ≠ 0)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0) :
    candidateSlope r (Complex.I*(w:ℂ)) ≠ 0 := by
  obtain ⟨he,ho⟩ := frequency_equations_of_root r w hw hp
  have ht := sq_pos_of_ne_zero hw
  have hpos := (frequency_transverse (w^2) r ht he ho).1
  intro hz
  rw [candidate_slope_at_imaginary,ho,zero_add] at hz
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp [pow_two,Complex.mul_re,Complex.mul_im,hw] at hr hi
  have hdo : odd0Slope (w^2)+r*odd1Slope (w^2)=0 := by
    simpa only [pow_two] using hr
  have hde : even0Slope (w^2)+r*even1Slope (w^2)=0 := by
    simpa only [pow_two] using hi
  rw [hdo,hde] at hpos
  norm_num at hpos


def candidateParameter (z : ℂ) : ℂ := candidatePolynomial 1 z-candidatePolynomial 0 z

theorem candidate_affine (r s : ℝ) (z : ℂ) :
    candidatePolynomial s z = candidatePolynomial r z + ((s-r:ℝ):ℂ)*candidateParameter z := by
  unfold candidateParameter candidatePolynomial
  push_cast
  ring

theorem candidate_parameter_at_imaginary (w : ℝ) :
    candidateParameter (Complex.I*(w:ℂ)) =
      (even1 (w^2):ℂ)+Complex.I*(w:ℂ)*(odd1 (w^2):ℂ) := by
  unfold candidateParameter
  rw [candidate_at_imaginary,candidate_at_imaginary]
  push_cast
  ring

theorem complex_crossing_real (w E O dE dO : ℝ) (hw : w ≠ 0)
    (hd : 0 < w^2*dO^2+dE^2) :
    (-((E:ℂ)+Complex.I*(w:ℂ)*(O:ℂ))/
      (((2*w^2*dO:ℝ):ℂ)-Complex.I*((2*w*dE:ℝ):ℂ))).re =
      -(E*dO-O*dE)/(2*(w^2*dO^2+dE^2)) := by
  rw [Complex.div_re]
  simp only [Complex.neg_re,Complex.neg_im,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,
    one_mul,zero_add,add_zero,sub_zero,zero_sub,Complex.normSq_apply]
  have he : (2*w^2*dO)*(2*w^2*dO)+(-(2*w*dE))*(-(2*w*dE)) =
      4*w^2*(w^2*dO^2+dE^2) := by ring
  rw [he]
  have hw2 : w^2 ≠ 0 := pow_ne_zero _ hw
  have hn : w^2*dO^2+dE^2 ≠ 0 := ne_of_gt hd
  field_simp
  ring

theorem candidate_crossing_negative (r w : ℝ) (hw : w ≠ 0)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0) :
    (-candidateParameter (Complex.I*(w:ℂ))/candidateSlope r (Complex.I*(w:ℂ))).re < 0 := by
  obtain ⟨he,ho⟩ := frequency_equations_of_root r w hw hp
  have ht := sq_pos_of_ne_zero hw
  have htrans := frequency_transverse (w^2) r ht he ho
  rw [candidate_parameter_at_imaginary,candidate_slope_at_imaginary,ho,zero_add,
    complex_crossing_real w _ _ _ _ hw htrans.1,← frequency_orientation (w^2) r he ho]
  exact htrans.2


def complexScalar (d : ℂ) : ℂ →L[ℝ] ℂ :=
  (d • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ

@[simp] theorem complexScalar_apply (d z : ℂ) : complexScalar d z = d*z := rfl

theorem complexScalar_invertible (d : ℂ) (hd : d ≠ 0) :
    (complexScalar d).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := complexScalar d⁻¹)
  · ext z; simp [hd]
  · ext z; simp [hd]

def spectralResidual (p : ℝ × ℂ) : ℂ := candidatePolynomial p.1 p.2

theorem spectralResidual_smooth : ContDiff ℝ ⊤ spectralResidual := by
  have hc : ContDiff ℝ ⊤ (fun p : ℝ × ℂ => (p.1:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_fst
  unfold spectralResidual candidatePolynomial
  push_cast
  fun_prop

theorem spectralResidual_partial (r : ℝ) (z : ℂ) :
    fderiv ℝ spectralResidual (r,z) ∘L ContinuousLinearMap.inr ℝ ℝ ℂ =
      complexScalar (candidateSlope r z) := by
  have hi : HasFDerivAt (fun u : ℂ => (r,u))
      (ContinuousLinearMap.inr ℝ ℝ ℂ) z := by
    convert (hasFDerivAt_const r z).prodMk (hasFDerivAt_id z) using 1
  have h := (spectralResidual_smooth.differentiable (by norm_num) (r,z)).hasFDerivAt
  have hc := h.comp z hi
  have hp := (candidate_hasDerivAt r z).hasFDerivAt.restrictScalars ℝ
  have he : (ContinuousLinearMap.toSpanSingleton ℂ
      (candidateSlope r z)).restrictScalars ℝ = complexScalar (candidateSlope r z) := by
    ext u
    simp [complexScalar,mul_comm]
  rw [he] at hp
  exact hc.unique hp

theorem simple_root_branch (r : ℝ) (z : ℂ)
    (hp : candidatePolynomial r z=0) (hs : candidateSlope r z ≠ 0) :
    ∃ g : ℝ → ℂ, ContDiffAt ℝ ⊤ g r ∧ g r=z ∧
      ∀ᶠ s in 𝓝 r, candidatePolynomial s (g s)=0 := by
  have hi : (fderiv ℝ spectralResidual (r,z) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℂ).IsInvertible := by
    rw [spectralResidual_partial]
    exact complexScalar_invertible _ hs
  let h := spectralResidual_smooth.contDiffAt (x := (r,z))
  refine ⟨h.implicitFunction (by simp) hi,h.contDiffAt_implicitFunction (by simp) hi,
    h.implicitFunction_apply_self (by simp) hi,?_⟩
  simpa only [spectralResidual,hp] using h.eventually_apply_implicitFunction (by simp) hi


theorem root_branch_derivative (r : ℝ) (g : ℝ → ℂ)
    (hg : DifferentiableAt ℝ g r)
    (he : ∀ᶠ s in 𝓝 r, candidatePolynomial s (g s)=0)
    (hs : candidateSlope r (g r) ≠ 0) :
    deriv g r = -candidateParameter (g r)/candidateSlope r (g r) := by
  have hcomp := (candidate_hasDerivAt r (g r)).scomp r hg.hasDerivAt
  have hparam : DifferentiableAt ℝ (fun s => candidateParameter (g s)) r := by
    have hp : Differentiable ℝ candidateParameter := by
      unfold candidateParameter candidatePolynomial
      fun_prop
    exact (hp (g r)).comp r hg
  have hlin : HasDerivAt (fun s : ℝ => ((s-r:ℝ):ℂ)) (1:ℂ) r := by
    exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).sub_const r)
  have hsum := hcomp.add (hlin.mul hparam.hasDerivAt)
  have hf : (fun s => candidatePolynomial s (g s)) =
      (fun s => candidatePolynomial r (g s)+((s-r:ℝ):ℂ)*candidateParameter (g s)) := by
    funext s
    exact candidate_affine r s (g s)
  have hd : HasDerivAt (fun s => candidatePolynomial s (g s))
      (deriv g r*candidateSlope r (g r)+candidateParameter (g r)) r := by
    rw [hf]
    simpa [Function.comp_def] using hsum
  have he' : (fun s => candidatePolynomial s (g s)) =ᶠ[𝓝 r] (fun _ => (0:ℂ)) := he
  have hz := (hd.congr_of_eventuallyEq he'.symm).unique
    (hasDerivAt_const (x := r) (c := (0:ℂ)))
  apply (eq_div_iff hs).2
  linear_combination hz



theorem source_transverse_branch_at (r w : ℝ) (hw : 0 < w)
    (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0) :
    ∃ g : ℝ → ℂ, ContDiffAt ℝ ⊤ g r ∧ g r=Complex.I*(w:ℂ) ∧
    HasDerivAt (fun s => (g s).re) (deriv g r).re r ∧ (deriv g r).re < 0 ∧
    ∀ᶠ s in 𝓝 r, ∃ v : Fin 9 → ℂ, v ≠ 0 ∧ (complexSource s).mulVec v=g s • v := by
  have hs := candidate_imaginary_root_simple r w (ne_of_gt hw) hp
  obtain ⟨g,hg,hgr,hge⟩ := simple_root_branch r (Complex.I*(w:ℂ)) hp hs
  have hd := (hg.differentiableAt (by simp)).hasDerivAt
  have hq := root_branch_derivative r g (hg.differentiableAt (by simp)) hge
    (by simpa only [hgr] using hs)
  refine ⟨g,hg,hgr,?_,?_,?_⟩
  · exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt r hd
  · rw [hq,hgr]
    exact candidate_crossing_negative r w (ne_of_gt hw) hp
  · filter_upwards [hge] with s hsp
    exact ⟨adjugateVector (g s),source_root_eigenvector s (g s) hsp⟩

theorem source_root_of_adjugate (r : ℝ) (z : ℂ)
    (he : (complexSource r).mulVec (adjugateVector z) = z • adjugateVector z) :
    candidatePolynomial r z = 0 := by
  have h := congrFun he (6 : Fin 9)
  simp only [complexSource,adjugate_residual,ite_true,Pi.smul_apply,smul_eq_mul] at h
  linear_combination -h

/-- The stable complement and transverse branch occur at the same parameter.
There is no numerical or spectral hypothesis in this existential theorem. -/
theorem source_stable_transverse_branch : ∃ r w : ℝ, ∃ x : Fin 7 → ℝ,
    ∃ b : Module.Basis SpectralIndex ℂ (Fin 9 → ℂ), ∃ g : ℝ → ℂ,
    0 < r ∧ 0 < w ∧ (7/5:ℝ)<r ∧ r<(3/2:ℝ) ∧
    frequencyLower ≤ w^2 ∧ w^2 ≤ frequencyUpper ∧ StrictMono x ∧ (∀ i, x i<0) ∧
    (∀ i, (complexSource r).mulVec (b i)=spectralValues x w i • b i) ∧
    ContDiffAt ℝ ⊤ g r ∧ g r=Complex.I*(w:ℂ) ∧
    HasDerivAt (fun s => (g s).re) (deriv g r).re r ∧ (deriv g r).re < 0 ∧
    ∀ᶠ s in 𝓝 r, ∃ v : Fin 9 → ℂ, v ≠ 0 ∧ (complexSource s).mulVec v=g s • v := by
  obtain ⟨r,w,x,hr,hw,hrl,hru,hwl,hwu,hx,hn,b,hb,he⟩ := critical_source_eigenbasis
  have he0 := he (Sum.inr (0 : Fin 2))
  rw [hb] at he0
  have hp : candidatePolynomial r (Complex.I*(w:ℂ))=0 := by
    apply source_root_of_adjugate
    simpa [spectralValues] using he0
  obtain ⟨g,hg,hgr,hd,hneg,hnear⟩ := source_transverse_branch_at r w hw hp
  exact ⟨r,w,x,b,g,hr,hw,hrl,hru,hwl,hwu,hx,hn,he,hg,hgr,hd,hneg,hnear⟩

end
end ThreeSitePhosphorylation.AttractingWitness
