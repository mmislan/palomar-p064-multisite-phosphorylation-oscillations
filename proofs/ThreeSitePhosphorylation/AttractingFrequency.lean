import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-! Exact scalar certificate for witness A. Source docking is in
AttractingSpectral; this file alone makes no source eigenvalue claim. -/
namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section
set_option maxHeartbeats 1500000

def frequencyPolynomial (t : ℝ) : ℝ :=
  (145/552)*t^8 + (164080190390061748577/136712305440000000)*t^7 + (4986060771899292958761386733617/4254165269280000000000000)*t^6 + (41628757430417616496911430476085897452841/122041366162470000000000000000000)*t^5 + (1115685484107323815962991600425072210111485743/152551707703087500000000000000000000)*t^4 + (889950332318024978194733139883387878601427701919/31781605771476562500000000000000000000)*t^3 + (11036156194634528287632349057623875778520661/27588199454406738281250000000000000)*t^2 + (-12116099996770782228713817865450069909559/114950831060028076171875000000000)*t^1 + (-4768770897113492996902621415394764/24945926879346370697021484375)*t^0

def even0 (t : ℝ) : ℝ :=
  (869379059/7038000)*t^4 + (-2268022646334229960049/33507918000000000)*t^3 + (46614837240281630174067101/83769795000000000000)*t^2 + (118846275934324197547273/34904081250000000000)*t^1 + (533510085136988654/3787335205078125)*t^0

def odd0 (t : ℝ) : ℝ :=
  (1)*t^4 + (-1123287418214581/242811000000)*t^3 + (150436261805724529928987/418848975000000000)*t^2 + (-10386606547280019362335297/139616325000000000000)*t^1 + (266708962258783276681/90896044921875000)*t^0

def even1 (t : ℝ) : ℝ :=
  (145/552)*t^4 + (-1328396252697850573/1340316720000000)*t^3 + (931837933283894317481801/16753959000000000000)*t^2 + (-1085025848693755537444247/34904081250000000000)*t^1 + (533510085136988654/3787335205078125)*t^0

def odd1 (t : ℝ) : ℝ :=
  (-535682119897/19424880000)*t^3 + (383465940690669782329/27923265000000000)*t^2 + (-10804886710795876287254177/139616325000000000000)*t^1 + (390060029489815107481/90896044921875000)*t^0

def frequencyLower : ℝ := (276313501/5000000000)
def frequencyUpper : ℝ := (552627003/10000000000)

theorem frequency_signs : frequencyPolynomial frequencyLower < 0 ∧
    0 < frequencyPolynomial frequencyUpper := by
  norm_num [frequencyPolynomial,frequencyLower,frequencyUpper]

theorem positive_frequency_exists : ∃ t : ℝ,
    frequencyLower ≤ t ∧ t ≤ frequencyUpper ∧ 0 < t ∧ frequencyPolynomial t = 0 := by
  have hab : frequencyLower ≤ frequencyUpper := by norm_num [frequencyLower,frequencyUpper]
  have hc : Continuous frequencyPolynomial := by unfold frequencyPolynomial; fun_prop
  have hm : (0:ℝ) ∈ Set.Icc (frequencyPolynomial frequencyLower)
      (frequencyPolynomial frequencyUpper) := ⟨frequency_signs.1.le,frequency_signs.2.le⟩
  obtain ⟨t,ht,hz⟩ := intermediate_value_Icc hab hc.continuousOn hm
  exact ⟨t,ht.1,ht.2,lt_of_lt_of_le (by norm_num [frequencyLower]) ht.1,hz⟩

theorem frequency_elimination_identity (t : ℝ) :
    frequencyPolynomial t = odd0 t*even1 t-even0 t*odd1 t := by
  unfold frequencyPolynomial even0 odd0 even1 odd1
  ring

theorem frequency_even_signs (t : ℝ) (ht : frequencyLower ≤ t ∧ t ≤ frequencyUpper) :
    0 < even0 t ∧ even1 t < 0 := by
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
  constructor
  · unfold even0
    linarith only [ht.1,ht.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]
  · unfold even1
    linarith only [ht.1,ht.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]

theorem admissible_frequency_exists : ∃ t r : ℝ,
    0 < t ∧ 0 < r ∧ frequencyLower ≤ t ∧ t ≤ frequencyUpper ∧
    even0 t+r*even1 t = 0 ∧ odd0 t+r*odd1 t = 0 := by
  obtain ⟨t,hl,hu,ht,hphi⟩ := positive_frequency_exists
  have hs := frequency_even_signs t ⟨hl,hu⟩
  have hn : even1 t ≠ 0 := ne_of_lt hs.2
  have hr : 0 < -(even0 t)/(even1 t) := div_pos_of_neg_of_neg (neg_neg_of_pos hs.1) hs.2
  refine ⟨t,-(even0 t)/(even1 t),ht,hr,hl,hu,?_,?_⟩
  · field_simp
    ring
  · rw [frequency_elimination_identity] at hphi
    field_simp
    nlinarith only [hphi]

def candidatePolynomial (r : ℝ) (z : ℂ) : ℂ :=
  (((1)+r*(0):ℝ):ℂ)*z^9 +
  (((869379059/7038000)+r*(145/552):ℝ):ℂ)*z^8 +
  (((1123287418214581/242811000000)+r*(535682119897/19424880000):ℝ):ℂ)*z^7 +
  (((2268022646334229960049/33507918000000000)+r*(1328396252697850573/1340316720000000):ℝ):ℂ)*z^6 +
  (((150436261805724529928987/418848975000000000)+r*(383465940690669782329/27923265000000000):ℝ):ℂ)*z^5 +
  (((46614837240281630174067101/83769795000000000000)+r*(931837933283894317481801/16753959000000000000):ℝ):ℂ)*z^4 +
  (((10386606547280019362335297/139616325000000000000)+r*(10804886710795876287254177/139616325000000000000):ℝ):ℂ)*z^3 +
  (((-118846275934324197547273/34904081250000000000)+r*(1085025848693755537444247/34904081250000000000):ℝ):ℂ)*z^2 +
  (((266708962258783276681/90896044921875000)+r*(390060029489815107481/90896044921875000):ℝ):ℂ)*z^1 +
  (((533510085136988654/3787335205078125)+r*(533510085136988654/3787335205078125):ℝ):ℂ)*z^0

theorem candidate_at_imaginary (r w : ℝ) :
    candidatePolynomial r (Complex.I*(w:ℂ)) =
      ((even0 (w^2)+r*even1 (w^2):ℝ):ℂ) +
      Complex.I*(w:ℂ)*((odd0 (w^2)+r*odd1 (w^2):ℝ):ℂ) := by
  apply Complex.ext <;>
    simp [candidatePolynomial,even0,odd0,even1,odd1,pow_succ,
      Complex.mul_re,Complex.mul_im] <;> ring

end
end ThreeSitePhosphorylation.AttractingWitness
