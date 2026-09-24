import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! Exact local source identities for the site-addition construction of P064.
These establish equilibrium, conserved inventories and stability of the added
limiting block. They do not assert Hopf persistence or attraction. -/
namespace ThreeSitePhosphorylation.AddedSite
noncomputable section

abbrev LocalState := Fin 6 → ℝ

/- Species order: old terminal substrate, free E, free F, new C, new S, new D.
The six reactions are the new kinase and phosphatase arms alone. -/
def field (a α : ℝ) (x : LocalState) : LocalState :=
  ![-a*x 0*x 1+x 3+x 5, -a*x 0*x 1+2*x 3,
    -α*x 4*x 2+2*x 5, a*x 0*x 1-2*x 3,
    x 3-α*x 4*x 2+x 5, α*x 4*x 2-2*x 5]

def equilibrium (s e f ε : ℝ) : LocalState := ![s,e,f,ε,2*ε,ε]

theorem equilibrium_positive (s e f ε : ℝ)
    (hs : 0 < s) (he : 0 < e) (hf : 0 < f) (hε : 0 < ε) :
    ∀ i, 0 < equilibrium s e f ε i := by
  intro i
  fin_cases i <;> simp [equilibrium] <;> positivity

theorem rates_positive (s e f ε : ℝ)
    (hs : 0 < s) (he : 0 < e) (hf : 0 < f) (hε : 0 < ε) :
    0 < 2*ε/(s*e) ∧ 0 < 1/f := by
  constructor <;> positivity

theorem equilibrium_stationary (s e f ε : ℝ)
    (hs : s ≠ 0) (he : e ≠ 0) (hf : f ≠ 0) :
    field (2*ε/(s*e)) (1/f) (equilibrium s e f ε) = 0 := by
  funext i
  fin_cases i <;> simp [field, equilibrium] <;> field_simp <;> ring

theorem inventories_conserved (a α : ℝ) (x : LocalState) :
    (field a α x) 1 + (field a α x) 3 = 0 ∧
    (field a α x) 2 + (field a α x) 5 = 0 ∧
    (field a α x) 0 + (field a α x) 3 +
      (field a α x) 4 + (field a α x) 5 = 0 := by
  simp [field]
  ring

theorem inventory_increments (s e f ε : ℝ) :
    (equilibrium s e f ε) 3 = ε ∧
    (equilibrium s e f ε) 5 = ε ∧
    (equilibrium s e f ε) 3 + (equilibrium s e f ε) 4 +
      (equilibrium s e f ε) 5 = 4*ε := by
  simp [equilibrium]
  ring

theorem zero_load_face (s e f α : ℝ) :
    field 0 α ![s,e,f,0,0,0] = 0 := by
  funext i
  fin_cases i <;> simp [field]

/- Exact first-order expansion of the three new equations at zero load.
The first-order coefficient is independent of all old coordinate variations;
the variation in free phosphatase enters only the quadratic remainder. -/
theorem zero_load_expansion (s e f df c q d t : ℝ) (hf : f ≠ 0) :
    let v := field 0 (1/f) ![s,e,f+t*df,t*c,t*q,t*d]
    ![v 3,v 4,v 5] =
      t • (![-2*c,c-q+d,q-2*d] : Fin 3 → ℝ) +
      t^2 • (![0,-df*q/f,df*q/f] : Fin 3 → ℝ) := by
  dsimp
  funext i
  fin_cases i <;> simp [field] <;> field_simp <;> ring

def limitingBlock : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-2,0,0; 1,-1,1; 0,1,-2]

theorem limitingBlock_characteristic (z : ℂ) :
    Matrix.det (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) - limitingBlock) =
      (z+2)*(z^2+3*z+1) := by
  simp [limitingBlock, Matrix.det_fin_three, Matrix.sub_apply,
    Matrix.smul_apply]
  ring

theorem quadratic_roots_stable (z : ℂ) (hz : z^2+3*z+1 = 0) : z.re < 0 := by
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hr hi
  by_contra hn
  have hx : 0 ≤ z.re := le_of_not_gt hn
  have hy : z.im = 0 := by nlinarith
  rw [hy] at hr
  nlinarith [sq_nonneg z.re]

theorem limitingBlock_roots_stable (z : ℂ)
    (hz : Matrix.det (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) - limitingBlock) = 0) :
    z.re < 0 := by
  rw [limitingBlock_characteristic] at hz
  rcases mul_eq_zero.mp hz with h | h
  · have he : z = -2 := by linear_combination h
    rw [he]
    norm_num
  · exact quadratic_roots_stable z h

section LyapunovEmbedding
variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/- The quadratic-field cubic vector in the standard first Lyapunov formula.
I and R stand for J⁻¹ and (2 i ω - J)⁻¹. Their analytic existence is not
asserted here. qbar is supplied explicitly as the conjugate eigenvector. -/
def quadraticLyapunovVector (B : V → V → V) (I R : V → V) (q qbar : V) : V :=
  B qbar (R (B q q)) - (2 : ℂ) • B q (I (B q qbar))

/- Conditional algebraic transport: the hypotheses are precisely the
restriction identities that the full site-addition field must establish. -/
theorem quadraticLyapunovVector_embedding
    (j : V →ₗ[ℂ] W) (B : V → V → V) (B' : W → W → W)
    (I R : V → V) (I' R' : W → W)
    (hB : ∀ x y, B' (j x) (j y) = j (B x y))
    (hI : ∀ x, I' (j x) = j (I x))
    (hR : ∀ x, R' (j x) = j (R x)) (q qbar : V) :
    quadraticLyapunovVector B' I' R' (j q) (j qbar) =
      j (quadraticLyapunovVector B I R q qbar) := by
  simp only [quadraticLyapunovVector, hB, hI, hR, map_sub, map_smul]

theorem quadraticLyapunovCoefficient_embedding
    (j : V →ₗ[ℂ] W) (B : V → V → V) (B' : W → W → W)
    (I R : V → V) (I' R' : W → W)
    (hB : ∀ x y, B' (j x) (j y) = j (B x y))
    (hI : ∀ x, I' (j x) = j (I x))
    (hR : ∀ x, R' (j x) = j (R x))
    (p : V → ℂ) (p' : W → ℂ) (hp : ∀ x, p' (j x) = p x)
    (q qbar : V) (ω : ℝ) :
    (p' (quadraticLyapunovVector B' I' R' (j q) (j qbar))).re / (2*ω) =
      (p (quadraticLyapunovVector B I R q qbar)).re / (2*ω) := by
  rw [quadraticLyapunovVector_embedding j B B' I R I' R' hB hI hR, hp]

end LyapunovEmbedding

end
end ThreeSitePhosphorylation.AddedSite
