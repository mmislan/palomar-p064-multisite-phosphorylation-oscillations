import proofs.ThreeSitePhosphorylation.MultisiteCenteredFace
import proofs.ThreeSitePhosphorylation.ScaledAffineFamily

/-! Literal exact quadratic expansion of the reduced chemical source.
The full fixed-total tangent, including S0,E,F, is retained throughout. -/
namespace ThreeSitePhosphorylation.MultisiteTaylor
noncomputable section
open PhosphorylationSharpness MultisiteChart MultisiteCenteredFace ScaledAffineFamily
open scoped BigOperators
set_option maxHeartbeats 700000

def sourceRow {n : ℕ} (i j : Fin n) (a b c d : ℝ) : ℝ :=
  (if i.castSucc=j.succ then -a+d else 0) + (if i.succ=j.succ then c-b else 0)

def assemble {n : ℕ} (a b c d : Fin n → ℝ) : ReducedState n :=
  (fun j => ∑ i, sourceRow i j (a i) (b i) (c i) (d i),
    (fun i => a i-c i,fun i => b i-d i))

theorem sourceRow_affine {n : ℕ} (i j : Fin n)
    (a b c d a' b' c' d' a'' b'' c'' d'' t : ℝ) :
    sourceRow i j (a+a'+t*a'') (b+b'+t*b'') (c+c'+t*c'') (d+d'+t*d'') =
      sourceRow i j a b c d + sourceRow i j a' b' c' d' +
        t*sourceRow i j a'' b'' c'' d'' := by
  unfold sourceRow
  split_ifs <;> ring

theorem assemble_affine {n : ℕ} (a b c d a' b' c' d' a'' b'' c'' d'' : Fin n → ℝ)
    (t : ℝ) :
    assemble (a+a'+t • a'') (b+b'+t • b'') (c+c'+t • c'') (d+d'+t • d'') =
      assemble a b c d + assemble a' b' c' d' + t • assemble a'' b'' c'' d'' := by
  ext j <;>
    simp [assemble,sourceRow_affine,Finset.sum_add_distrib,Finset.mul_sum] <;> ring

theorem assemble_zero {n : ℕ} : assemble (0 : Fin n → ℝ) 0 0 0 = 0 := by
  ext i <;> simp [assemble,sourceRow]

theorem assemble_add_smul {n : ℕ} (a b c d a' b' c' d' : Fin n → ℝ) (t : ℝ) :
    assemble (a+t • a') (b+t • b') (c+t • c') (d+t • d') =
      assemble a b c d + t • assemble a' b' c' d' := by
  simpa only [add_zero,assemble_zero] using
    assemble_affine a b c d 0 0 0 0 a' b' c' d' t

theorem project_field {n : ℕ} (k : Rates n) (x : PhosphorylationSharpness.State n) :
    project (field k x) = assemble (kinaseNet k x) (phosphataseNet k x)
      (fun i => k.c i*x.C i) (fun i => k.gamma i*x.D i) := rfl

/-- Fixed-total chart translation has precisely the zero-total tangent.
In particular its S0,E,F components vary with the retained inventories. -/
theorem chart_translation {n : ℕ} (x : PhosphorylationSharpness.State n) (y : ReducedState n) :
    let z := chart (totalE x) (totalF x) (totalS x) (project x+y)
    (∀ i, z.S i=x.S i+(tangent y).S i) ∧ z.E=x.E+(tangent y).E ∧
      z.F=x.F+(tangent y).F ∧ (∀ i, z.C i=x.C i+(tangent y).C i) ∧
      (∀ i, z.D i=x.D i+(tangent y).D i) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [chart,project,tangent,totalS,Fin.sum_univ_succ,Finset.sum_add_distrib]
      ring
    · rfl
  · simp [chart,project,tangent,totalE,Finset.sum_add_distrib]
    ring
  · simp [chart,project,tangent,totalF,Finset.sum_add_distrib]
    ring
  · intro i; rfl
  · intro i; rfl

def linearKinase {n : ℕ} (k : Rates n) (x : PhosphorylationSharpness.State n)
    (y : ReducedState n) (i : Fin n) : ℝ :=
  k.a i*((tangent y).S i.castSucc*x.E+x.S i.castSucc*(tangent y).E)-k.b i*(tangent y).C i

def linearPhosphatase {n : ℕ} (k : Rates n) (x : PhosphorylationSharpness.State n)
    (y : ReducedState n) (i : Fin n) : ℝ :=
  k.alpha i*((tangent y).S i.succ*x.F+x.S i.succ*(tangent y).F)-k.beta i*(tangent y).D i

def bilinearKinase {n : ℕ} (k : Rates n) (u v : ReducedState n) (i : Fin n) : ℝ :=
  k.a i*((tangent u).S i.castSucc*(tangent v).E+(tangent v).S i.castSucc*(tangent u).E)

def bilinearPhosphatase {n : ℕ} (k : Rates n) (u v : ReducedState n) (i : Fin n) : ℝ :=
  k.alpha i*((tangent u).S i.succ*(tangent v).F+(tangent v).S i.succ*(tangent u).F)

def linearTerm {n : ℕ} (k : Rates n) (x : PhosphorylationSharpness.State n)
    (y : ReducedState n) : ReducedState n :=
  assemble (linearKinase k x y) (linearPhosphatase k x y)
    (fun i => k.c i*(tangent y).C i) (fun i => k.gamma i*(tangent y).D i)

def bilinearTerm {n : ℕ} (k : Rates n) (u v : ReducedState n) : ReducedState n :=
  assemble (bilinearKinase k u v) (bilinearPhosphatase k u v) 0 0

theorem bilinearTerm_symmetric {n : ℕ} (k : Rates n) (u v : ReducedState n) :
    bilinearTerm k u v = bilinearTerm k v u := by
  have ha : bilinearKinase k u v = bilinearKinase k v u := by
    funext i
    simp only [bilinearKinase,add_comm]
  have hb : bilinearPhosphatase k u v = bilinearPhosphatase k v u := by
    funext i
    simp only [bilinearPhosphatase,add_comm]
  unfold bilinearTerm
  rw [ha,hb]

theorem tangent_add_smul {n : ℕ} (u v : ReducedState n) (t : ℝ) :
    (∀ i, (tangent (u+t • v)).S i=(tangent u).S i+t*(tangent v).S i) ∧
    (tangent (u+t • v)).E=(tangent u).E+t*(tangent v).E ∧
    (tangent (u+t • v)).F=(tangent u).F+t*(tangent v).F ∧
    (∀ i, (tangent (u+t • v)).C i=(tangent u).C i+t*(tangent v).C i) ∧
    (∀ i, (tangent (u+t • v)).D i=(tangent u).D i+t*(tangent v).D i) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [tangent,chart,Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum]
      ring
    · rfl
  · simp [tangent,chart,Finset.sum_add_distrib,Finset.mul_sum]
    ring
  · simp [tangent,chart,Finset.sum_add_distrib,Finset.mul_sum]
    ring
  · intro i; rfl
  · intro i; rfl

theorem linearTerm_add_smul {n : ℕ} (k : Rates n) (x : PhosphorylationSharpness.State n)
    (u v : ReducedState n) (t : ℝ) :
    linearTerm k x (u+t • v) = linearTerm k x u + t • linearTerm k x v := by
  obtain ⟨hS,hE,hF,hC,hD⟩ := tangent_add_smul u v t
  have ha : linearKinase k x (u+t • v) = linearKinase k x u+t • linearKinase k x v := by
    funext i
    simp only [linearKinase,hS,hE,hC,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have hb : linearPhosphatase k x (u+t • v) =
      linearPhosphatase k x u+t • linearPhosphatase k x v := by
    funext i
    simp only [linearPhosphatase,hS,hF,hD,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have hc : (fun i => k.c i*(tangent (u+t • v)).C i) =
      (fun i => k.c i*(tangent u).C i)+t • (fun i => k.c i*(tangent v).C i) := by
    funext i
    simp only [hC,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have hd : (fun i => k.gamma i*(tangent (u+t • v)).D i) =
      (fun i => k.gamma i*(tangent u).D i)+t • (fun i => k.gamma i*(tangent v).D i) := by
    funext i
    simp only [hD,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  unfold linearTerm
  rw [ha,hb,hc,hd,assemble_add_smul]

theorem bilinearTerm_add_smul_right {n : ℕ} (k : Rates n)
    (u v z : ReducedState n) (t : ℝ) :
    bilinearTerm k u (v+t • z) = bilinearTerm k u v+t • bilinearTerm k u z := by
  obtain ⟨hS,hE,hF,_,_⟩ := tangent_add_smul v z t
  have ha : bilinearKinase k u (v+t • z) =
      bilinearKinase k u v+t • bilinearKinase k u z := by
    funext i
    simp only [bilinearKinase,hS,hE,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have hb : bilinearPhosphatase k u (v+t • z) =
      bilinearPhosphatase k u v+t • bilinearPhosphatase k u z := by
    funext i
    simp only [bilinearPhosphatase,hS,hF,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  unfold bilinearTerm
  rw [ha,hb]
  simpa only [smul_zero,add_zero] using assemble_add_smul
    (bilinearKinase k u v) (bilinearPhosphatase k u v) 0 0
    (bilinearKinase k u z) (bilinearPhosphatase k u z) 0 0 t

theorem bilinearTerm_add_smul_left {n : ℕ} (k : Rates n)
    (u v z : ReducedState n) (t : ℝ) :
    bilinearTerm k (u+t • v) z = bilinearTerm k u z+t • bilinearTerm k v z := by
  rw [bilinearTerm_symmetric k (u+t • v) z,bilinearTerm_add_smul_right,
    bilinearTerm_symmetric k z u,bilinearTerm_symmetric k z v]

/-- Both coefficients of the exact expansion depend linearly on the six
rate arrays. In particular an affine kinetic parameter gives an affine
linear part and an affine quadratic tensor, with no moving center. -/
theorem linearTerm_affine_rates {n : ℕ} (k0 k1 : Rates n)
    (x : PhosphorylationSharpness.State n) (r : ℝ) (y : ReducedState n) :
    linearTerm (affineRates k0 k1 r) x y = linearTerm k0 x y + r • linearTerm k1 x y := by
  have ha : linearKinase (affineRates k0 k1 r) x y =
      linearKinase k0 x y + r • linearKinase k1 x y := by
    funext i
    simp [linearKinase,affineRates]
    ring
  have hb : linearPhosphatase (affineRates k0 k1 r) x y =
      linearPhosphatase k0 x y + r • linearPhosphatase k1 x y := by
    funext i
    simp [linearPhosphatase,affineRates]
    ring
  have hc : (fun i => (affineRates k0 k1 r).c i*(tangent y).C i) =
      (fun i => k0.c i*(tangent y).C i) + r • (fun i => k1.c i*(tangent y).C i) := by
    funext i
    simp [affineRates]
    ring
  have hd : (fun i => (affineRates k0 k1 r).gamma i*(tangent y).D i) =
      (fun i => k0.gamma i*(tangent y).D i) + r • (fun i => k1.gamma i*(tangent y).D i) := by
    funext i
    simp [affineRates]
    ring
  unfold linearTerm
  rw [ha,hb,hc,hd,assemble_add_smul]

theorem bilinearTerm_affine_rates {n : ℕ} (k0 k1 : Rates n)
    (r : ℝ) (u v : ReducedState n) :
    bilinearTerm (affineRates k0 k1 r) u v =
      bilinearTerm k0 u v + r • bilinearTerm k1 u v := by
  have ha : bilinearKinase (affineRates k0 k1 r) u v =
      bilinearKinase k0 u v + r • bilinearKinase k1 u v := by
    funext i
    simp [bilinearKinase,affineRates]
    ring
  have hb : bilinearPhosphatase (affineRates k0 k1 r) u v =
      bilinearPhosphatase k0 u v + r • bilinearPhosphatase k1 u v := by
    funext i
    simp [bilinearPhosphatase,affineRates]
    ring
  unfold bilinearTerm
  rw [ha,hb]
  simpa only [smul_zero,add_zero] using assemble_add_smul
    (bilinearKinase k0 u v) (bilinearPhosphatase k0 u v) 0 0
    (bilinearKinase k1 u v) (bilinearPhosphatase k1 u v) 0 0 r

theorem exact_expansion {n : ℕ} (k : Rates n) (x : PhosphorylationSharpness.State n)
    (y : ReducedState n) :
    centeredField (totalE x) (totalF x) (totalS x) k (project x) y =
      project (field k x) + linearTerm k x y + (1/2 : ℝ) • bilinearTerm k y y := by
  let z := chart (totalE x) (totalF x) (totalS x) (project x+y)
  obtain ⟨hS,hE,hF,hC,hD⟩ := chart_translation x y
  have ha : kinaseNet k z = kinaseNet k x + linearKinase k x y +
      (1/2 : ℝ) • bilinearKinase k y y := by
    funext i
    change k.a i*z.S i.castSucc*z.E-k.b i*z.C i = _
    rw [hS,hE,hC]
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,kinaseNet,linearKinase,bilinearKinase]
    ring
  have hb : phosphataseNet k z = phosphataseNet k x + linearPhosphatase k x y +
      (1/2 : ℝ) • bilinearPhosphatase k y y := by
    funext i
    change k.alpha i*z.S i.succ*z.F-k.beta i*z.D i = _
    rw [hS,hF,hD]
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,phosphataseNet,linearPhosphatase,bilinearPhosphatase]
    ring
  have hc : (fun i => k.c i*z.C i) =
      (fun i => k.c i*x.C i) + (fun i => k.c i*(tangent y).C i) + (1/2 : ℝ) • 0 := by
    funext i
    rw [hC]
    simp [mul_add]
  have hd : (fun i => k.gamma i*z.D i) =
      (fun i => k.gamma i*x.D i) + (fun i => k.gamma i*(tangent y).D i) + (1/2 : ℝ) • 0 := by
    funext i
    rw [hD]
    simp [mul_add]
  change project (field k z) = _
  rw [project_field,ha,hb,hc,hd,assemble_affine,project_field]
  rfl

theorem equilibrium_expansion {n : ℕ} (k : Rates n) (x : PhosphorylationSharpness.State n)
    (hx : Equilibrium k x) (y : ReducedState n) :
    centeredField (totalE x) (totalF x) (totalS x) k (project x) y =
      linearTerm k x y + (1/2 : ℝ) • bilinearTerm k y y := by
  have hz : project (field k x)=0 := by
    apply Prod.ext
    · exact funext (fun i => hx.1 i.succ)
    · exact Prod.ext (funext hx.2.2.2.1) (funext hx.2.2.2.2)
  rw [exact_expansion,hz,zero_add]

end
end ThreeSitePhosphorylation.MultisiteTaylor
