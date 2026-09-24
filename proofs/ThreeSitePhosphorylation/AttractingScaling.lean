import proofs.ThreeSitePhosphorylation.AttractingFlow

namespace ThreeSitePhosphorylation.AttractingWitness
noncomputable section
open Filter
open scoped Topology

/-- Exact amplitude-state scaling of the literal quadratic source. -/
theorem rescaledField_scaling (a r s : ℝ) (hs : s ≠ 0) (y : ReducedState) :
    rescaledField (a/s) r (s • y) = s • rescaledField a r y := by
  simp only [rescaledField,map_smul,quadraticPart_homogeneous,smul_add,smul_smul]
  have hc : a/s*(s*s)=s*a := by field_simp
  rw [hc]

theorem pathQuadratic_scaling (r s : ℝ) (u : SourcePath) :
    pathQuadratic r (s • u) = (s*s) • pathQuadratic r u := by
  ext t i
  change pathQuadratic r (s • u) t i = ((s*s) • pathQuadratic r u t) i
  rw [pathQuadratic_apply,pathQuadratic_apply]
  change quadraticPart r (s • u t) i = ((s*s) • quadraticPart r (u t)) i
  rw [quadraticPart_homogeneous]

theorem pathField_scaling (a r T s : ℝ) (hs : s ≠ 0) (u : SourcePath) :
    pathField (a/s,(r,T)) (s • u) = s • pathField (a,(r,T)) u := by
  ext t i
  change pathField (a/s,(r,T)) (s • u) t i = (s • pathField (a,(r,T)) u t) i
  rw [pathField_apply,pathField_apply]
  change (T • rescaledField (a/s) r (s • u t)) i = (s • (T • rescaledField a r (u t))) i
  rw [rescaledField_scaling a r s hs,smul_comm T s]

/-- The full Volterra residual respects the same exact scaling. -/
theorem pathResidual_scaling (a r T s : ℝ) (hs : s ≠ 0)
    (x : ReducedState) (u : SourcePath) :
    pathResidual (((a/s,(r,T)),s • x),s • u) =
      s • pathResidual (((a,(r,T)),x),u) := by
  simp only [pathResidual,pathField_scaling a r T s hs,map_smul,smul_sub]

theorem pathResidual_scaling_zero_iff (a r T s : ℝ) (hs : s ≠ 0)
    (x : ReducedState) (u : SourcePath) :
    pathResidual (((a/s,(r,T)),s • x),s • u) = 0 ↔
      pathResidual (((a,(r,T)),x),u) = 0 := by
  rw [pathResidual_scaling a r T s hs,smul_eq_zero]
  simp [hs]

/-- Differentiating an actual local scaling identity gives its Euler identity.
For a return map, the scaling identity itself must first be established. -/
theorem scaling_euler_identity {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : ℝ × E → G) (a : ℝ) (x : E) (D : (ℝ × E) →L[ℝ] G)
    (hD : HasFDerivAt F D (a,x))
    (hscale : ∀ᶠ s in 𝓝 (1 : ℝ), F (a/s,s • x) = s • F (a,x)) :
    D (-a,x) = F (a,x) := by
  have ha : HasDerivAt (fun s : ℝ => a/s) (-a) 1 := by
    simpa using (hasDerivAt_const (1 : ℝ) a).div (hasDerivAt_id (1 : ℝ)) (by norm_num)
  have hx : HasDerivAt (fun s : ℝ => s • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have hD' : HasFDerivAt F D (a/1,(1 : ℝ) • x) := by simpa using hD
  have hh := hD'.comp_hasDerivAt (1 : ℝ) (ha.prodMk hx)
  have hr0 : HasDerivAt (fun s : ℝ => s • F (a,x)) (F (a,x)) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const (F (a,x))
  have hr : HasDerivAt (fun s : ℝ => F (a/s,s • x)) (F (a,x)) 1 :=
    hr0.congr_of_eventuallyEq hscale
  exact hh.unique hr

/-- Euler scaling and differentiation of a fixed branch give the radial
state equation. Both differential identities are explicit hypotheses. -/
theorem branch_scaling_linear_identity {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : (ℝ × (ℝ × E)) →L[ℝ] E) (a r' : ℝ) (x x' : E)
    (hEuler : D (-a,(0,x)) = x) (hBranch : D (1,(r',x')) = x') :
    D (0,(0,x+a • x')) - (x+a • x') = (-a*r') • D (0,(1,0)) := by
  have hv : ((0:ℝ),((0:ℝ),x+a • x')) =
      (-a,((0:ℝ),x)) + a • ((1:ℝ),(r',x')) - (a*r') • ((0:ℝ),((1:ℝ),(0:E))) := by
    ext <;> simp
  rw [hv,map_sub,map_add,map_smul,map_smul,hEuler,hBranch]
  module

theorem branch_scaling_left_identity {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : (ℝ × (ℝ × E)) →L[ℝ] E) (a r' μ : ℝ) (x x' : E)
    (l : E →ₗ[ℝ] ℝ)
    (hEuler : D (-a,(0,x)) = x) (hBranch : D (1,(r',x')) = x')
    (hleft : ∀ v, l (D (0,(0,v))) = μ*l v) :
    (μ-1)*l (x+a • x') = (-a*r')*l (D (0,(1,0))) := by
  have hh := congrArg l (branch_scaling_linear_identity D a r' x x' hEuler hBranch)
  simp only [map_sub,map_smul,smul_eq_mul,hleft] at hh
  linear_combination hh

/-- These signs put the radial eigenvalue strictly below one; a lower
bound, spectral isolation, and source docking remain separate obligations. -/
theorem branch_scaling_left_lt_one {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : (ℝ × (ℝ × E)) →L[ℝ] E) (a r' μ : ℝ) (x x' : E)
    (l : E →ₗ[ℝ] ℝ)
    (hEuler : D (-a,(0,x)) = x) (hBranch : D (1,(r',x')) = x')
    (hleft : ∀ v, l (D (0,(0,v))) = μ*l v)
    (ha : 0<a) (hr : r'<0) (hp : l (D (0,(1,0)))<0)
    (hv : 0<l (x+a • x')) : μ<1 := by
  have hh := branch_scaling_left_identity D a r' μ x x' l hEuler hBranch hleft
  have hpos : 0 < -a*r' := mul_pos_of_neg_of_neg (by linarith) hr
  have hneg := mul_neg_of_pos_of_neg hpos hp
  nlinarith

end
end ThreeSitePhosphorylation.AttractingWitness
