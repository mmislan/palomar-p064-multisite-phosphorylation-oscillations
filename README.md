# Orbitally stable periodic orbits from a fixed positive equilibrium for affine rate families of n-site sequential distributive phosphorylation, n >= 3

Michael Mislan

Vassena showed that the mass-action sequential distributive two-site phosphorylation cycle has no Hopf bifurcation and left open whether the n-site cycle with n ≥ 3 can oscillate. The cycle has one kinase E and one phosphatase F, with reactions S_i + E ⇌ C_i → S_{i+1} + E and S_{i+1} + F ⇌ D_i → S_i + F; a compatibility class is the set of states sharing the three conserved kinase, phosphatase and substrate totals. For every n ≥ 3 we construct rate constants k(r), each an affine function of a real parameter r and positive for r near 0, and a positive state x that is an equilibrium for every r. There are ω > 0 and, for all sufficiently small a > 0, a parameter value par(a) < 0 with positive rates and a nonconstant, strictly positive periodic solution γ_a in the compatibility class of x. As a → 0, par(a) → 0, the periods tend to 2π/ω and γ_a converges uniformly to x. Each orbit is orbitally asymptotically stable relative to its compatibility class: for every ε > 0, every state with the totals of x in some open neighbourhood of the orbit has a unique forward solution, which stays positive, stays within ε of the orbit and converges to it.

[Formal statements](Registry/P064/Challenge.lean) · [Proof](Registry/P064/Solution.lean) · [Manuscript](papers/P064/paper.pdf) · [Metadata](entries/P064/formalization.yaml) · [Claim correspondence](entries/P064/CLAIM-EVIDENCE.md)

Lean and Mathlib are pinned by `lean-toolchain` and `lake-manifest.json`; the selected declarations and permitted axioms are in [the Comparator configuration](entries/P064/comparator.json).
