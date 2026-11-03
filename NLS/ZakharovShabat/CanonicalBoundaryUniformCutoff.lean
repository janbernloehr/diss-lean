import NLS.ZakharovShabat.CanonicalBoundaryRoots

/-! Uniform canonical boundary cutoffs on the FULL complex source space.
Sorting a complete actual central block identifies the canonical sequence
at that SAME cutoff, eliminating its pointwise choice of cutoff. -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- ANY complete actual boundary labeling supplies the canonical sequence
at its OWN cutoff, without comparing the canonical choice of cutoff. -/
theorem BoundaryRootLabeling.canonical_at_cutoff
    {b : BoundaryCondition} {hp : p ≠ ⊤} (hp1 : 1 < p)
    {φ : PairSpace p} {hφ : φ ∈ dirichletSubspace} {N : ℕ} {xi : ℤ → ℂ}
    (h : BoundaryRootLabeling b hp φ hφ N xi) :
    BoundaryRootLabeling b hp φ hφ N (b.canonicalRoots hp hp1 φ hφ) := by
  obtain ⟨alpha,ha,ho⟩ := h.exists_ordered_relabeling
  have he := ha.eq_canonicalRoots hp1 ho
  rw [he] at ha
  exact ha

/-- ONE cutoff works for BOTH canonical boundary sequences on a common
complex source neighborhood; the canonical sequence need not choose this cutoff. -/
theorem exists_uniform_canonical_boundaryRootLabeling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : dirichletSubspace (p := p)) :
    ∃ N : ℕ, ∃ U : Set (dirichletSubspace (p := p)),
      0 < N ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ b : BoundaryCondition,
        BoundaryRootLabeling b hp ψ.val ψ.property N (b.canonicalRoots hp hp1 ψ.val ψ.property) := by
  obtain ⟨N,hN,U,hU,hconv,hφ,h0,hlabel⟩ := exists_uniform_boundaryRootLabeling hp hp1 φ
  refine ⟨N,U,hN,hU,hconv,hφ,h0,fun ψ hψ b => ?_⟩
  obtain ⟨xi,hxi⟩ := hlabel ψ hψ b
  exact hxi.canonical_at_cutoff hp1

/-- Full complex neighborhoods have one canonical cutoff AND analyticity
of EVERY high canonical coordinate, with that cutoff fixed BEFORE the source. -/
theorem exists_uniform_analytic_canonical_boundaryRoots (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : dirichletSubspace (p := p)) :
    ∃ N : ℕ, ∃ U : Set (dirichletSubspace (p := p)),
      0 < N ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ ψ ∈ U, ∀ b : BoundaryCondition,
        BoundaryRootLabeling b hp ψ.val ψ.property N (b.canonicalRoots hp hp1 ψ.val ψ.property)) ∧
      ∀ b : BoundaryCondition, ∀ n : ℤ, N < n.natAbs →
        AnalyticOnNhd ℂ (fun ψ : dirichletSubspace (p := p) =>
          b.canonicalRoots hp hp1 ψ.val ψ.property n) U := by
  obtain ⟨N₀,U₀,hN₀,hU₀,hc₀,hφ₀,h0₀,hl⟩ := exists_uniform_canonical_boundaryRootLabeling hp hp1 φ
  obtain ⟨N₁,U₁,_,hU₁,hc₁,hφ₁,h0₁,hcount,han⟩ := exists_uniform_analytic_boundaryEigenvalues hp φ
  let N := max N₀ N₁
  let U := U₀ ∩ U₁
  have hU : IsOpen U := hU₀.inter hU₁
  have hlabel (ψ : dirichletSubspace (p := p)) (hψ : ψ ∈ U) (b : BoundaryCondition) :
      BoundaryRootLabeling b hp ψ.val ψ.property N (b.canonicalRoots hp hp1 ψ.val ψ.property) :=
    (hl ψ hψ.1 b).enlarge N (le_max_left _ _) (hcount ψ hψ.2 N (le_max_right _ _))
  refine ⟨N,U,lt_of_lt_of_le hN₀ (le_max_left _ _),hU,hc₀.inter hc₁,
    ⟨hφ₀,hφ₁⟩,⟨h0₀,h0₁⟩,hlabel,?_⟩
  intro b n hn ψ hψ
  have hn₁ : N₁ < n.natAbs := lt_of_le_of_lt (le_max_right _ _) hn
  have ha := (han b n hn₁).1 ψ hψ.2
  apply ha.congr
  filter_upwards [hU.mem_nhds hψ] with χ hχ
  exact ((hlabel χ hχ b).distant n hn).symm

end NLS.ZakharovShabat
