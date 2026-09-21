import NLS.ZakharovShabat.CanonicalBoundaryRoots
import NLS.ZakharovShabat.UniformBoundaryDisplacementBounds

/-! # Common cutoffs and bounds for canonical boundary roots
Sorting changes only finitely many roots in a uniformly bounded central box.
Uniqueness transfers complete local labelings to the canonical coordinates.
-/

noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both canonical sequences have complete labelings and bounded full lp displacements on one neighborhood. -/
theorem exists_uniform_canonicalBoundaryRoots (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : dirichletSubspace (p := p)) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (dirichletSubspace (p := p)),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∃ R : ℝ, 0 ≤ R ∧
        ∀ ψ ∈ U, ∀ b : BoundaryCondition,
          BoundaryRootLabeling b hp ψ.val ψ.property N (b.canonicalRoots hp hp1 ψ.val ψ.property) ∧
          ‖b.canonicalDisplacement hp hp1 ψ.val ψ.property‖ ≤ R := by
  obtain ⟨N,hN,U,hUo,hUc,hUφ,hU0,R,hR,hdata⟩ :=
    exists_uniform_bounded_boundaryRootLabeling hp hp1 φ
  obtain ⟨B,hB,hbox⟩ := (isBounded_centralSpectralBox N).exists_pos_norm_le
  refine ⟨N,hN,U,hUo,hUc,hUφ,hU0,(Finset.Icc (-(N : ℤ)) N).card*(B+Real.pi*N)+R,
    by positivity,?_⟩
  intro ψ hψ b
  obtain ⟨ξ,hξ,hd⟩ := hdata ψ hψ b
  obtain ⟨α,hα,hs⟩ := hξ.exists_ordered_relabeling
  have he := BoundaryRootLabeling.eq_canonicalRoots hp1 hα hs
  refine ⟨he ▸ hα,?_⟩
  have hb : ‖(⟨_,hα.displacement⟩ : Coeff p)‖ ≤
      (Finset.Icc (-(N : ℤ)) N).card*(B+Real.pi*N)+‖(⟨_,hξ.displacement⟩ : Coeff p)‖ := by
    apply Coeff.norm_le_of_eq_outside_finset _ _ (Finset.Icc (-(N : ℤ)) N) (B+Real.pi*N)
    · intro n hn
      have hnN : n.natAbs ≤ N := by simp only [Finset.mem_Icc] at hn; omega
      have hc : ‖(Real.pi : ℂ)*n‖ ≤ Real.pi*N := by
        rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_intCast]
        apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
        rw [← Int.cast_abs,← Int.natCast_natAbs]
        exact_mod_cast hnN
      exact (norm_sub_le _ _).trans (add_le_add (hbox _ (hα.central_mem n hnN)) hc)
    · intro n hn
      have hnN : N < n.natAbs := by simp only [Finset.mem_Icc] at hn; omega
      change spliceCentralRoots N α ξ n - (Real.pi : ℂ)*n = ξ n - (Real.pi : ℂ)*n
      simp only [spliceCentralRoots,if_pos hnN]
  have hdEq : (⟨_,hα.displacement⟩ : Coeff p) = b.canonicalDisplacement hp hp1 ψ.val ψ.property := by
    ext n
    exact congrArg (fun f : ℤ → ℂ => f n-(Real.pi : ℂ)*n) he
  rw [hdEq] at hb
  exact hb.trans (add_le_add le_rfl hd)

/-- One common neighborhood and threshold work for every larger admissible central block. -/
theorem exists_uniform_canonicalBoundaryRoots_all_cutoffs (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : dirichletSubspace (p := p)) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (dirichletSubspace (p := p)),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∃ R : ℝ, 0 ≤ R ∧
        ∀ ψ ∈ U, ∀ b : BoundaryCondition,
          (∀ K : ℕ, N ≤ K → BoundaryRootLabeling b hp ψ.val ψ.property K
            (b.canonicalRoots hp hp1 ψ.val ψ.property)) ∧
          ‖b.canonicalDisplacement hp hp1 ψ.val ψ.property‖ ≤ R := by
  obtain ⟨N,hN,U,hUo,hUc,hUφ,hU0,R,hR,hdata⟩ := exists_uniform_canonicalBoundaryRoots hp hp1 φ
  obtain ⟨M, V,_,hVo,hVc,hVφ,hV0,hcount,_⟩ := exists_uniform_analytic_boundaryEigenvalues hp φ
  refine ⟨max N M,hN.trans_le (le_max_left _ _),U ∩ V,hUo.inter hVo,hUc.inter hVc,
    ⟨hUφ,hVφ⟩,⟨hU0,hV0⟩,R,hR,?_⟩
  intro ψ hψ b
  have hd := hdata ψ hψ.1 b
  refine ⟨fun K hK => hd.1.enlarge K ((le_max_left _ _).trans hK)
    (hcount ψ hψ.2 K ((le_max_right _ _).trans hK)),hd.2⟩

end NLS.ZakharovShabat
