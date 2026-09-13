import NLS.ZakharovShabat.PeriodicRootSequence
import NLS.ZakharovShabat.SpectralDisplacementTail
import NLS.ZakharovShabat.BoundaryEigenvalues

/-!
# Ordinary Dirichlet and Neumann displacement sequences

Each actual high-index boundary eigenvalue is a periodic eigenvalue in the
same refined disc. The corrected periodic two-root power sum therefore
controls either boundary branch. One neighborhood and cutoff work for both
boundary conditions, and finitely many omitted modes do not affect ℓp membership.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both ordinary boundary branches have locally uniform quantitative tails on reflected coefficient potentials. -/
theorem exists_uniform_boundaryDisplacementSummability (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : dirichletSubspace (p := p)) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (dirichletSubspace (p := p)),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∀ b : BoundaryCondition,
        Memℓp (fun n : ℤ => b.eigenvalue hp ψ.val n-(Real.pi : ℂ)*n) p ∧
        ∀ N : ℕ, N₀ ≤ N → Summable (spectralDisplacementPowerTail p N (b.eigenvalue hp ψ.val)) ∧
          (∑' n : ℤ, spectralDisplacementPowerTail p N (b.eigenvalue hp ψ.val) n) ≤
            rootDisplacementBudget SpectralWeight.one (unitBaseEquiv.symm ψ.val) N := by
  let F : dirichletSubspace (p := p) →L[ℂ] WeightedCoeffPair SpectralWeight.one.toWeight p :=
    unitBaseEquiv.symm.toContinuousLinearMap.comp (dirichletSubspace (p := p)).subtypeL
  have hF (ψ : dirichletSubspace (p := p)) : weightedBaseToPair SpectralWeight.one (F ψ) = ψ.val := by
    rw [← unitBaseEquiv_eq]
    exact unitBaseEquiv.apply_symm_apply ψ.val
  obtain ⟨N₁,U₁,_,ho₁,hc₁,hφ₁,h0₁,hboundary,_⟩ := exists_uniform_analytic_boundaryEigenvalues hp φ
  obtain ⟨N₂,hN₂,U₂,ho₂,hc₂,hφ₂,h0₂,hroots⟩ := exists_uniform_periodicRoots_with_power_sums hp hp1 SpectralWeight.one (F φ)
  refine ⟨max (N₁+1) N₂,hN₂.trans (le_max_right _ _),U₁ ∩ (F ⁻¹' U₂),
    ho₁.inter (ho₂.preimage F.continuous),hc₁.inter (hc₂.linear_preimage (F.restrictScalars ℝ).toLinearMap),
    ⟨hφ₁,hφ₂⟩,⟨h0₁,by simpa using h0₂⟩,?_⟩
  intro ψ hψ b
  obtain ⟨ξ,η,hpair,htail⟩ := hroots (F ψ) hψ.2
  have hs (N : ℕ) (hN : max (N₁+1) N₂ ≤ N) :
      Summable (spectralDisplacementPowerTail p N (b.eigenvalue hp ψ.val)) ∧
      (∑' n : ℤ, spectralDisplacementPowerTail p N (b.eigenvalue hp ψ.val) n) ≤
        rootDisplacementBudget SpectralWeight.one (F ψ) N := by
    have hb (n : ℤ) : spectralDisplacementPowerTail p N (b.eigenvalue hp ψ.val) n ≤
        rootDisplacementPowerTail p N ξ η n := by
      unfold spectralDisplacementPowerTail rootDisplacementPowerTail
      by_cases hn : N ≤ n.natAbs
      · simp only [if_pos hn]
        have he := (hboundary ψ hψ.1 N₁ le_rfl).eigenvalue_mem_spectrum b n (by omega)
        have hpz := BoundaryCondition.spectrum_subset_periodic b hp ψ.val ψ.property he.1
        have hspec := (hpair n (by omega)).spectrum_iff (b.eigenvalue hp ψ.val n)
          (refinedResonantDisk_subset_strip n he.2)
        rw [hF] at hspec
        rcases hspec.mp hpz with hx | hy
        · rw [hx]
          exact le_add_of_nonneg_right (by positivity)
        · rw [hy]
          exact le_add_of_nonneg_left (by positivity)
      · simp only [if_neg hn, le_refl]
    obtain ⟨ha,hb'⟩ := spectralDisplacementPowerTail_summable_and_le p N _ _ (htail N (by omega)).1 hb
    exact ⟨ha,hb'.trans (htail N (by omega)).2.1⟩
  have hP : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  exact ⟨memℓp_displacement_of_summable_tail hP _ _ (hs _ le_rfl).1,hs⟩

end NLS.ZakharovShabat
