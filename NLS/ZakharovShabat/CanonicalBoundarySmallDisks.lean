import NLS.ZakharovShabat.CanonicalBoundaryUniformCutoff

/-! Arbitrarily small disks for the actual canonical boundary roots,
uniformly on a neighborhood in the full complex reflected source space. -/
noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The canonical roots approach their free frequencies uniformly on one
complex neighborhood. Both boundary conditions share the same cutoff. -/
theorem exists_uniform_small_canonicalBoundaryDisks (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : dirichletSubspace (p := p)) {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) :
    ∃ N : ℕ, ∃ U : Set (dirichletSubspace (p := p)),
      0 < N ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ b : BoundaryCondition, ∀ n : ℤ, N < n.natAbs →
        b.canonicalRoots hp hp1 ψ.val ψ.property n ∈ ball ((Real.pi : ℂ)*n) r := by
  obtain ⟨N₀,U₀,hN₀,hU₀,hc₀,hφ₀,h0₀,hl⟩ :=
    exists_uniform_canonical_boundaryRootLabeling hp hp1 φ
  obtain ⟨N₁,U₁,hN₁,hU₁,hc₁,hφ₁,h0₁,hbounds⟩ :=
    exists_uniform_height_and_strips hp φ.val hr hrπ
  let N := max N₀ N₁
  let T : dirichletSubspace (p := p) →L[ℂ] PairSpace p :=
    (dirichletSubspace (p := p)).subtypeL
  let U := U₀ ∩ T ⁻¹' U₁
  refine ⟨N,U,hN₀.trans_le (le_max_left _ _),hU₀.inter (hU₁.preimage T.continuous),
    hc₀.inter (hc₁.linear_preimage (T.toLinearMap.restrictScalars ℝ)),
    ⟨hφ₀,hφ₁⟩,⟨h0₀,h0₁⟩,?_⟩
  intro ψ hψ b n hn
  let z := b.canonicalRoots hp hp1 ψ.val ψ.property n
  have hd : z ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4) :=
    ((hl ψ hψ.1 b).distant_spec n ((le_max_left _ _).trans_lt hn)).1
  have hs := b.spectrum_subset_periodic hp ψ.val ψ.property
    (b.canonicalRoots_mem_spectrum hp hp1 ψ.val ψ.property n)
  have hext : spectralExterior N₁ r ⊆ resolventSet hp ψ.val := by
    intro a ha
    rcases spectralExterior_height_or_strip N₁ hrπ ha with him | ⟨k,hk,ha⟩
    · exact (hbounds ψ.val hψ.2).1 a him.le
    · exact (hbounds ψ.val hψ.2).2 k hk ha
  rcases periodicSpectrum_subset_box_union_disks hp ψ.val N₁ r hext hs with hz | hz
  · exact False.elim ((centralBox_disjoint_periodicDisk N₁ hN₁ n
      ((le_max_right _ _).trans_lt hn)).le_bot ⟨hz,hd⟩)
  · obtain ⟨k,hk⟩ := mem_iUnion.mp hz
    obtain ⟨hk,hz⟩ := mem_iUnion.mp hk
    have hd' : z ∈ ball ((Real.pi : ℂ)*k) (Real.pi/4) :=
      ball_subset_ball hrπ hz
    have hkn : k = n := by
      by_contra hne
      exact (periodicDisks_disjoint k n hne).le_bot ⟨hd',hd⟩
    simpa only [hkn] using hz

end NLS.ZakharovShabat
