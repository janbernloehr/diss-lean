import NLS.ZakharovShabat.SourceStandardRootContourRadial

noncomputable section
open Set Metric Complex
open scoped unitInterval ENNReal
namespace NLS.ZakharovShabat

/-- The reciprocal root associated with a different isolated gap has
zero integral on a polar contour confined to this index's isolating disc. -/
theorem sourceStandardRoot_inv_radialPath_off_index_eq_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (N : ℕ) (ε : ℝ) (m n : ℤ)
    (c : ℂ) (R Rmax : ℝ) (hR0 : 0 ≤ R) (hRmax : R ≤ Rmax)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ 2 ρ)
    (hperiod : ρ (2*Real.pi) = ρ 0)
    (hρbounds : ∀ θ ∈ Icc (0:ℝ) (2*Real.pi),
      0 ≤ ρ θ ∧ ρ θ ≤ Rmax)
    (hcluster : sourceSpectralCluster hp hp1 ψ n ⊆
      sourceIsolatingDisc hp hp1 φ N ε n)
    (hdisjoint : Disjoint (sourceIsolatingDisc hp hp1 φ N ε m)
      (sourceIsolatingDisc hp hp1 φ N ε n))
    (hfilled : closedBall c Rmax ⊆ sourceIsolatingDisc hp hp1 φ N ε m) :
    (∫ᶜ z in NLS.ComplexAnalysis.radialPath c ρ hρ.continuous hperiod,
      NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z) = 0 := by
  let H := NLS.ComplexAnalysis.radialHomotopy c R ρ hρ.continuous hperiod
  have hseg : sourcePeriodicSegment hp hp1 ψ n ⊆
      sourceIsolatingDisc hp hp1 φ N ε n :=
    sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ ψ N ε n hcluster
  have havoid : closure (closedBall c Rmax) ⊆
      (sourcePeriodicSegment hp hp1 ψ n)ᶜ := by
    rw [closure_closedBall]
    intro z hz hzin
    exact (Set.disjoint_left.mp hdisjoint (hfilled hz)) (hseg hzin)
  have hφt : ∀ s ∈ Ioo (0:unitInterval) 1,
      ∀ u ∈ Ioo (0:unitInterval) 1,
      H (s,u) ∈ closedBall c Rmax := by
    intro s _ u _
    exact NLS.ComplexAnalysis.radialHomotopy_mem_closedBall
      c R Rmax ρ hρ.continuous hperiod hR0 hRmax hρbounds s u
  let f : ℂ → ℂ := fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹
  calc
    (∫ᶜ z in NLS.ComplexAnalysis.radialPath c ρ hρ.continuous hperiod,
        NLS.ComplexAnalysis.holomorphicOneForm f z) =
      ∫ᶜ z in NLS.ComplexAnalysis.circlePath c R,
        NLS.ComplexAnalysis.holomorphicOneForm f z :=
      (sourceStandardRoot_inv_curveIntegral_eq_of_homotopy
        hp hp1 ψ n H
        (NLS.ComplexAnalysis.radialHomotopy_loop
          c R ρ hρ.continuous hperiod)
        hφt havoid
        (NLS.ComplexAnalysis.radialHomotopy_contDiffOn
          c R ρ hρ.continuous hperiod hρ)).symm
    _ = ∮ z in C(c,R), f z :=
      NLS.ComplexAnalysis.curveIntegral_circlePath f c R
    _ = 0 :=
      circleIntegral_sourceStandardRoot_inv_off_index_eq_zero
        hp hp1 φ ψ N ε m n c R hR0 hcluster hdisjoint
        ((closedBall_subset_closedBall hRmax).trans hfilled)

/-- The inverse-root integrals on a smooth polar contour form the negative
Kronecker delta, provided the filled contour lies in the indexed isolating
disc and the contour surrounds that index's complete periodic segment. -/
theorem normalized_sourceStandardRoot_inv_radialPath_indexed
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (N : ℕ) (ε : ℝ) (m n : ℤ)
    (c : ℂ) (R r₀ Rmax : ℝ)
    (hr₀ : 0 < r₀) (hrR : r₀ < R) (hRmax : R ≤ Rmax)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c r₀)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ 2 ρ)
    (hperiod : ρ (2*Real.pi) = ρ 0)
    (hρlo : ∀ θ ∈ Icc (0:ℝ) (2*Real.pi), r₀ < ρ θ)
    (hρmax : ∀ θ ∈ Icc (0:ℝ) (2*Real.pi), ρ θ ≤ Rmax)
    (hcluster : sourceSpectralCluster hp hp1 ψ n ⊆
      sourceIsolatingDisc hp hp1 φ N ε n)
    (hdisjoint : m ≠ n → Disjoint
      (sourceIsolatingDisc hp hp1 φ N ε m)
      (sourceIsolatingDisc hp hp1 φ N ε n))
    (hfilled : closedBall c Rmax ⊆ sourceIsolatingDisc hp hp1 φ N ε m) :
    (2*Real.pi*Complex.I)⁻¹ *
      (∫ᶜ z in NLS.ComplexAnalysis.radialPath c ρ hρ.continuous hperiod,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z) =
      if m = n then -1 else 0 := by
  by_cases hmn : m = n
  · subst n
    simpa using normalized_sourceStandardRoot_inv_radialPath
      hp hp1 ψ m c R r₀ hr₀ hrR hseg ρ hρ hperiod hρlo
  · have hρbounds : ∀ θ ∈ Icc (0:ℝ) (2*Real.pi),
        0 ≤ ρ θ ∧ ρ θ ≤ Rmax := by
      intro θ hθ
      exact ⟨le_trans hr₀.le (hρlo θ hθ).le, hρmax θ hθ⟩
    have hzero := sourceStandardRoot_inv_radialPath_off_index_eq_zero
      hp hp1 φ ψ N ε m n c R Rmax (hr₀.trans hrR).le hRmax
      ρ hρ hperiod hρbounds hcluster (hdisjoint hmn) hfilled
    rw [hzero]
    simp [hmn]

end NLS.ZakharovShabat
