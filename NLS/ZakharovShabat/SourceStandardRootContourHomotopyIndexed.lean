import NLS.ZakharovShabat.SourceStandardRootContourPath
import NLS.ZakharovShabat.SourceStandardRootContourBasic

/-!
# Indexed inverse-root integrals on smoothly deformable contours

A smooth loop joined to an enclosing circle inside an isolating disc has
the expected diagonal and off-diagonal inverse-root integrals. The
homotopy need not be radial or the target loop star-shaped.
-/

noncomputable section
open Set Metric Complex
open scoped unitInterval ENNReal
namespace NLS.ZakharovShabat

/-- The inverse root for a different gap integrates to zero on a loop
smoothly deformable from a circle inside the assigned isolating disc. -/
theorem sourceStandardRoot_inv_curveIntegral_of_homotopy_circle_off_index_eq_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (N : ℕ) (ε : ℝ) (m n : ℤ)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hfilled : closedBall c r ⊆ sourceIsolatingDisc hp hp1 φ N ε m)
    (hcluster : sourceSpectralCluster hp hp1 ψ n ⊆
      sourceIsolatingDisc hp hp1 φ N ε n)
    (hdisjoint : Disjoint
      (sourceIsolatingDisc hp hp1 φ N ε m)
      (sourceIsolatingDisc hp hp1 φ N ε n))
    {a : ℂ} {γ : Path a a}
    (H : (NLS.ComplexAnalysis.circlePath c r : C(I, ℂ)).Homotopy γ)
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
    (hinside : range H ⊆ sourceIsolatingDisc hp hp1 φ N ε m)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (H.extend xy.1) xy.2) (Icc 0 1)) :
    (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z) = 0 := by
  have hseg : sourcePeriodicSegment hp hp1 ψ n ⊆
      sourceIsolatingDisc hp hp1 φ N ε n :=
    sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ ψ N ε n hcluster
  have havoid : range H ⊆ (sourcePeriodicSegment hp hp1 ψ n)ᶜ := by
    intro z hz hzin
    exact (Set.disjoint_left.mp hdisjoint (hinside hz)) (hseg hzin)
  let f : ℂ → ℂ := fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹
  calc
    (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm f z) =
      ∫ᶜ z in NLS.ComplexAnalysis.circlePath c r,
        NLS.ComplexAnalysis.holomorphicOneForm f z :=
      (sourceStandardRoot_inv_curveIntegral_eq_of_homotopy_range
        hp hp1 ψ n H hloop havoid hcontdiff).symm
    _ = ∮ z in C(c,r), f z :=
      NLS.ComplexAnalysis.curveIntegral_circlePath f c r
    _ = 0 :=
      circleIntegral_sourceStandardRoot_inv_off_index_eq_zero
        hp hp1 φ ψ N ε m n c r hr hcluster hdisjoint hfilled

/-- The normalized inverse-root integrals on any smooth loop with a
gap-avoiding homotopy from an enclosing circle confined to the assigned
isolating disc form the negative Kronecker delta. -/
theorem normalized_sourceStandardRoot_inv_curveIntegral_indexed_of_homotopy_circle
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (N : ℕ) (ε : ℝ) (m n : ℤ)
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hsegm : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c r)
    (hfilled : closedBall c r ⊆ sourceIsolatingDisc hp hp1 φ N ε m)
    (hcluster : sourceSpectralCluster hp hp1 ψ n ⊆
      sourceIsolatingDisc hp hp1 φ N ε n)
    (hdisjoint : m ≠ n → Disjoint
      (sourceIsolatingDisc hp hp1 φ N ε m)
      (sourceIsolatingDisc hp hp1 φ N ε n))
    {a : ℂ} {γ : Path a a}
    (H : (NLS.ComplexAnalysis.circlePath c r : C(I, ℂ)).Homotopy γ)
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
    (hinside : range H ⊆ sourceIsolatingDisc hp hp1 φ N ε m)
    (havoidm : range H ⊆ (sourcePeriodicSegment hp hp1 ψ m)ᶜ)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (H.extend xy.1) xy.2) (Icc 0 1)) :
    (2*Real.pi*Complex.I)⁻¹ *
      (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z) =
      if m = n then -1 else 0 := by
  by_cases hmn : m = n
  · subst n
    simpa using normalized_sourceStandardRoot_inv_curveIntegral_of_homotopy_circle_range
      hp hp1 ψ m c r hr hsegm H hloop havoidm hcontdiff
  · have hzero := sourceStandardRoot_inv_curveIntegral_of_homotopy_circle_off_index_eq_zero
      hp hp1 φ ψ N ε m n c r hr.le hfilled hcluster (hdisjoint hmn)
      H hloop hinside hcontdiff
    rw [hzero]
    simp [hmn]

end NLS.ZakharovShabat
