import NLS.ComplexAnalysis.ConvexHolomorphicLoopIntegral
import NLS.ZakharovShabat.SourceStandardRootContourBasic
import NLS.ZakharovShabat.SourceIsolatingContourGeometry
import NLS.ZakharovShabat.SourceStandardRootContourPath

/-!
# Off-diagonal root integrals on arbitrary smooth loops in isolating discs

An assigned isolating disc is convex and disjoint from every other indexed
gap. The inverse root for another index is holomorphic throughout it, so
its curve integral vanishes on every twice-smooth closed loop in the disc.
The diagonal homotopy condition alone then gives the full indexed identity.
-/

noncomputable section
open Set Metric Complex
open scoped unitInterval ENNReal
namespace NLS.ZakharovShabat

/-- The off-diagonal inverse-root curve integral vanishes for every
twice-smooth closed loop contained in the assigned isolating disc. -/
theorem sourceStandardRoot_inv_curveIntegral_off_index_eq_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (N : ℕ) (ε : ℝ) (m n : ℤ)
    (hcluster : sourceSpectralCluster hp hp1 ψ n ⊆
      sourceIsolatingDisc hp hp1 φ N ε n)
    (hdisjoint : Disjoint
      (sourceIsolatingDisc hp hp1 φ N ε m)
      (sourceIsolatingDisc hp hp1 φ N ε n))
    {a : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 2 γ.extend (Icc 0 1))
    (hγinside : ∀ u : I, γ u ∈ sourceIsolatingDisc hp hp1 φ N ε m) :
    (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
      (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z) = 0 := by
  have hseg : sourcePeriodicSegment hp hp1 ψ n ⊆
      sourceIsolatingDisc hp hp1 φ N ε n :=
    sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ ψ N ε n hcluster
  have hconv : Convex ℝ (sourceIsolatingDisc hp hp1 φ N ε m) := by
    rw [sourceIsolatingDisc_eq_ball]
    exact convex_ball _ _
  apply NLS.ComplexAnalysis.curveIntegral_eq_zero_of_convex
    (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹)
    (sourceIsolatingDisc hp hp1 φ N ε m) hconv
  · intro z hz
    have hnot : z ∉ sourcePeriodicSegment hp hp1 ψ n := by
      intro hzin
      exact (Set.disjoint_left.mp hdisjoint hz) (hseg hzin)
    exact (sourceStandardRoot_inv_analyticAt hp hp1 ψ n z hnot).differentiableAt
  · exact hγ
  · exact hγinside

/-- The indexed inverse-root identity for a smooth loop inside its
assigned isolating disc. Only the diagonal case needs a gap-avoiding
homotopy from an enclosing circle. -/
theorem normalized_sourceStandardRoot_inv_curveIntegral_indexed_of_gap_homotopy
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (N : ℕ) (ε : ℝ) (m n : ℤ)
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hsegm : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c r)
    (hcluster : sourceSpectralCluster hp hp1 ψ n ⊆
      sourceIsolatingDisc hp hp1 φ N ε n)
    (hdisjoint : m ≠ n → Disjoint
      (sourceIsolatingDisc hp hp1 φ N ε m)
      (sourceIsolatingDisc hp hp1 φ N ε n))
    {a : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 2 γ.extend (Icc 0 1))
    (hγinside : ∀ u : I, γ u ∈ sourceIsolatingDisc hp hp1 φ N ε m)
    (H : (NLS.ComplexAnalysis.circlePath c r : C(I, ℂ)).Homotopy γ)
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
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
  · have hzero := sourceStandardRoot_inv_curveIntegral_off_index_eq_zero
      hp hp1 φ ψ N ε m n hcluster (hdisjoint hmn) γ hγ hγinside
    rw [hzero]
    simp [hmn]

end NLS.ZakharovShabat
