import NLS.ComplexAnalysis.AffineLoopHomotopy
import NLS.ZakharovShabat.SourceStandardRootContourHomotopyIndexed

/-!
# Indexed root integrals on loops close to a circle

A twice-smooth closed loop uniformly close to a gap-enclosing circle
has an affine homotopy that stays in the assigned isolating disc and
avoids the indexed gap. The loop need not be a polar graph.
-/

noncomputable section
open Set Metric Complex
open scoped unitInterval ENNReal
namespace NLS.ZakharovShabat

/-- A uniformly small smooth perturbation of an enclosing circle has
normalized inverse-root integrals equal to the negative Kronecker delta. -/
theorem normalized_sourceStandardRoot_inv_nearCircle_indexed
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (N : ℕ) (εiso : ℝ) (m n : ℤ)
    (c : ℂ) (R r₀ Rmax δ : ℝ)
    (hr₀ : 0 ≤ r₀) (hδ : 0 ≤ δ)
    (hinner : r₀+δ < R) (houter : R+δ ≤ Rmax)
    (hsegm : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c r₀)
    (hfilled : closedBall c Rmax ⊆ sourceIsolatingDisc hp hp1 φ N εiso m)
    (hcluster : sourceSpectralCluster hp hp1 ψ n ⊆
      sourceIsolatingDisc hp hp1 φ N εiso n)
    (hdisjoint : m ≠ n → Disjoint
      (sourceIsolatingDisc hp hp1 φ N εiso m)
      (sourceIsolatingDisc hp hp1 φ N εiso n))
    {a : ℂ} (γ : Path a a)
    (hγ : ContDiffOn ℝ 2 γ.extend (Icc 0 1))
    (hclose : ∀ u : I,
      dist (γ u) (NLS.ComplexAnalysis.circlePath c R u) ≤ δ) :
    (2*Real.pi*Complex.I)⁻¹ *
      (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z) =
      if m = n then -1 else 0 := by
  let H := ContinuousMap.Homotopy.affine
    (NLS.ComplexAnalysis.circlePath c R : C(I, ℂ)) (γ : C(I, ℂ))
  have hRpos : 0 < R := by linarith
  have hRmax : R ≤ Rmax := by linarith
  have hannulus (s u : I) :
      r₀ < dist (H (s,u)) c ∧ dist (H (s,u)) c ≤ Rmax :=
    NLS.ComplexAnalysis.affineCircleHomotopy_annulus
      c R r₀ Rmax δ hr₀ hδ hinner houter γ hclose s u
  have hinside : range H ⊆ sourceIsolatingDisc hp hp1 φ N εiso m := by
    rintro z ⟨⟨s,u⟩, rfl⟩
    exact hfilled (mem_closedBall.mpr (hannulus s u).2)
  have havoid : range H ⊆ (sourcePeriodicSegment hp hp1 ψ m)ᶜ := by
    rintro z ⟨⟨s,u⟩, rfl⟩ hseg
    have hmem := hsegm hseg
    exact (not_lt_of_ge (hannulus s u).1.le) (mem_ball.mp hmem)
  exact normalized_sourceStandardRoot_inv_curveIntegral_indexed_of_homotopy_circle
    hp hp1 φ ψ N εiso m n c R hRpos
    (hsegm.trans (ball_subset_ball (by linarith)))
    ((closedBall_subset_closedBall hRmax).trans hfilled)
    hcluster hdisjoint H
    (NLS.ComplexAnalysis.affineHomotopy_loop (γ₁ := NLS.ComplexAnalysis.circlePath c R)
      (γ₂ := γ)) hinside havoid
    (NLS.ComplexAnalysis.affineHomotopy_contDiffOn
      (NLS.ComplexAnalysis.circlePath_contDiffOn c R) hγ)

end NLS.ZakharovShabat
