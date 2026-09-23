import NLS.ComplexAnalysis.RadialContourHomotopy
import NLS.ZakharovShabat.SourceStandardRootContourPath

/-!
# Standard-root integrals on polar contours

A smooth positive polar graph enclosing the indexed gap can be deformed
radially to a circle without crossing the gap. Its normalized inverse-root
integral is therefore `−1`. A cosine modulation supplies an explicit
noncircular example.
-/

noncomputable section
open Set Metric Complex
open scoped unitInterval ENNReal
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The normalized inverse standard-root integral on a smooth polar
contour enclosing the complete indexed gap. -/
theorem normalized_sourceStandardRoot_inv_radialPath
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c : ℂ) (R r₀ : ℝ) (hr₀ : 0 < r₀) (hrR : r₀ < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c r₀)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ 2 ρ)
    (hperiod : ρ (2*Real.pi) = ρ 0)
    (hρlo : ∀ θ ∈ Icc (0:ℝ) (2*Real.pi), r₀ < ρ θ) :
    (2*Real.pi*Complex.I)⁻¹ *
      (∫ᶜ z in NLS.ComplexAnalysis.radialPath c ρ hρ.continuous hperiod,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z) = -1 := by
  let φ := NLS.ComplexAnalysis.radialHomotopy c R ρ hρ.continuous hperiod
  have hφt : ∀ s ∈ Ioo (0:unitInterval) 1,
      ∀ u ∈ Ioo (0:unitInterval) 1,
      φ (s, u) ∈ (ball c r₀)ᶜ := by
    intro s _ u _ hball
    exact (NLS.ComplexAnalysis.radialHomotopy_disjoint_closedBall
      c R r₀ ρ hρ.continuous hperiod hr₀.le hrR hρlo s u)
        (ball_subset_closedBall hball)
  have havoid : closure ((ball c r₀)ᶜ) ⊆
      (sourcePeriodicSegment hp hp1 ψ n)ᶜ := by
    rw [(isOpen_ball.isClosed_compl).closure_eq]
    intro z hz hzin
    exact hz (hseg hzin)
  exact normalized_sourceStandardRoot_inv_curveIntegral_of_homotopy_circle
    hp hp1 ψ n c R (hr₀.trans hrR)
    (hseg.trans (ball_subset_ball hrR.le))
    φ (NLS.ComplexAnalysis.radialHomotopy_loop
      c R ρ hρ.continuous hperiod)
    hφt havoid
    (NLS.ComplexAnalysis.radialHomotopy_contDiffOn
      c R ρ hρ.continuous hperiod hρ)

/-- A genuinely noncircular cosine-modulated contour is a special case. -/
theorem normalized_sourceStandardRoot_inv_cosineRadialPath
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c : ℂ) (R r₀ ε : ℝ)
    (hr₀ : 0 < r₀) (hε : 0 < ε) (hsize : r₀+ε < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c r₀) :
    (2*Real.pi*Complex.I)⁻¹ *
      (∫ᶜ z in NLS.ComplexAnalysis.radialPath c
        (fun θ => R+ε*Real.cos θ)
        (by fun_prop)
        (by simp [Real.cos_two_pi]),
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z) = -1 := by
  apply normalized_sourceStandardRoot_inv_radialPath
    hp hp1 ψ n c R r₀ hr₀ (by linarith) hseg
    (fun θ => R+ε*Real.cos θ) (by fun_prop) (by simp [Real.cos_two_pi])
  intro θ _
  have hcos := Real.neg_one_le_cos θ
  have hbound : 0 ≤ ε*(1+Real.cos θ) := by
    apply mul_nonneg hε.le
    linarith
  nlinarith

end NLS.ZakharovShabat
