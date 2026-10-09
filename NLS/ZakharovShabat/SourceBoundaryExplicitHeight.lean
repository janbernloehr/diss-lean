import NLS.ZakharovShabat.SourceBoundaryPrintedHeight

/-! # A proposed all-p correction to the boundary height

The source height (1+8*p*E_p*norm)^p is sufficient for both ordinary
boundary conditions for every finite p>1. Here E_p is the proved interval
extension bound, retained explicitly. This is a separate corrected
statement, not the printed height of Theorem 1.4, which has a counterexample.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original source norm controls the reflected potential by the proved extension bound. -/
theorem norm_periodOneBoundaryPotential_le (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ‖(periodOneBoundaryPotential hp hp1 φ).val‖ ≤
      BoundaryCondition.intervalExtensionBound hp1 hp * ‖φ‖ := by
  change ‖BoundaryCondition.intervalExtensionCLM .dirichlet hp1 hp (CoeffPair.toMax p φ)‖ ≤ _
  exact (BoundaryCondition.norm_intervalExtensionCLM_apply_le .dirichlet hp1 hp _).trans
    (mul_le_mul_of_nonneg_left (CoeffPair.norm_toMax_le φ)
      (BoundaryCondition.intervalExtensionBound_pos hp1 hp).le)

/-- A sufficient norm coefficient for the proposed all-p correction. -/
def sourceBoundaryHeightCoefficient (hp : p ≠ ⊤) (hp1 : 1 < p) : ℝ :=
  8*p.toReal*BoundaryCondition.intervalExtensionBound hp1 hp

theorem sourceBoundaryHeightCoefficient_pos (hp : p ≠ ⊤) (hp1 : 1 < p) :
    0 < sourceBoundaryHeightCoefficient hp hp1 := by
  have hp0 := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have hE := BoundaryCondition.intervalExtensionBound_pos hp1 hp
  unfold sourceBoundaryHeightCoefficient
  positivity

/-- The norm-ball height proposed in place of the false printed all-p formula. -/
def sourceBoundaryExplicitHeight (hp : p ≠ ⊤) (hp1 : 1 < p) (M : ℝ) : ℝ :=
  (1+sourceBoundaryHeightCoefficient hp hp1*M)^p.toReal

theorem sourceBoundaryExplicitHeight_pos (hp : p ≠ ⊤) (hp1 : 1 < p)
    {M : ℝ} (hM : 0 ≤ M) : 0 < sourceBoundaryExplicitHeight hp hp1 M := by
  have hC := sourceBoundaryHeightCoefficient_pos hp hp1
  unfold sourceBoundaryExplicitHeight
  positivity

theorem sourceBoundaryExplicitHeight_mono (hp : p ≠ ⊤) (hp1 : 1 < p)
    {M R : ℝ} (hM : 0 ≤ M) (hMR : M ≤ R) :
    sourceBoundaryExplicitHeight hp hp1 M ≤ sourceBoundaryExplicitHeight hp hp1 R := by
  have hC := sourceBoundaryHeightCoefficient_pos hp hp1
  unfold sourceBoundaryExplicitHeight
  gcongr

/-- On and above the proposed height, the actual reflected periodic resolvent exists. -/
theorem mem_resolventSet_of_sourceBoundaryExplicitHeight (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) {M : ℝ} (hφ : ‖φ‖ ≤ M) {z : ℂ}
    (hz : sourceBoundaryExplicitHeight hp hp1 M ≤ |z.im|) :
    z ∈ resolventSet hp (periodOneBoundaryPotential hp hp1 φ).val := by
  apply mem_resolventSet_of_explicit_height hp _
    ((norm_periodOneBoundaryPotential_le hp hp1 φ).trans
      (mul_le_mul_of_nonneg_left hφ (BoundaryCondition.intervalExtensionBound_pos hp1 hp).le))
  simpa only [sourceBoundaryExplicitHeight,sourceBoundaryHeightCoefficient,mul_assoc] using hz

/-- The same closed exterior strip is in both actual boundary resolvent sets. -/
theorem mem_boundaryResolventSet_of_sourceBoundaryExplicitHeight (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) {M : ℝ} (hφ : ‖φ‖ ≤ M) {z : ℂ}
    (hz : sourceBoundaryExplicitHeight hp hp1 M ≤ |z.im|) :
    z ∈ b.resolventSet hp (periodOneBoundaryPotential hp hp1 φ).val
      (periodOneBoundaryPotential hp hp1 φ).property :=
  b.mem_resolventSet_of_periodic hp _ _ z
    (mem_resolventSet_of_sourceBoundaryExplicitHeight hp hp1 φ hφ hz)

/-- Both ordinary source spectra lie strictly below the proposed norm-ball height. -/
theorem sourceBoundarySpectrum_abs_im_lt_explicit_height (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) {M : ℝ} (hφ : ‖φ‖ ≤ M) {z : ℂ}
    (hz : z ∈ b.spectrum hp (periodOneBoundaryPotential hp hp1 φ).val
      (periodOneBoundaryPotential hp hp1 φ).property) :
    |z.im| < sourceBoundaryExplicitHeight hp hp1 M := by
  by_contra h
  exact hz (mem_boundaryResolventSet_of_sourceBoundaryExplicitHeight hp hp1 b φ hφ (le_of_not_gt h))

/-- The proposed correction supplies both exact central counts and exhaustion on one
open convex source neighborhood, for every larger cutoff, for all finite p>1.
The counting data retains one simple root in each high disk, with original multiplicities. -/
theorem sourceTheorem1_4_proposed_height (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        BoundaryCountingData hp (periodOneBoundaryPotential hp hp1 ψ).val
          (periodOneBoundaryPotential hp hp1 ψ).property N ∧
        ∀ b : BoundaryCondition,
          b.heightSpectrum hp (periodOneBoundaryPotential hp hp1 ψ).val
            (periodOneBoundaryPotential hp hp1 ψ).property N (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖) =
            b.centralSpectrum hp (periodOneBoundaryPotential hp hp1 ψ).val
              (periodOneBoundaryPotential hp hp1 ψ).property N ∧
          (∑ z ∈ b.heightSpectrum hp (periodOneBoundaryPotential hp hp1 ψ).val
            (periodOneBoundaryPotential hp hp1 ψ).property N (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖),
            b.algebraicMultiplicity hp (periodOneBoundaryPotential hp hp1 ψ).val
              (periodOneBoundaryPotential hp hp1 ψ).property z) = 2*N+1 ∧
          b.spectrum hp (periodOneBoundaryPotential hp hp1 ψ).val
            (periodOneBoundaryPotential hp hp1 ψ).property ⊆
            heightSpectralBox N (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖) ∪
              highSpectralDisks N (Real.pi/4) :=
  exists_source_boundaryCounting_height_of_bound hp hp1
    (sourceBoundaryHeightCoefficient_pos hp hp1).le
    (fun ψ b _z hz => (sourceBoundarySpectrum_abs_im_lt_explicit_height hp hp1 b ψ le_rfl hz).le) φ

end NLS.ZakharovShabat
