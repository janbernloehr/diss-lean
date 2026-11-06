import NLS.ZakharovShabat.SourceFullAbelianFourthContourPoisson
import NLS.ZakharovShabat.SourceFullAbelianPhysicalContourLocal

/-! # Local physical value of a fixed quartic contour

Annular Cauchy deformation removes the asymptotic radius restriction.
Continuity of finitely many gap endpoints makes the actual H₄−6H₁H₂
identity local on every prescribed finite open-gap support.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W U : Set (CoeffPair p)}

/-- The asymptotic radius in the physical fourth-contour formula may be
replaced by any positive radius enclosing every open gap. -/
theorem sourceFullAbelianFourthContour_eq_physical_of_enclosing
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (D : SourceAbelianSpectralChart hp hp1 W φ.val) (R : ℝ) (hR : 0 < R)
    (hgap : ∀ k : ℤ, canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) k ≠ 0 → sourcePeriodicSegment hp hp1 φ.val k ⊆ ball 0 R) :
    sourceFullAbelianFourthContour hp hp1 W 0 R φ.val =
      sourceFiniteGapNLSHamiltonian hp hp1 φ hf 4-
      6*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 2 := by
  obtain ⟨T,_,hphysical⟩ := exists_sourceFullAbelian_hamiltonian_fourth_contour_of_chart φ hf D
  let S := max R T
  have ha : AnalyticOnNhd ℂ (fun z => sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val)^4)
      (closedBall 0 S \ ball 0 R) := by
    intro z hz
    apply (sourceFullAbelianPrimitive_spectral_analytic D 0 z ?_).pow
    intro k hk hzk
    exact hz.2 (hgap k hk hzk)
  have he := circleIntegral_eq_of_differentiable_on_annulus_off_countable hR (le_max_left R T)
    countable_empty ha.continuousOn (by
      intro z hz
      exact (ha z ⟨ball_subset_closedBall hz.1.1,
        fun h => hz.1.2 (ball_subset_closedBall h)⟩).differentiableAt)
  rw [hphysical S (le_max_right R T)]
  exact congrArg (fun z : ℂ => (2*I/Real.pi:ℂ)*z) he.symm

namespace SourceFullAbelianDifferentialData

/-- One fixed contour gives the physical value on nearby real finite-gap
sources whose open gaps remain in a prescribed finite index set. -/
theorem eventually_fourthContour_eq_physical_of_gap_support
    (D : SourceFullAbelianDifferentialData hp hp1 W U)
    (φ : realTypeSourceSubmodule p) (S : Finset ℤ) (R : ℝ) (hR : 0 < R)
    (hseg : ∀ k ∈ S, sourcePeriodicSegment hp hp1 φ.val k ⊆ ball 0 R) :
    ∀ᶠ ψ : CoeffPair p in 𝓝 φ.val, ∀ hψ : IsRealType (CoeffPair.toMax p ψ),
      ∀ hf : (⟨ψ,hψ⟩ : realTypeSourceSubmodule p) ∈ sourceFiniteGapLocus hp hp1,
      (∀ k ∉ S, canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k = 0) →
      sourceFullAbelianFourthContour hp hp1 W 0 R ψ =
        sourceFiniteGapNLSHamiltonian hp hp1 ⟨ψ,hψ⟩ hf 4-
          6*sourceFiniteGapNLSHamiltonian hp hp1 ⟨ψ,hψ⟩ hf 1*sourceFiniteGapNLSHamiltonian hp hp1 ⟨ψ,hψ⟩ hf 2 := by
  filter_upwards [eventually_sourcePeriodicSegments_subset_ball hp hp1 φ S R hseg,
    D.source_open.mem_nhds (D.real_subset φ.property)] with ψ hsegments hψU
  intro hψ hf hsupport
  obtain ⟨E⟩ := D.charts ψ hψU
  apply sourceFullAbelianFourthContour_eq_physical_of_enclosing ⟨ψ,hψ⟩ hf E R hR
  intro k hk
  exact hsegments k (by_contra fun h => hk (hsupport k h))

end SourceFullAbelianDifferentialData
end NLS.ZakharovShabat
