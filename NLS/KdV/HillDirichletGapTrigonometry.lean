import NLS.KdV.HillDirichletSheetRoot
import NLS.KdV.HillDeflatedRadicandFactorization
import NLS.KdV.HillDeflatedCanonicalRootPhase
import NLS.KdV.HillFilledGapCutDomain

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillDirichletGapCosine (n : ℕ) (hn : 1 ≤ n) : ℂ :=
  ((hillDirichletEnergy q hq hr n hn : ℂ)-(hillRealGapCenter q hq hr n : ℂ))/
    (hillRealGapHalfLength q hq hr n : ℂ)

def hillDirichletGapSine (n : ℕ) (hn : 1 ≤ n) : ℂ :=
  I*hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr n hn)/
    ((hillRealGapHalfLength q hq hr n : ℂ)*hillDeflatedEnergyCanonicalRoot q hq hr n (hillDirichletEnergy q hq hr n hn))

theorem hillDirichletGapSine_sq_add_cosine_sq (n : ℕ) (hn : 1 ≤ n)
    (hgap : hillRealGapHalfLength q hq hr n ≠ 0) :
    hillDirichletGapSine q hq hr n hn^2+hillDirichletGapCosine q hq hr n hn^2 = 1 := by
  let μ : ℂ := hillDirichletEnergy q hq hr n hn
  let τ : ℂ := hillRealGapCenter q hq hr n
  let δ : ℂ := hillRealGapHalfLength q hq hr n
  let U := hillDeflatedEnergyCanonicalRoot q hq hr n μ
  let S := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) μ
  have hμ : μ ∈ hillGapFilledDomain q hq hr n :=
    hillRealGapContour_closedBall_subset_filledDomain q hq hr n hn (ball_subset_closedBall
      (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr n hn
        (ofReal_mem_ordered_segment _ _ _ (monotone_hillRealLabels q hq hr (by omega : 2*n-1 ≤ 2*n))
          (hillDirichletEnergy_mem_gap q hq hr n hn))))
  have hUne : U ≠ 0 := hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr n hn μ hμ
  have hδne : δ ≠ 0 := ofReal_ne_zero.mpr hgap
  have hsq : S^2 = ((μ-τ)^2-δ^2)*U^2 := by
    dsimp only [S]
    rw [hillDirichletSheetRoot_sq_of_characteristic_zero _ _ (hillDirichletEnergy_zero q hq hr n hn),
      hillL2Radicand_eq_gap_polynomial_mul_deflated_sq q hq hr n hn μ hμ]
    dsimp only [τ,δ,U]
    dsimp only [hillRealGapCenter,hillRealGapHalfLength]
    push_cast
    ring
  change (I*S/(δ*U))^2+((μ-τ)/δ)^2 = 1
  rw [div_pow,mul_pow,I_sq,neg_one_mul,hsq]
  field_simp [hδne,hUne]
  ring

end NLS.KdV
