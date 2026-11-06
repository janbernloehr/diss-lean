import NLS.KdV.HillDirichletGapTrigonometry
import NLS.KdV.HillAbelianCosineDifferential

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- Exact conversion of the cosine terminal tangent to the energy
terminal tangent, with the physical sheet sign. The multiplied identity
also holds at zero terminal sheet factor. -/
theorem hillDirichletCosineDifferential_mul_terminal_variation
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (hgap : hillRealGapHalfLength q hq hr k≠0)
    (e u v : ℂ)
    (hpoint : cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) e=
      (hillDirichletEnergy q hq hr k hk : ℂ))
    (hsin : Complex.sin e=hillDirichletGapSine q hq hr k hk)
    (hvar : v=-((hillRealGapHalfLength q hq hr k : ℂ)*Complex.sin e)*u) :
    hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr k hk)*
      (hillAbelianCosineDifferential q hq hr n hn k e*u)=
        hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr k hk)*v := by
  have hμfilled := hillRealGapContour_closedBall_subset_filledDomain q hq hr k hk (ball_subset_closedBall
    (hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk
      (ofReal_mem_ordered_segment _ _ _ (monotone_hillRealLabels q hq hr (by omega : 2*k-1≤2*k))
        (hillDirichletEnergy_mem_gap q hq hr k hk))))
  have hUne := hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk _ hμfilled
  have hdne : (hillRealGapHalfLength q hq hr k : ℂ)≠0 := ofReal_ne_zero.mpr hgap
  have hdsin : (hillRealGapHalfLength q hq hr k : ℂ)*Complex.sin e=
      I*hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr k hk)/
        hillDeflatedEnergyCanonicalRoot q hq hr k (hillDirichletEnergy q hq hr k hk) := by
    rw [hsin,hillDirichletGapSine]
    field_simp
  rw [hillAbelianCosineDifferential,hpoint,hvar,hdsin]
  ring

theorem hillDirichletCosineDifferential_regular_terminal_variation
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (hgap : hillRealGapHalfLength q hq hr k≠0)
    (e u v : ℂ)
    (hpoint : cosineGapPoint (hillRealGapCenter q hq hr k) (hillRealGapHalfLength q hq hr k) e=
      (hillDirichletEnergy q hq hr k hk : ℂ))
    (hsin : Complex.sin e=hillDirichletGapSine q hq hr k hk)
    (hvar : v=-((hillRealGapHalfLength q hq hr k : ℂ)*Complex.sin e)*u)
    (hreg : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr k hk)≠0) :
    hillAbelianCosineDifferential q hq hr n hn k e*u=
      (hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr k hk)/
        hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr k hk))*v := by
  have ht := hillDirichletCosineDifferential_mul_terminal_variation q hq hr n k hn hk hgap e u v hpoint hsin hvar
  apply mul_left_cancel₀ hreg
  rw [ht]
  field_simp

end NLS.KdV
