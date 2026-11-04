import NLS.KdV.HillAnalyticQuadraticDirichletValue
import NLS.KdV.HillPhysicalQuadraticTerminal

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillComplexQuadraticDirichletValue_eq_physical_of_data
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k≠n)
    (G H : ℂ × Coeff 2 → ℂ)
    (hH : AnalyticOnNhd ℂ (fun E => H (E,SpectralWeight.one.toCoeff q))
      (ball (hillRealGapCenter 0 h0q h0r k : ℂ)
        (3*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/4)))
    (heq : ∀ E ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ)
      (3*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/4),
      hillLocalGapPolynomial 0 h0q h0r k (SpectralWeight.one.toCoeff q) E*
        deriv (fun z => H (z,SpectralWeight.one.toCoeff q)) E+
      (E-hillLocalGapMidpoint 0 h0q h0r k (SpectralWeight.one.toCoeff q))*H (E,SpectralWeight.one.toCoeff q)=
        hillComplexRegularGapNumerator h0q h0r G k (E,SpectralWeight.one.toCoeff q))
    (hG : ∀ E : ℂ, G (E,SpectralWeight.one.toCoeff q)=hillAbelianSelectedGlobalPsi q hq hr n hn E)
    (hroot : ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
      hillFilledFreeGapRoot h0q h0r k (E,SpectralWeight.one.toCoeff q)=hillDeflatedEnergyCanonicalRoot q hq hr k E)
    (hM : hillLocalGapMidpoint 0 h0q h0r k (SpectralWeight.one.toCoeff q)=(hillRealGapCenter q hq hr k : ℂ))
    (hS : hillLocalGapSquare 0 h0q h0r k (SpectralWeight.one.toCoeff q)=(2*(hillRealGapHalfLength q hq hr k : ℂ))^2)
    (hmu : hillScaledDirichletRoot h0q h0r (1/16) k (SpectralWeight.one.toCoeff q)=(hillDirichletEnergy q hq hr k hk : ℂ))
    (hmuK : hillScaledDirichletRoot h0q h0r (1/16) k (SpectralWeight.one.toCoeff q) ∈
      closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
        (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k))
    (hτ : ‖(hillRealGapCenter q hq hr k : ℂ)-(hillRealGapCenter 0 h0q h0r k : ℂ)‖ ≤
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/16)
    (hδ : ‖(hillRealGapHalfLength q hq hr k : ℂ)‖ ≤
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/16) :
    hillComplexQuadraticDirichletValue h0q h0r H k (SpectralWeight.one.toCoeff q)=hillRegularAbelianCorrection q hq hr n hn k hk := by
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk).1
    (hillRealGapContour_geometry 0 h0q h0r k hk).2.1
  have hODE (E : ℂ) (hE : E ∈ ball c (3*R/4)) :
      ((E-(hillRealGapCenter q hq hr k : ℂ))^2-(hillRealGapHalfLength q hq hr k : ℂ)^2)*
        deriv (fun z => H (z,SpectralWeight.one.toCoeff q)) E+
      (E-(hillRealGapCenter q hq hr k : ℂ))*H (E,SpectralWeight.one.toCoeff q)=
        -I*hillAbelianSelectedGlobalPsi q hq hr n hn E/hillDeflatedEnergyCanonicalRoot q hq hr k E := by
    have hh := heq E hE
    have hEK : E ∈ closedBall c R := closedBall_subset_closedBall (by linarith : 3*R/4 ≤ R) (ball_subset_closedBall hE)
    rw [hillLocalGapPolynomial,hM,hS,hillComplexRegularGapNumerator,hG E,hroot E hEK] at hh
    have hδsq : (2*(hillRealGapHalfLength q hq hr k : ℂ))^2/4=(hillRealGapHalfLength q hq hr k : ℂ)^2 := by ring
    rwa [hδsq] at hh
  have hphysical := hillRegularAbelianCorrection_eq_quadratic_terminal q hq hr n k hn hk hkn c R hR
    (fun E => H (E,SpectralWeight.one.toCoeff q)) hH hτ hδ hODE
  have hmuK' : (hillDirichletEnergy q hq hr k hk : ℂ) ∈ closedBall c R := by simpa only [hmu] using hmuK
  rw [hillComplexQuadraticDirichletValue,hillComplexDirichletGapTerminal,hmu,hroot _ hmuK',hphysical]
  ring

end NLS.KdV
