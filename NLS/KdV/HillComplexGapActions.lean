import NLS.KdV.HillCommonComplexActionGapRatio
import NLS.KdV.HillCommonActionGapRatioPhysical
import NLS.KdV.HillActionGapRatioAllBase

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillComplexGapAction (n : ℕ) (p : Coeff 2) : ℂ :=
  hillComplexActionGapRatio h0q h0r n p*(hillLocalGapSquare 0 h0q h0r n p/4)

theorem exists_hillComplexGapAction_common_analytic (B : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ n : ℕ, N≤n →
      AnalyticOnNhd ℂ (hillComplexGapAction h0q h0r n) (ball (0 : Coeff 2) B) := by
  obtain ⟨Nr,hNr,hr⟩ := exists_hillComplexActionGapRatio_common_analytic h0q h0r B
  obtain ⟨Ns,hNs,hs⟩ := exists_hillFreeGap_bounded_complex_analytic_symmetric_data h0q h0r B
  refine ⟨Nr+Ns,hNr.trans (by omega),?_⟩
  intro n hn
  exact (hr n (by omega)).mul ((hs n (by omega)).2.1.div_const)

theorem exists_hillComplexGapAction_bounded_real_physical_matching (B : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ q : WeightedCoeff SpectralWeight.one.toWeight 2,
      ∀ hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0,
      ∀ hr : IsRealHillPotential (SpectralWeight.one.toCoeff q), ‖SpectralWeight.one.toCoeff q‖≤B →
        ∀ n : ℕ, N≤n → hillComplexGapAction h0q h0r n (SpectralWeight.one.toCoeff q)=
          (hillRealGapIntegral q hq hr n 0:ℂ) := by
  obtain ⟨Nr,hNr,hr⟩ := exists_hillComplexActionGapRatio_bounded_real_physical_matching h0q h0r B
  obtain ⟨Ns,hNs,hs⟩ := exists_hillFreeGap_bounded_real_symmetric_data_matching h0q h0r B
  refine ⟨Nr+Ns,hNr.trans (by omega),?_⟩
  intro q hq hreal hp n hn
  rw [hillComplexGapAction,hr q hq hreal hp n (by omega),(hs q hq hreal hp n (by omega)).2,
    hillRealGapIntegral_eq_halfLength_sq_mul_ratio q hq hreal n (hNr.trans (by omega))]
  ring

end NLS.KdV
