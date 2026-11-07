import NLS.Articles.KdVPseudomeasures.SourceWideStripSpectralResults
import NLS.KdV.PseudomeasureWideInhomogeneousResults

/-! Remarks 2.6 and 2.8 on the entire printed strip, with the original
complex distribution data, the sign (L-lambda)f=g, full two-sided normal
form, unique complementary response and literal s+2,infinity regularity. -/
noncomputable section
open NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

def SourceInhomogeneousStatements (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) : Prop :=
  ∃ N : ℕ, 2≤N ∧
    ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖≤R →
    ∀ (n : ℕ) (hn : 2≤n), N≤n → ∀ (z : ℂ) (hz : z ∈ printedHillStrip n),
    ∀ (u : ℂ × ℂ) (g : FourierLebesgueSpace (2:ℝ) (-r) ⊤),
      EndpointComplementResult r hr.1 hr.2 n hn z hz (sourceEndpointCoefficients r q)
        (endpointHillModePotential r hr.1 hr.2 n (sourceEndpointCoefficients r q) u-
          sourceEndpointCoefficients r g) ∧
      EndpointInhomogeneousResult r hr.1 hr.2 n z
        (sourceEndpointCoefficients r q) (sourceEndpointCoefficients r g) u ∧
      EndpointInhomogeneousFullResult r hr.1 hr.2 n z
        (sourceEndpointCoefficients r q) (sourceEndpointCoefficients r g)

theorem sourceRemarks2_6_2_8 (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    SourceInhomogeneousStatements r hr R := by
  obtain ⟨N,hN,hcut⟩ := exists_wideEndpointHill_cutoff r hr.2 R
  refine ⟨N,hN,?_⟩
  intro q hq n hn hNn z hz u g
  have hC : 0 ≤ 13*endpointHillConstant r*(n:ℝ)^(r-1/2) :=
    mul_nonneg (mul_nonneg (by norm_num) (endpointHillConstant_pos r hr.2).le)
      (Real.rpow_nonneg (by positivity) _)
  have hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r q‖ ≤ 1/2 := by
    rw [norm_sourceEndpointCoefficients]
    exact (mul_le_mul_of_nonneg_left hq hC).trans (hcut n hNn)
  exact ⟨endpointComplementResult r hr.1 hr.2 n hn z hz (sourceEndpointCoefficients r q)
    (endpointHillModePotential r hr.1 hr.2 n (sourceEndpointCoefficients r q) u-sourceEndpointCoefficients r g) hs,
    endpointInhomogeneousResult r hr.1 hr.2 n hn z hz (sourceEndpointCoefficients r q) (sourceEndpointCoefficients r g) u hs,
    endpointInhomogeneousFullResult r hr.1 hr.2 n hn z hz (sourceEndpointCoefficients r q) (sourceEndpointCoefficients r g) hs⟩

end NLS.Articles.KdVPseudomeasures
