import NLS.Articles.KdVPseudomeasures.SourceLemma29Counterexample
import NLS.Articles.KdVPseudomeasures.SourceTwoModeOriginalPotential
import NLS.Articles.KdVPseudomeasures.SourceWeightedDiagonalTransport

/-! Failure of the literal Lemma 2.9(i) bound on the actual original
real, mean-zero, period-one potentials in a fixed weighted norm ball.
There is a violating potential beyond every proposed uniform cutoff. -/
noncomputable section
open scoped ENNReal
open NLS.KdV NLS.WeightedCoeff NLS.Fourier NLS.Fourier.SmoothPeriodicTest
namespace NLS.Articles.KdVPseudomeasures

theorem sourceLemma2_9_i_original_counterexample (N : ℕ) :
    let w := SpectralWeight.sobolev (1/4) (by norm_num)
    ∃ (n : ℕ) (_ : N ≤ n) (hn2 : 2 ≤ n)
      (Q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev (1/4)) ⊤)
      (hz : (freeHillValue n:ℂ) ∈ wideHillStrip n),
      Q.val.IsRealMeanZeroPeriodOne ∧ ‖Q‖=1 ∧
      13*endpointHillConstant (1/4)*(n:ℝ)^((1/4:ℝ)-1/2)*‖Q‖ ≤ 1/2 ∧
      2*wideEndpointShiftedOperatorNorm w (1/4) (by norm_num) (by norm_num)
        n hn2 (freeHillValue n:ℂ) hz (sourceWeightedEndpointCoefficients w (1/4) Q) (-(n:ℤ))*
          ‖sourceForgetWeight w (1/4) Q‖ <
        ‖(sourceEndpointEntries (1/4) ⟨by norm_num,by norm_num⟩ n
          (sourceForgetWeight w (1/4) Q,(freeHillValue n:ℂ))).1‖ := by
  let w := SpectralWeight.sobolev (1/4) (by norm_num)
  let n := max N (4096^4)
  let q := twoSymmetricInfinityModes (w.negativeSobolev (1/4)) (2*(n:ℤ)-2)
  let Q := sourceTwoModeOriginalPotential w (1/4) (2*(n:ℤ)-2)
  obtain ⟨hn2,hz,hq,_,hs,hfail⟩ := sourceLemma2_9_i_counterexample_at n (le_max_right _ _)
  have hcoeff : sourceWeightedEndpointCoefficients w (1/4) Q=q :=
    sourceTwoModeOriginalPotential_coefficients w (1/4) (2*(n:ℤ)-2)
  have hnorm : ‖Q‖=‖q‖ := (norm_sourceWeightedEndpointCoefficients w (1/4) Q).symm.trans
    (congrArg norm hcoeff)
  have hforget : ‖sourceForgetWeight w (1/4) Q‖ = ‖endpointForgetWeight w (1/4) q‖ := by
    rw [← norm_sourceEndpointCoefficients (1/4) (sourceForgetWeight w (1/4) Q),
      sourceEndpointCoefficients_forgetWeight,hcoeff]
  refine ⟨n,le_max_left _ _,hn2,Q,hz,?_,hnorm.trans hq,?_,?_⟩
  · have hn3 : 3 ≤ n := by
      have hlarge : 4096^4 ≤ n := le_max_right _ _
      norm_num at hlarge
      omega
    have hphys := sourceTwoModeOriginalPotential_physical w (1/4) ((n:ℤ)-1) (by omega)
    have hm : 2*((n:ℤ)-1)=2*(n:ℤ)-2 := by ring
    rw [hm] at hphys
    exact hphys
  · rwa [hnorm]
  · have hop := congrArg (fun a : WeightedCoeff (w.negativeSobolev (1/4)) ⊤ =>
        wideEndpointShiftedOperatorNorm w (1/4) (by norm_num) (by norm_num)
          n hn2 (freeHillValue n:ℂ) hz a (-(n:ℤ))) hcoeff
    have hdiag := (sourceEndpointDiagonal_forgetWeight w (1/4) ⟨by norm_num,by norm_num⟩ n Q
      (freeHillValue n:ℂ)).trans
        (congrArg (fun a : WeightedCoeff (w.negativeSobolev (1/4)) ⊤ =>
          endpointDiagonal (1/4) (by norm_num) (by norm_num) n (endpointForgetWeight w (1/4) a,
            (freeHillValue n:ℂ))) hcoeff)
    rw [hop,hforget,hdiag]
    exact hfail

end NLS.Articles.KdVPseudomeasures
