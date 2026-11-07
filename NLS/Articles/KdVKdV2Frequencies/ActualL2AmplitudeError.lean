import NLS.Articles.KdVKdV2Frequencies.ActualL2AmplitudeSquareError
import NLS.SequenceSpaces.AnalyticAmplitudeSourcePullback
import NLS.SequenceSpaces.PositiveBoundedAnalyticFamily

/-! The SAME stored physical amplitude differs from its EXACT free
factor by a bounded analytic inverse-index symbol on ONE original
complex L2 neighborhood, including the finite head and closed gaps. -/
noncomputable section
open Set Metric Complex NLS.KdV Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
variable {q0 : PeriodOneHminusOne}

theorem exists_l2_amplitude_error (D : RoughAbelianFourierDataAt q0)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion 1 (by norm_num) q))
    (hq : periodOneSobolevImageInclusion 1 (by norm_num) q∈ball q0 D.radius) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2), IsOpen U ∧ q∈U ∧
      (∀ a∈U,periodOneSobolevImageInclusion 1 (by norm_num) a∈ball q0 D.radius) ∧
      ∃ C : ℝ,∃ M : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → Coeff ⊤,
        0≤C ∧ AnalyticOnNhd ℂ M U ∧ ∀ a∈U,‖M a‖≤C ∧
          (∀ j : ℤ,j≤0 → M a j=0) ∧ ∀ n : ℕ+,
            M a (n:ℤ)=(1+(n:ℂ))*(D.amplitude (periodOneSobolevImageInclusion 1 (by norm_num) a) (n:ℤ)-
              (hillL2FreeAmplitude n:ℂ)) := by
  let L := periodOneSobolevImageInclusion 1 (by norm_num : (0:ℝ)≤1)
  obtain ⟨V,hV,hqV,_hVD,N,K,hK,hsq⟩ := D.exists_l2_amplitude_squared_error q hr hq
  exact Coeff.exists_analytic_amplitude_error_pullback L (ball q0 D.radius) isOpen_ball
    D.amplitude D.amplitude_analytic V hV q hqV hq hillL2FreeAmplitude hillL2FreeAmplitude_pos
    hillL2FreeAmplitude_le_one (D.native_amplitude_re_pos q hr hq) N K hK hsq

end NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
