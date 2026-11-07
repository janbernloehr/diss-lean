import NLS.Articles.KdVKdV2Frequencies.ArbitraryBaseAbelianFourierData
import NLS.KdV.HillNativeL2PhysicalRatioDecay
import NLS.KdV.HillNativeL2PhysicalSource
import NLS.Articles.KdVKdV2Frequencies.ActualNativeAmplitudeValue
import NLS.SequenceSpaces.PhysicalAmplitudeSquarePullback

/-! The SAME stored physical amplitude has a quantitative normalized
SQUARED error on one original complex L2 neighborhood before all high
labels. Physical agreement identifies its actual square at closed gaps too. -/
noncomputable section
open Set Metric Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
variable {q0 : PeriodOneHminusOne}

theorem exists_l2_amplitude_squared_error (D : RoughAbelianFourierDataAt q0)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion 1 (by norm_num) q))
    (hq : periodOneSobolevImageInclusion 1 (by norm_num) q∈ball q0 D.radius) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2), IsOpen U ∧ q∈U ∧
      (∀ a∈U,periodOneSobolevImageInclusion 1 (by norm_num) a∈ball q0 D.radius) ∧
      ∃ N : ℕ, ∃ K : ℝ,0≤K ∧ ∀ n : ℕ+,N≤(n:ℕ) → ∀ a∈U,
        (1+(n:ℝ))*‖(D.amplitude (periodOneSobolevImageInclusion 1 (by norm_num) a) (n:ℤ)/
          (hillL2FreeAmplitude n:ℂ))^2-1‖≤K := by
  let v := Weight.sobolev ((1:ℝ)-1)
  let L := periodOneSobolevImageInclusion 1 (by norm_num : (0:ℝ)≤1)
  obtain ⟨V,hV,hqV,N,K,R,hK,hR⟩ := exists_native_l2_physical_actionRatio_decay q hr
  obtain ⟨U,hU,hqU,hUD,hd⟩ := WeightedCoeff.exists_physical_amplitude_square_pullback v
    (Weight.sobolev_neg _) L (ball q0 D.radius) isOpen_ball D.amplitude D.amplitude_analytic
    hillL2FreeAmplitude (fun n => 2*((Real.pi:ℂ)*(n:ℕ)))
    (fun p : RealPeriodOneHillPotential => hillOriginalHminusSource p.val)
    (fun n p => hillActionGapRatio p.val p.property.1 p.property.2 (n:ℕ))
    (fun p hp n => D.normalized_amplitude_sq_physical p hp n)
    (fun a har => native_l2_source_eq_physical a (native_l2_inclusion_real_of_fixed a har))
    V hV q hqV hq (sobolev_conjugateReflection_fixed_of_real_inclusion 1 (by norm_num) q hr)
    R N K (fun _ => rfl) hR
  exact ⟨U,hU,hqU,hUD,N,K,hK,hd⟩

end NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
