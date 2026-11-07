import NLS.Articles.KdVKdV2Frequencies.ActualPhysicalAmplitudeValue
import NLS.KdV.HillNativeL2PhysicalSource

/-! Exact real native values of the SAME stored physical amplitude. -/
noncomputable section
open Set Metric Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
variable {q0 : PeriodOneHminusOne}

theorem native_normalized_amplitude_sq_of_physical_ratio (D : RoughAbelianFourierDataAt q0)
    (a : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (ha : periodOneSobolevImageInclusion 1 (by norm_num) a∈ball q0 D.radius)
    (har : WeightedCoeff.conjugateReflection (Weight.sobolev ((1:ℝ)-1)) (Weight.sobolev_neg _) a=a)
    (n : ℕ+) (R : ℂ)
    (hR : ∀ p : RealPeriodOneHillPotential,hillOriginalHminusSource p.val=periodOneSobolevImageInclusion 1 (by norm_num) a →
      R=hillActionGapRatio p.val p.property.1 p.property.2 (n:ℕ)) :
    (D.amplitude (periodOneSobolevImageInclusion 1 (by norm_num) a) (n:ℤ)/(hillL2FreeAmplitude n:ℂ))^2=
      (2*((Real.pi:ℂ)*(n:ℕ)))*R := by
  obtain ⟨p,hp⟩ := native_l2_source_eq_physical a (native_l2_inclusion_real_of_fixed a har)
  have hpD : (hillPhysicalHminusEmbedding p).val∈ball q0 D.radius := by
    rw [←hillOriginalHminusSource_eq_physical,hp]
    exact ha
  rw [←hp,D.normalized_amplitude_sq_physical p hpD n,hR p hp]

theorem native_amplitude_re_pos (D : RoughAbelianFourierDataAt q0)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion 1 (by norm_num) q))
    (hq : periodOneSobolevImageInclusion 1 (by norm_num) q∈ball q0 D.radius) (n : ℕ+) :
    0<(D.amplitude (periodOneSobolevImageInclusion 1 (by norm_num) q) (n:ℤ)).re := by
  obtain ⟨p,hp⟩ := native_l2_source_eq_physical q hr
  have hpD : (hillPhysicalHminusEmbedding p).val∈ball q0 D.radius := by
    rw [←hillOriginalHminusSource_eq_physical,hp]
    exact hq
  have h := D.amplitude_re_pos_physical p hpD n
  rw [hp] at h
  exact h

end NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
