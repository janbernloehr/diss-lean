import NLS.Articles.KdVKdV2Frequencies.ArbitraryBaseAbelianFourierData
import NLS.KdV.HillPhysicalNormalizedAmplitude

/-! Exact physical values of the SAME stored amplitude and its branch. -/
noncomputable section
open Set Metric Complex NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
variable {q0 : PeriodOneHminusOne}

theorem normalized_amplitude_sq_physical (D : RoughAbelianFourierDataAt q0)
    (p : RealPeriodOneHillPotential) (hp : (hillPhysicalHminusEmbedding p).val∈ball q0 D.radius) (n : ℕ+) :
    (D.amplitude (hillOriginalHminusSource p.val) (n:ℤ)/(hillL2FreeAmplitude n:ℂ))^2=
      (2*((Real.pi:ℂ)*(n:ℕ)))*hillActionGapRatio p.val p.property.1 p.property.2 (n:ℕ) := by
  rw [hillOriginalHminusSource_eq_physical,D.amplitude_physical p hp n]
  exact physical_normalized_amplitude_sq p n

theorem amplitude_re_pos_physical (D : RoughAbelianFourierDataAt q0)
    (p : RealPeriodOneHillPotential) (hp : (hillPhysicalHminusEmbedding p).val∈ball q0 D.radius) (n : ℕ+) :
    0<(D.amplitude (hillOriginalHminusSource p.val) (n:ℤ)).re := by
  rw [hillOriginalHminusSource_eq_physical,D.amplitude_physical p hp n,mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_pos (Real.sqrt_pos.mpr (by positivity)) (hillAbelianAmplitudePrefactor_re_pos p n)

end NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
