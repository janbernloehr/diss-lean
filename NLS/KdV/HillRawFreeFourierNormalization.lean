import NLS.KdV.HillFreeNormalizedAmplitude

noncomputable section
open Complex
namespace NLS.KdV

theorem raw_free_amplitude_fourier_normalization (n : ℕ+) :
    Weight.sobolev (1/2) (n:ℤ)*hillL2FreeAmplitude n/(1+(n:ℝ))=
      (Real.sqrt (2*Real.pi*(n:ℝ)))⁻¹ := by
  have hw : Weight.sobolev (1/2) (n:ℤ)=Real.sqrt (1+(n:ℝ)) := by
    simp only [Weight.sobolev_apply,Int.cast_natCast,
      abs_of_pos (by positivity : (0:ℝ)<n),Real.sqrt_eq_rpow]
  rw [hw,hillL2FreeAmplitude]
  have hs := Real.sq_sqrt (by positivity : (0:ℝ)≤1+(n:ℝ))
  have hden : Real.sqrt (2*Real.pi*(n:ℝ))≠0 := by positivity
  have hn : 1+(n:ℝ)≠0 := by positivity
  field_simp
  nlinarith

end NLS.KdV
