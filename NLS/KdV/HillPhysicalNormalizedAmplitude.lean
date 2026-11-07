import NLS.KdV.HillFreeNormalizedAmplitude

/-! Exact square and branch of the physically normalized original
Abelian amplitude. The literal 1+n and 2*pi*n factors are both retained. -/
noncomputable section
open Complex
namespace NLS.KdV

theorem physical_normalized_amplitude_sq (p : RealPeriodOneHillPotential) (n : ℕ+) :
    (((Real.sqrt (1+(n:ℝ)):ℂ)*hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 (n:ℕ))/
      (hillL2FreeAmplitude n:ℂ))^2=
        (2*((Real.pi:ℂ)*(n:ℕ)))*hillActionGapRatio p.val p.property.1 p.property.2 (n:ℕ) := by
  have ha : (hillL2FreeAmplitude n:ℂ)^2=(1+(n:ℂ))/(2*(Real.pi:ℂ)*(n:ℂ)) := by
    exact_mod_cast hillL2FreeAmplitude_sq n
  have hs : ((Real.sqrt (1+(n:ℝ)):ℂ))^2=1+(n:ℂ) := by
    rw [←Complex.ofReal_pow,Real.sq_sqrt (by positivity),Complex.ofReal_add,Complex.ofReal_one,
      Complex.ofReal_natCast]
  rw [div_pow,mul_pow,hs,hillAbelianAmplitudePrefactor_sq,ha]
  have hn : 1+(n:ℂ)≠0 := by exact_mod_cast (show 1+(n:ℝ)≠0 by positivity)
  field_simp

theorem physical_normalized_amplitude_re_pos (p : RealPeriodOneHillPotential) (n : ℕ+) :
    0<(((Real.sqrt (1+(n:ℝ)):ℂ)*hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 (n:ℕ))/
      (hillL2FreeAmplitude n:ℂ)).re := by
  rw [div_ofReal_re,mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact div_pos (mul_pos (Real.sqrt_pos.mpr (by positivity)) (hillAbelianAmplitudePrefactor_re_pos p n))
    (hillL2FreeAmplitude_pos n)

end NLS.KdV
