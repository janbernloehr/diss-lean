import NLS.KdV.HillAbelianCoordinateFactor

/-! Exact free amplitudes for the normalized original L2 packet.
The finite-index factor sqrt((1+n)/(2*pi*n)) is retained. -/
noncomputable section
open Complex
namespace NLS.KdV

def hillL2FreeAmplitude (n : ℕ+) : ℝ := Real.sqrt (1+(n:ℝ))/Real.sqrt (2*Real.pi*(n:ℝ))

theorem hillL2FreeAmplitude_pos (n : ℕ+) : 0<hillL2FreeAmplitude n := by
  unfold hillL2FreeAmplitude
  positivity

theorem hillL2FreeAmplitude_sq (n : ℕ+) : (hillL2FreeAmplitude n)^2=(1+(n:ℝ))/(2*Real.pi*(n:ℝ)) := by
  rw [hillL2FreeAmplitude,div_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]

theorem hillL2FreeAmplitude_le_one (n : ℕ+) : hillL2FreeAmplitude n≤1 := by
  apply (sq_le_sq₀ (hillL2FreeAmplitude_pos n).le zero_le_one).mp
  rw [hillL2FreeAmplitude_sq,one_pow]
  apply (div_le_one (by positivity : 0<2*Real.pi*(n:ℝ))).mpr
  have hn : (1:ℝ)≤n := by exact_mod_cast n.property
  nlinarith [Real.pi_gt_three]

theorem hillAbelianAmplitudePrefactor_sq (p : RealPeriodOneHillPotential) (n : ℕ+) :
    (hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 (n:ℕ))^2=
      hillActionGapRatio p.val p.property.1 p.property.2 (n:ℕ) := by
  have hp := hillActionGapRatio_real_positive p.val p.property.1 p.property.2 (n:ℕ) n.property
  have he : hillActionGapRatio p.val p.property.1 p.property.2 (n:ℕ)=
      ((hillActionGapRatio p.val p.property.1 p.property.2 (n:ℕ)).re:ℂ) := Complex.ext rfl (by simpa using hp.2)
  have hs : ((Real.sqrt (2*(hillActionGapRatio p.val p.property.1 p.property.2 (n:ℕ)).re):ℂ))^2=
      2*((hillActionGapRatio p.val p.property.1 p.property.2 (n:ℕ)).re:ℂ) := by
    rw [←Complex.ofReal_pow,Real.sq_sqrt (by linarith [hp.1]),Complex.ofReal_mul,Complex.ofReal_ofNat]
  have ht : ((Real.sqrt 2:ℂ))^2=2 := by
    rw [←Complex.ofReal_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Complex.ofReal_ofNat]
  unfold hillAbelianAmplitudePrefactor hillActionGapPrefactor
  rw [div_pow,hs,ht]
  calc
    _ = ((hillActionGapRatio p.val p.property.1 p.property.2 (n:ℕ)).re:ℂ) := by ring
    _ = _ := he.symm

theorem hillAbelianAmplitudePrefactor_re_pos (p : RealPeriodOneHillPotential) (n : ℕ+) :
    0<(hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 (n:ℕ)).re := by
  have hp := (hillActionGapRatio_real_positive p.val p.property.1 p.property.2 (n:ℕ) n.property).1
  change 0<((Real.sqrt (2*(hillActionGapRatio p.val p.property.1 p.property.2 (n:ℕ)).re):ℂ)/(Real.sqrt 2:ℂ)).re
  rw [div_ofReal_re,Complex.ofReal_re]
  positivity

end NLS.KdV
