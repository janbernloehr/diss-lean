import NLS.SequenceSpaces.PiSobolevEmbedding
import NLS.ZakharovShabat.AbsolutePotentialHeight
import NLS.ZakharovShabat.WeightedFreePencil

/-! # The global H¹ imaginary spectral bound in Theorem 25.1 -/
noncomputable section
namespace NLS.ZakharovShabat

/-- Every original periodic eigenvalue has imaginary part bounded by the source H¹ pair norm. -/
theorem abs_im_le_H1_norm
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (z : ℂ) (hz : z ∈ periodicSpectrum (by simp)
      (weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ)) : |z.im| ≤ ‖φ‖ := by
  let a := WeightedCoeff.piSobolevToL1 φ.fst
  let b := WeightedCoeff.piSobolevToL1 φ.snd
  have h := periodicSpectrum_im_sq_le_l1 (by simp) _ a b
    (by intro k; simp [a]) (by intro k; simp [b]) z hz
  have ha := WeightedCoeff.norm_piSobolevToL1_sq_le φ.fst
  have hb := WeightedCoeff.norm_piSobolevToL1_sq_le φ.snd
  have hab : ‖a‖*‖b‖ ≤ ‖φ‖^2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖a‖*‖b‖ ≤ ‖φ.fst‖^2+‖φ.snd‖^2
    change ‖a‖^2 ≤ 2*‖φ.fst‖^2 at ha
    change ‖b‖^2 ≤ 2*‖φ.snd‖^2 at hb
    nlinarith [sq_nonneg (‖a‖-‖b‖)]
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp (h.trans hab)

end NLS.ZakharovShabat
