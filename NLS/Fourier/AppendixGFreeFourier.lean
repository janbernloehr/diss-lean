import NLS.Fourier.SourceLemmaE3
import NLS.Fourier.UnitIntervalEnergyBound
import NLS.ZakharovShabat.ClassicalFreeFrequencyDifference

/-! # The free-mode comparison used in Appendix G.3

The coefficient difference is the literal Fourier integral of the
exponential difference. Its Fourier-Lebesgue norm is uniformly bounded
near the pi lattice, and its L2 norm is linear in the displacement.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Fourier

/-- Subtracting the coefficient sequences gives the actual integral of the difference. -/
theorem appendixG_free_difference_coefficient {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hq : 1 < q) (z w : ℂ) (k : ℤ) :
    (exponentialFourierCoefficients hq z-exponentialFourierCoefficients hq w) k =
      intervalFourierCoefficient 1 (fun t => unitIntervalExponential z t-
        unitIntervalExponential w t) k := by
  simp only [lp.coeFn_sub,Pi.sub_apply,exponentialFourierCoefficients_apply]
  exact (intervalFourierCoefficient_sub 1 _ _
    (contDiff_unitIntervalExponential z).continuous
    (contDiff_unitIntervalExponential w).continuous k).symm

/-- The same constant works near every positive or negative lattice frequency,
for every q>1, including infinity. -/
theorem appendixG_free_difference_fourier_bound {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hq : 1 < q) (n : ℤ) (z : ℂ)
    (hz : ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) :
    ‖exponentialFourierCoefficients hq z-
      exponentialFourierCoefficients hq ((Real.pi : ℂ)*n)‖ ≤
      2*(2+5*Real.pi/4)*Real.exp (5*Real.pi/4)*unitIntervalC1FourierConstant hq := by
  have h1 := norm_exponentialFourierCoefficients_near_lattice hq n z hz
  have h2 := norm_exponentialFourierCoefficients_near_lattice hq n ((Real.pi : ℂ)*n)
    (by simp only [sub_self,norm_zero]; positivity)
  exact (norm_sub_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

/-- The actual L2 Fourier norm of the free difference is linear in the
displacement from a real reference, with a constant independent of that reference. -/
theorem appendixG_free_difference_l2_bound (z : ℂ) (x : ℝ)
    (hz : ‖z-(x : ℂ)‖ ≤ 1) :
    ‖unitIntervalL2Coefficients
      (fun t => unitIntervalExponential z t-unitIntervalExponential (x : ℂ) t)
      ((contDiff_unitIntervalExponential z).continuous.sub
        (contDiff_unitIntervalExponential (x : ℂ)).continuous)‖ ≤ 2*‖z-(x : ℂ)‖ := by
  apply norm_unitIntervalL2Coefficients_le _ _ _ (by positivity)
  intro t ht
  have h := NLS.ZakharovShabat.norm_classicalFreeFrequencyDifference_le z x (0,1) hz ⟨t,ht⟩
  have hs := (norm_snd_le _).trans h
  simpa [NLS.ZakharovShabat.classicalFreeFrequencyDifference,
    NLS.ZakharovShabat.classicalFreeVector,unitIntervalExponential] using hs

end NLS.Fourier
