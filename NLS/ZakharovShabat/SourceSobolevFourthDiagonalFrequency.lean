import NLS.ZakharovShabat.SourceSobolevFourthFrequencySwap
import NLS.ZakharovShabat.SourceSobolevFourthDiagonal
import NLS.ZakharovShabat.SourceSobolevFourthMomentIdentification

/-! # Odd normalized physical H₄ frequencies on the actual mKdV diagonal -/
noncomputable section
set_option autoImplicit false
namespace NLS.ZakharovShabat

/-- Equality of the original coefficient components is retained in the
native weighted source, rather than inferred from spectral actions. -/
theorem nativeFourth_components_eq_of_original
    (a : NativeFourthSobolevSource)
    (ha : (originalWeightedRealSource fourthSobolevSpectralWeight a).val.fst =
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val.snd) :
    a.val.fst = a.val.snd := by
  apply Subtype.ext
  funext n
  exact (originalWeightedRealSource_fst fourthSobolevSpectralWeight a n).symm.trans
    ((congrArg (fun b : Coeff 2 => b n) ha).trans
      (originalWeightedRealSource_snd fourthSobolevSpectralWeight a n))

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The original physical frequency with the article's exact three shifts
is odd on the whole fractional mKdV diagonal, including closed actions. -/
theorem normalizedSobolevFourthFrequency_odd_of_diagonal
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource)
    (ha : (originalWeightedRealSource fourthSobolevSpectralWeight a).val.fst =
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val.snd) (n : ℤ) :
    D.normalizedSobolevFourthFrequency a (-n) = -D.normalizedSobolevFourthFrequency a n := by
  unfold normalizedSobolevFourthFrequency
  rw [D.sobolevFourthFrequency_odd_of_diagonal a (nativeFourth_components_eq_of_original a ha) n,
    sourceFourthSobolevMomentum_eq_zero_of_diagonal a ha]
  push_cast
  ring

/-- The zero-index normalized physical frequency vanishes on the actual
diagonal, without division by its action or gap length. -/
theorem normalizedSobolevFourthFrequency_zero_of_diagonal
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource)
    (ha : (originalWeightedRealSource fourthSobolevSpectralWeight a).val.fst =
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val.snd) :
    D.normalizedSobolevFourthFrequency a 0 = 0 := by
  have h := D.normalizedSobolevFourthFrequency_odd_of_diagonal a ha 0
  simp only [neg_zero] at h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  apply Complex.ext <;> simp only [Complex.neg_re,Complex.neg_im,Complex.zero_re,Complex.zero_im] at * <;> linarith

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
