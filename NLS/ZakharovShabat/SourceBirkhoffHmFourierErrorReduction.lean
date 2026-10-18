import NLS.ZakharovShabat.SourceBirkhoffHmSpectralTerminal
import NLS.ZakharovShabat.SourceBirkhoffFourierErrorReduction

/-! # Higher-order reduction of the remaining Fourier errors

At each integer m >= 1, membership of the two literal spectral errors
in h^(m+1) implies membership of the actual rectangular Birkhoff-minus-
Fourier error. The spectral-error premises remain explicit: this is
not a proof of their decay or of full one-smoothing.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal

namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- The precise spectral-error reduction at every positive integer Sobolev order. -/
theorem birkhoff_fourier_higher_sobolev_of_spectral_errors
    (m : ℕ) (hm : 1 ≤ m) (a : realTypeHigherSobolevSourceLocus m)
    (A B : WeightedCoeff (Weight.sobolev (m+1)) 2)
    (hA : ∀ n, A.val n = sourceEtaMidpointFourierError (by simp) (by norm_num) (higherSobolevSourceInclusion m a.val) n)
    (hB : ∀ n, B.val n = sourceEtaSineFourierError (by simp) (by norm_num) (higherSobolevSourceInclusion m a.val) n) :
    ∃ E : WeightedCoeff (Weight.sobolev (m+1)) 2 × WeightedCoeff (Weight.sobolev (m+1)) 2,
      ∀ n, (E.1.val n = (sourceBirkhoffMap (by simp) (by norm_num) s (higherSobolevSourceInclusion m a.val)).1 n-
          (sourceBirkhoffFourier (higherSobolevSourceInclusion m a.val)).1 n) ∧
        (E.2.val n = (sourceBirkhoffMap (by simp) (by norm_num) s (higherSobolevSourceInclusion m a.val)).2 n-
          (sourceBirkhoffFourier (higherSobolevSourceInclusion m a.val)).2 n) := by
  obtain ⟨M,_,h⟩ := D.birkhoff_minus_spectral_terminal_uniform_physical_Hm_ball m hm ‖sourcePiSobolevCoordinates m m le_rfl a.val‖
  obtain ⟨u,hu,_⟩ := h a le_rfl 1 (Or.inl rfl)
  obtain ⟨v,hv,_⟩ := h a le_rfl (-1) (Or.inr rfl)
  let X := ((1:ℂ)/(Real.sqrt 8:ℂ)) • (u+v-(4:ℂ) • A)
  let Y := ((1:ℂ)/((Real.sqrt 8:ℂ)*Complex.I)) • (u-v-(4*Complex.I) • B)
  refine ⟨(X,Y),?_⟩
  intro n
  have he := sourceBirkhoff_fourier_error_decomposition (by simp) (by norm_num) (higherSobolevSourceInclusion m a.val) s n
  rw [(D.coordinates _ (D.real_subset a.property) n).1,
    (D.coordinates _ (D.real_subset a.property) n).2]
  constructor
  · rw [he.1]
    simp only [X,WeightedCoeff.smul_val,WeightedCoeff.sub_val,WeightedCoeff.add_val,hu,hv,hA,Complex.ofReal_one,Complex.ofReal_neg]
    ring
  · rw [he.2]
    simp only [Y,WeightedCoeff.smul_val,WeightedCoeff.sub_val,hu,hv,hB,Complex.ofReal_one,Complex.ofReal_neg]
    ring

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
