import NLS.ZakharovShabat.SourceEtaMidpointFourierAnalytic
import NLS.ZakharovShabat.SourceEtaSineFourierAnalytic
import NLS.ZakharovShabat.SourceBirkhoffHmComplexFourierErrorReduction

/-! # Positive-integer Birkhoff-minus-Fourier one-smoothing

The two proved analytic spectral remainders complete the local complex one-derivative Fourier remainder at every positive integer Sobolev order.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- The actual rectangular Birkhoff-minus-Fourier map gains one derivative
analytically near every real original Hm source, for every integer m ≥ 1.
Both spectral-error estimates are supplied by the preceding theorems. -/
theorem exists_local_higherSobolevBirkhoffFourier_analytic
    (m : ℕ) (hm : 1 ≤ m) (a : realTypeHigherSobolevSourceLocus m) :
    ∃ V : Set (SobolevSource m), IsOpen V ∧ a.val ∈ V ∧
      ∃ E : SobolevSource m → WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2 ×
        WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2,
        AnalyticOnNhd ℂ E V ∧ ∀ b ∈ V, ∀ n,
          (E b).1.val n = (sourceBirkhoffMap (by simp) (by norm_num) s (higherSobolevSourceInclusion m b)).1 n-
            (sourceBirkhoffFourier (higherSobolevSourceInclusion m b)).1 n ∧
          (E b).2.val n = (sourceBirkhoffMap (by simp) (by norm_num) s (higherSobolevSourceInclusion m b)).2 n-
            (sourceBirkhoffFourier (higherSobolevSourceInclusion m b)).2 n := by
  obtain ⟨U,hU,haU,_,_,hAa,hA⟩ := exists_local_sourceEtaMidpointFourierRemainder_analytic m hm a
  obtain ⟨V,hV,haV,_,_,hBa,hB⟩ := exists_local_sourceEtaSineFourierRemainder_analytic m hm a
  obtain ⟨Z,hZ,haZ,_,E,hE,he⟩ := D.exists_local_higherSobolevBirkhoffFourier_analytic_of_spectral_errors
    m hm a (U ∩ V) (hU.inter hV) ⟨haU,haV⟩
    (sourceEtaMidpointFourierRemainder m) (sourceEtaSineFourierRemainder m)
    (fun b hb => hAa b hb.1) (fun b hb => hBa b hb.2)
    (fun b hb => (hA b hb.1).2) (fun b hb => (hB b hb.2).2)
  exact ⟨Z,hZ,haZ,E,hE,he⟩

end SourceBirkhoffMapComplexData

/-- A constructed Birkhoff map has the analytic one-derivative Fourier
remainder at every positive integer Sobolev order, with the same root family
at all orders and no unproved spectral regularity premise. -/
theorem exists_sourceBirkhoffMap_positive_integer_one_smoothing :
    ∃ W₀ B W : Set (CoeffPair 2), ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
      SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s ∧
      ∀ m : ℕ, 1 ≤ m → ∀ a : realTypeHigherSobolevSourceLocus m,
      ∃ V : Set (SobolevSource m), IsOpen V ∧ a.val ∈ V ∧
      ∃ E : SobolevSource m → WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2 ×
        WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2,
        AnalyticOnNhd ℂ E V ∧ ∀ b ∈ V, ∀ n,
          (E b).1.val n = (sourceBirkhoffMap (by simp) (by norm_num) s (higherSobolevSourceInclusion m b)).1 n-
            (sourceBirkhoffFourier (higherSobolevSourceInclusion m b)).1 n ∧
          (E b).2.val n = (sourceBirkhoffMap (by simp) (by norm_num) s (higherSobolevSourceInclusion m b)).2 n-
            (sourceBirkhoffFourier (higherSobolevSourceInclusion m b)).2 n := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  exact ⟨W₀,B,W,s,D,fun m hm a => D.exists_local_higherSobolevBirkhoffFourier_analytic m hm a⟩

end NLS.ZakharovShabat
