import NLS.ZakharovShabat.SourceEtaMidpointFourierSobolevBall
import NLS.ZakharovShabat.SourceEtaSineFourierSobolevBall
import NLS.ZakharovShabat.SourceBirkhoffHmFourierErrorReduction

/-! # Bounded Birkhoff Fourier remainders on real Sobolev balls

Both complete spectral errors and the existing angular bound give a uniform h^(m+1) bound for the actual rectangular Birkhoff-minus-Fourier remainder.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- The actual rectangular Birkhoff-minus-Fourier remainder is uniformly
bounded in h^(m+1) on each entire real original Hm ball, for every integer m ≥ 1. -/
theorem birkhoff_fourier_uniform_real_Hm_ball
    (m : ℕ) (hm : 1 ≤ m) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : realTypeHigherSobolevSourceLocus m, ‖a.val‖ ≤ R →
      ∃ E : WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2 × WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2,
        ‖E‖ ≤ C ∧ ∀ n,
        (E.1.val n = (sourceBirkhoffMap (by simp) (by norm_num) s (higherSobolevSourceInclusion m a.val)).1 n-
          (sourceBirkhoffFourier (higherSobolevSourceInclusion m a.val)).1 n) ∧
        (E.2.val n = (sourceBirkhoffMap (by simp) (by norm_num) s (higherSobolevSourceInclusion m a.val)).2 n-
          (sourceBirkhoffFourier (higherSobolevSourceInclusion m a.val)).2 n) := by
  obtain ⟨M,hM,h⟩ := D.birkhoff_minus_spectral_terminal_uniform_physical_Hm_ball m hm (2*(2*Real.pi)^m*R)
  obtain ⟨A₀,hA₀,hA⟩ := exists_uniform_real_sourceEtaMidpointFourierRemainder_bound m hm R hR
  obtain ⟨B₀,hB₀,hB⟩ := exists_uniform_real_sourceEtaSineFourierRemainder_bound m hm R hR
  let c : ℂ := 1/(Real.sqrt 8:ℂ)
  let d : ℂ := 1/((Real.sqrt 8:ℂ)*I)
  let C := ‖c‖*(2*M+4*A₀)+‖d‖*(2*M+4*B₀)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro a ha
  have hphys := (norm_sourcePiSobolevCoordinates_le_native m m le_rfl a.val).trans
    (show 2*(2*Real.pi)^m*‖a.val‖ ≤ 2*(2*Real.pi)^m*R by gcongr)
  obtain ⟨u,hu,hun⟩ := h a hphys 1 (Or.inl rfl)
  obtain ⟨v,hv,hvn⟩ := h a hphys (-1) (Or.inr rfl)
  let A := sourceEtaMidpointFourierRemainder m a.val
  let B := sourceEtaSineFourierRemainder m a.val
  let X := c • (u+v-(4:ℂ) • A)
  let Y := d • (u-v-(4*I:ℂ) • B)
  have hX : ‖X‖ ≤ ‖c‖*(2*M+4*A₀) := by
    dsimp only [X]
    rw [norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg c)
    have ht := norm_sub_le (u+v) ((4:ℂ) • A)
    simp only [norm_smul,norm_ofNat] at ht
    have hAn := (hA a ha).1
    change ‖A‖ ≤ A₀ at hAn
    linarith [norm_add_le u v]
  have hY : ‖Y‖ ≤ ‖d‖*(2*M+4*B₀) := by
    dsimp only [Y]
    rw [norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg d)
    have ht := norm_sub_le (u-v) ((4*I:ℂ) • B)
    simp only [norm_smul,norm_mul,norm_ofNat,norm_I,mul_one] at ht
    have hBn := (hB a ha).1
    change ‖B‖ ≤ B₀ at hBn
    linarith [norm_sub_le u v]
  refine ⟨(X,Y),?_,?_⟩
  · change max ‖X‖ ‖Y‖ ≤ C
    dsimp only [C]
    exact max_le (hX.trans (le_add_of_nonneg_right (by positivity)))
      (hY.trans (le_add_of_nonneg_left (by positivity)))
  · intro n
    have he := sourceBirkhoff_fourier_error_decomposition (by simp) (by norm_num) (higherSobolevSourceInclusion m a.val) s n
    rw [(D.coordinates _ (D.real_subset a.property) n).1,
      (D.coordinates _ (D.real_subset a.property) n).2]
    constructor
    · rw [he.1]
      simp only [X,c,WeightedCoeff.smul_val,WeightedCoeff.sub_val,WeightedCoeff.add_val,hu,hv,
        A,(hA a ha).2,Complex.ofReal_one,Complex.ofReal_neg]
      ring
    · rw [he.2]
      simp only [Y,d,WeightedCoeff.smul_val,WeightedCoeff.sub_val,hu,hv,
        B,(hB a ha).2,Complex.ofReal_one,Complex.ofReal_neg]
      ring

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
