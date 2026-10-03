import NLS.SequenceSpaces.PowerDecaySummability
import NLS.Fourier.UnitIntervalFourierExponentEmbedding
import NLS.ZakharovShabat.FundamentalFourierSummabilityExponents
import NLS.ZakharovShabat.ClassicalSobolevRemainderFourierDecay
import NLS.ZakharovShabat.ClassicalShiftedFreeFourierDecay

/-! # Corollary G.4: common summable Fourier-norm tails

For every finite p > 1 and Fourier exponent q > 1+1/p, including
q = infinity, one ℓp sequence dominates the full family beyond one
cutoff. Initial spectral values are unrestricted.
-/

noncomputable section
open NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- G.4's remainder estimate, with a common ℓp majorant on each Sobolev ball. -/
theorem exists_classicalSobolevRemainder_fourier_memlp_majorant
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) :
    ∃ (N : ℕ) (b : ℤ → ℝ), 0 < N ∧ Memℓp b (ENNReal.ofReal p) ∧
      ∀ (ν : ℤ → ℂ),
      (∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B) →
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ), ‖L‖ ≤ 1 →
      ∀ n : ℤ, N ≤ n.natAbs →
      ‖classicalSobolevRemainderFourierCoefficients
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq) a (ν n) v L‖ ≤ b n*‖v‖ := by
  obtain ⟨r,ε,he0,he1,her,hr2,hrq,hep⟩ := exists_fundamentalFourier_summability_exponents p hp q hq
  have hr : 1 < r := by linarith
  let : Fact (1 ≤ ENNReal.ofReal r) := ⟨ENNReal.one_le_ofReal.mpr hr.le⟩
  obtain ⟨N,hN,h⟩ := exists_classicalSobolevRemainder_sequence_fourier_decay ε r he0 he1 her hr2 M B hB N₀
  let K := classicalSobolevInterpolationConstant ε he0 M B
  let α := fundamentalFourierDecayExponent ε r
  refine ⟨N,(fun n => K*(n.natAbs : ℝ)^(-α)),hN,?_,?_⟩
  · exact (memlp_inverse_natAbs_rpow p (by linarith) α hep).const_mul K
  intro ν hν a ha v L hL n hn
  have hmono := norm_unitIntervalC1Coefficients_mono_exponent
    (ENNReal.one_lt_ofReal.mpr hr)
    (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq) hrq
    (fun t => L (classicalSolutionRemainder (classicalSobolevPotential a) (ν n) v t))
    (contDiff_classicalRemainder_observation _ _ _ _)
  exact hmono.trans ((h ν hν a ha v L hL n hn).trans_eq (by
    dsimp only [K,α]
    rw [Real.rpow_neg (by positivity),div_eq_mul_inv]
    ring))

/-- G.4's shifted-free estimate, uniformly under inverse-index spectral displacement. -/
theorem exists_classicalShiftedFree_fourier_memlp_majorant
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) :
    ∃ (N : ℕ) (b : ℤ → ℝ), 0 < N ∧ Memℓp b (ENNReal.ofReal p) ∧
      ∀ (ν : ℤ → ℂ),
      (∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B/(n.natAbs : ℝ)) →
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ), ‖L‖ ≤ 1 →
      ∀ n : ℤ, N ≤ n.natAbs →
      ‖classicalShiftedFreeFourierCoefficients
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
        (classicalSobolevPotential a) (ν n) (Real.pi*(n : ℝ)) v L‖ ≤ b n*‖v‖ := by
  obtain ⟨r,ε,he0,he1,her,hr2,hrq,hep⟩ := exists_fundamentalFourier_summability_exponents p hp q hq
  have hr : 1 < r := by linarith
  obtain ⟨N,hN,h⟩ := exists_classicalShiftedFree_sequence_fourier_decay ε r he0 he1 her hr2 M B hB N₀
  let K := classicalShiftedFreeInterpolationConstant ε he0 M B
  let α := fundamentalFourierDecayExponent ε r
  refine ⟨N,(fun n => K*(n.natAbs : ℝ)^(-α)),hN,?_,?_⟩
  · exact (memlp_inverse_natAbs_rpow p (by linarith) α hep).const_mul K
  intro ν hν a ha v L hL n hn
  have hmono := norm_unitIntervalC1Coefficients_mono_exponent
    (ENNReal.one_lt_ofReal.mpr hr)
    (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq) hrq
    (fun t => L (classicalShiftedFreeRemainder (classicalSobolevPotential a) (ν n) (Real.pi*(n : ℝ)) v t))
    (L.contDiff.comp (contDiff_classicalShiftedFreeRemainder _ _ _ _))
  exact hmono.trans ((h ν hν a ha v L hL n hn).trans_eq (by
    dsimp only [K,α]
    rw [Real.rpow_neg (by positivity),div_eq_mul_inv]
    ring))

end NLS.ZakharovShabat
