import NLS.ZakharovShabat.ClassicalEndpointGradientFourierInterpolation
import NLS.ZakharovShabat.FundamentalFourierSummabilityExponents
import NLS.Fourier.UnitIntervalFourierExponentEmbedding
import NLS.SequenceSpaces.PowerDecaySummability

/-! # Uniform summability from the actual gradient-error time bounds

A single majorant controls all potentials in the Sobolev ball and all
unit vector, endpoint-functional, and gradient-component choices.
-/

noncomputable section
open Set NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Uniform small values and bounded time derivatives imply a whole-sequence ℓp Fourier majorant. -/
theorem exists_classicalGradient_fourier_uniform_memlp_of_time_bounds
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (M A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (ν ω : ℤ → ℂ) (N : ℕ) (hN : 0 < N)
    (h : ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (v : ℂ × ℂ), ‖v‖ ≤ 1 → ∀ (L : (ℂ × ℂ) →L[ℂ] ℂ), ‖L‖ ≤ 1 →
      ∀ n : ℤ, N ≤ n.natAbs → ∀ t : Icc (0 : ℝ) 1,
      ‖classicalEndpointGradientRemainder (classicalSobolevPotential a) (ν n) (ω n) v L t‖ ≤ A/(n.natAbs : ℝ) ∧
      ‖deriv (classicalEndpointGradientRemainder (classicalSobolevPotential a) (ν n) (ω n) v L) t‖ ≤ D) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (v : ℂ × ℂ), ‖v‖ ≤ 1 → ∀ (L : (ℂ × ℂ) →L[ℂ] ℂ), ‖L‖ ≤ 1 →
      ∀ (P : (ℂ × ℂ) →L[ℝ] ℂ), ‖P‖ ≤ 1 → ∀ n : ℤ,
      ‖classicalEndpointGradientFourierCoefficients
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
        (classicalSobolevPotential a) (ν n) (ω n) v L P‖ ≤ b n := by
  have hq1 : 1 < q := lt_of_le_of_lt
    (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq
  obtain ⟨r,ε,he0,he1,her,hr2,hrq,hep⟩ := exists_fundamentalFourier_summability_exponents p hp q hq
  have hr : 1 < r := by linarith
  let K := (2*A+D)*unitIntervalC1FourierConstant (q := ENNReal.ofReal (1+ε))
    (ENNReal.one_lt_ofReal.mpr (by linarith))+A
  let α := fundamentalFourierDecayExponent ε r
  let g (n : ℤ) := K*(n.natAbs : ℝ)^(-α)
  have hg : Memℓp g (ENNReal.ofReal p) := (memlp_inverse_natAbs_rpow p (by linarith) α hep).const_mul K
  let head (n : ℤ) := (24+24*‖ν n‖+12*‖ν n-ω n‖+8*M)*
    (Real.exp (4*M+‖ν n‖+‖ω n‖))^3*unitIntervalC1FourierConstant hq1
  let b (n : ℤ) := if N ≤ n.natAbs then ‖g n‖ else ‖head n‖
  refine ⟨b,?_,?_⟩
  · exact memlp_of_natAbs_eventual_bound p (by linarith) b (fun n => ‖g n‖) hg.norm N
      (by intro n hn; simp [b,hn])
  intro a ha v hv L hL P hP n
  by_cases hn : N ≤ n.natAbs
  · have hn1 : 1 ≤ (n.natAbs : ℝ) := by exact_mod_cast lt_of_lt_of_le hN hn
    have hsmall := norm_classicalEndpointGradientFourierCoefficients_interpolate
      (classicalSobolevPotential a) (ν n) (ω n) v L P hP
      (1+ε) r (by linarith) (by linarith) her hr2 A D (n.natAbs : ℝ) hA hD hn1
      (fun t => (h a ha v hv L hL n hn t).1) (fun t => (h a ha v hv L hL n hn t).2)
    have he : (r-(1+ε))/(2-(1+ε)) = α := by unfold α fundamentalFourierDecayExponent; congr 1 <;> ring
    rw [he] at hsmall
    have hmono := norm_unitIntervalC1Coefficients_mono_exponent (ENNReal.one_lt_ofReal.mpr hr) hq1 hrq
      (fun t => P (classicalEndpointGradientRemainder (classicalSobolevPotential a) (ν n) (ω n) v L t))
      (P.contDiff.comp (contDiff_classicalEndpointGradientRemainder _ _ _ _ _))
    calc
      _ ≤ K/(n.natAbs : ℝ)^α := hmono.trans hsmall
      _ = g n := by dsimp [g]; rw [Real.rpow_neg (by positivity),div_eq_mul_inv]
      _ ≤ b n := by simp only [b,if_pos hn]; exact Real.le_norm_self _
  · exact (norm_classicalEndpointGradientFourierCoefficients_all_frequencies_le hq1 M a ha (ν n) (ω n) v hv L hL P hP).trans
      (by simp only [b,if_neg hn]; exact Real.le_norm_self _)

end NLS.ZakharovShabat
