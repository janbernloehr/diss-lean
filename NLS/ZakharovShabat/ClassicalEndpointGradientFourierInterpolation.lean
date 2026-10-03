import NLS.ZakharovShabat.ClassicalSobolevGradientDerivativeBounds
import NLS.Fourier.UnitIntervalC1Interpolation
import NLS.ZakharovShabat.ClassicalEndpointGradientL2

/-! # Fourier interpolation for the actual potential-gradient error -/

noncomputable section
open Set NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Actual Fourier coefficients of the gradient error at every exponent above one. -/
def classicalEndpointGradientFourierCoefficients {q : ℝ≥0∞} (hq : 1 < q)
    (φ : Curve (ℂ × ℂ)) (z w : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) : Coeff q :=
  unitIntervalC1Coefficients hq (fun t => P (classicalEndpointGradientRemainder φ z w v L t))
    (P.contDiff.comp (contDiff_classicalEndpointGradientRemainder φ z w v L))

@[simp] theorem classicalEndpointGradientFourierCoefficients_apply {q : ℝ≥0∞} (hq : 1 < q)
    (φ : Curve (ℂ × ℂ)) (z w : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) (k : ℤ) :
    classicalEndpointGradientFourierCoefficients hq φ z w v L P k =
      intervalFourierCoefficient 1 (fun t => P (classicalEndpointGradient φ z v L t-
        classicalFreeEndpointGradient w v L t)) k := rfl

/-- At exponent two this is exactly the previously constructed Hilbert sequence. -/
@[simp] theorem classicalEndpointGradientFourierCoefficients_two
    (φ : Curve (ℂ × ℂ)) (z w : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) :
    classicalEndpointGradientFourierCoefficients (q := 2) (by norm_num) φ z w v L P =
      classicalEndpointGradientRemainderL2Coefficients φ z w v L P := by
  ext k
  rfl

/-- Time differentiation commutes with the fixed scalar observation. -/
theorem deriv_classicalEndpointGradient_observation
    (φ : Curve (ℂ × ℂ)) (z w : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) (t : ℝ) :
    deriv (fun s => P (classicalEndpointGradientRemainder φ z w v L s)) t =
      P (deriv (classicalEndpointGradientRemainder φ z w v L) t) :=
  (P.hasFDerivAt.comp_hasDerivAt t
    ((contDiff_one_iff_deriv.mp (contDiff_classicalEndpointGradientRemainder φ z w v L)).1 t).hasDerivAt).deriv

/-- The actual Fourier norm inherits the interpolation decay from value and derivative bounds. -/
theorem norm_classicalEndpointGradientFourierCoefficients_interpolate
    (φ : Curve (ℂ × ℂ)) (z w : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1)
    (s q : ℝ) (hs : 1 < s) (hs2 : s < 2) (hsq : s ≤ q) (hq2 : q ≤ 2)
    (A D d : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (hd : 1 ≤ d)
    (hv : ∀ t : Icc (0 : ℝ) 1, ‖classicalEndpointGradientRemainder φ z w v L t‖ ≤ A/d)
    (hder : ∀ t : Icc (0 : ℝ) 1, ‖deriv (classicalEndpointGradientRemainder φ z w v L) t‖ ≤ D) :
    ‖classicalEndpointGradientFourierCoefficients (q := ENNReal.ofReal q)
      (ENNReal.one_lt_ofReal.mpr (hs.trans_le hsq)) φ z w v L P‖ ≤
      ((2*A+D)*unitIntervalC1FourierConstant (q := ENNReal.ofReal s)
        (ENNReal.one_lt_ofReal.mpr hs)+A)/d^((q-s)/(2-s)) := by
  have hobs (u : ℂ × ℂ) : ‖P u‖ ≤ ‖u‖ :=
    (P.le_opNorm u).trans (by simpa using mul_le_mul_of_nonneg_right hP (norm_nonneg u))
  apply norm_unitIntervalC1Coefficients_interpolate _ _ s q hs hs2 hsq hq2 A D d hA hD hd
  · intro t ht; exact (hobs _).trans (hv ⟨t,ht⟩)
  · intro t ht
    rw [deriv_classicalEndpointGradient_observation]
    exact (hobs _).trans (hder ⟨t,ht⟩)

/-- A finite-head bound for every q>1, including infinity. -/
theorem norm_classicalEndpointGradientFourierCoefficients_all_frequencies_le
    {q : ℝ≥0∞} (hq : 1 < q)
    (M : ℝ) (a : ScalarDomain 2 × ScalarDomain 2) (ha : ‖a‖ ≤ M) (z w : ℂ)
    (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1) (L : (ℂ × ℂ) →L[ℂ] ℂ) (hL : ‖L‖ ≤ 1)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1) :
    ‖classicalEndpointGradientFourierCoefficients hq (classicalSobolevPotential a) z w v L P‖ ≤
      (24+24*‖z‖+12*‖z-w‖+8*M)*(Real.exp (4*M+‖z‖+‖w‖))^3*unitIntervalC1FourierConstant hq := by
  let : Fact (1 ≤ q) := ⟨hq.le⟩
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  have hobs (u : ℂ × ℂ) : ‖P u‖ ≤ ‖u‖ :=
    (P.le_opNorm u).trans (by simpa using mul_le_mul_of_nonneg_right hP (norm_nonneg u))
  apply (norm_unitIntervalC1Coefficients_le hq _ _
    (12*(Real.exp (4*M+‖z‖+‖w‖))^3)
    ((24*‖z‖+12*‖z-w‖+8*M)*(Real.exp (4*M+‖z‖+‖w‖))^3)
    (by positivity) (by positivity) ?_ ?_).trans_eq (by ring)
  · intro t ht
    exact (hobs _).trans (norm_classicalEndpointGradientRemainder_all_frequencies_le M a ha z w v hv L hL ⟨t,ht⟩)
  · intro t ht
    rw [deriv_classicalEndpointGradient_observation]
    exact (hobs _).trans (norm_deriv_classicalEndpointGradientRemainder_all_frequencies_le M a ha z w v hv L hL ⟨t,ht⟩)

end NLS.ZakharovShabat
