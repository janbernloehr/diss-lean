import NLS.ZakharovShabat.ClassicalDirichletGradientTimeRegularity
import NLS.Fourier.UnitIntervalC1Interpolation
import NLS.ZakharovShabat.FundamentalFourierSummabilityExponents
import NLS.Fourier.UnitIntervalFourierExponentEmbedding

/-! # Fourier interpolation of the normalized Dirichlet gradient error

These are the actual unit-interval Fourier coefficients of the normalized
squared eigenfunction minus the exact free waves. The two time estimates
give a power bound with summable outer exponent.
-/

noncomputable section
open Set NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Actual Fourier coefficients of the gradient error at every exponent above one. -/
def classicalDirichletGradientFourierCoefficients {q : ℝ≥0∞} (hq : 1 < q)
    (φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) : Coeff q :=
  unitIntervalC1Coefficients hq (fun t => P (classicalDirichletGradientError φ z w t))
    (P.contDiff.comp (contDiff_classicalDirichletGradientError φ z w))

@[simp] theorem classicalDirichletGradientFourierCoefficients_apply {q : ℝ≥0∞} (hq : 1 < q)
    (φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) (k : ℤ) :
    classicalDirichletGradientFourierCoefficients hq φ z w P k =
      intervalFourierCoefficient 1 (fun t => P (classicalDirichletNormalizedGradient φ z t-
        classicalDirichletNormalizedGradient 0 w t)) k := rfl

/-- Time differentiation commutes with the fixed scalar observation. -/
theorem deriv_classicalDirichletGradient_observation
    (φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) (t : ℝ) :
    deriv (fun s => P (classicalDirichletGradientError φ z w s)) t =
      P (deriv (classicalDirichletGradientError φ z w) t) :=
  (P.hasFDerivAt.comp_hasDerivAt t
    ((contDiff_one_iff_deriv.mp (contDiff_classicalDirichletGradientError φ z w)).1 t).hasDerivAt).deriv

/-- The actual Fourier norm inherits the interpolation decay from value and derivative bounds. -/
theorem norm_classicalDirichletGradientFourierCoefficients_interpolate
    (φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1)
    (s q : ℝ) (hs : 1 < s) (hs2 : s < 2) (hsq : s ≤ q) (hq2 : q ≤ 2)
    (A D d : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (hd : 1 ≤ d)
    (hv : ∀ t : Icc (0 : ℝ) 1, ‖classicalDirichletGradientError φ z w t‖ ≤ A/d)
    (hder : ∀ t : Icc (0 : ℝ) 1, ‖deriv (classicalDirichletGradientError φ z w) t‖ ≤ D) :
    ‖classicalDirichletGradientFourierCoefficients (q := ENNReal.ofReal q)
      (ENNReal.one_lt_ofReal.mpr (hs.trans_le hsq)) φ z w P‖ ≤
      ((2*A+D)*unitIntervalC1FourierConstant (q := ENNReal.ofReal s)
        (ENNReal.one_lt_ofReal.mpr hs)+A)/d^((q-s)/(2-s)) := by
  have hobs (u : ℂ × ℂ) : ‖P u‖ ≤ ‖u‖ :=
    (P.le_opNorm u).trans (by simpa using mul_le_mul_of_nonneg_right hP (norm_nonneg u))
  apply norm_unitIntervalC1Coefficients_interpolate _ _ s q hs hs2 hsq hq2 A D d hA hD hd
  · intro t ht; exact (hobs _).trans (hv ⟨t,ht⟩)
  · intro t ht
    rw [deriv_classicalDirichletGradient_observation]
    exact (hobs _).trans (hder ⟨t,ht⟩)

/-- One summable power controls every gradient error with the stated time bounds. -/
theorem exists_classicalDirichletGradientFourier_power_bound
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    ∃ K α : ℝ, 0 ≤ K ∧ 1 < α*p ∧
      ∀ (φ : Curve (ℂ × ℂ)) (z w : ℂ)
      (P : (ℂ × ℂ) →L[ℝ] ℂ), ‖P‖ ≤ 1 → ∀ d : ℝ, 1 ≤ d →
      (∀ t : Icc (0 : ℝ) 1, ‖classicalDirichletGradientError φ z w t‖ ≤ A/d) →
      (∀ t : Icc (0 : ℝ) 1, ‖deriv (classicalDirichletGradientError φ z w) t‖ ≤ D) →
      ‖classicalDirichletGradientFourierCoefficients
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
        φ z w P‖ ≤ K*d^(-α) := by
  have hq1 : 1 < q := lt_of_le_of_lt
    (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq
  obtain ⟨r,ε,he0,he1,her,hr2,hrq,hep⟩ := exists_fundamentalFourier_summability_exponents p hp q hq
  have hr : 1 < r := by linarith
  let K := (2*A+D)*unitIntervalC1FourierConstant (q := ENNReal.ofReal (1+ε))
    (ENNReal.one_lt_ofReal.mpr (by linarith))+A
  let α := fundamentalFourierDecayExponent ε r
  refine ⟨K,α,?_,hep,?_⟩
  · let : Fact (1 ≤ ENNReal.ofReal (1+ε)) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    have hconst := unitIntervalC1FourierConstant_nonneg
      (q := ENNReal.ofReal (1+ε)) (ENNReal.one_lt_ofReal.mpr (by linarith))
    positivity
  intro φ z w P hP d hd hv hder
  have hsmall := norm_classicalDirichletGradientFourierCoefficients_interpolate
    φ z w P hP (1+ε) r (by linarith) (by linarith) her hr2 A D d hA hD hd hv hder
  have he : (r-(1+ε))/(2-(1+ε)) = α := by unfold α fundamentalFourierDecayExponent; congr 1 <;> ring
  rw [he] at hsmall
  have hmono := norm_unitIntervalC1Coefficients_mono_exponent (ENNReal.one_lt_ofReal.mpr hr) hq1 hrq
    (fun t => P (classicalDirichletGradientError φ z w t))
    (P.contDiff.comp (contDiff_classicalDirichletGradientError _ _ _))
  calc
    _ ≤ K/d^α := hmono.trans hsmall
    _ = K*d^(-α) := by rw [Real.rpow_neg (by positivity),div_eq_mul_inv]

end NLS.ZakharovShabat
