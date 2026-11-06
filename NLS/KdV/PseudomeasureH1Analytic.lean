import NLS.KdV.PseudomeasureAnalytic

/-!
# Norm-analytic complementary inverse into the original H1 domain

The order-two infinity symbol is multiplied by the square-summable inverse
Sobolev weight of order `1-r`. This proves operator-norm analyticity with
values in the full original H1 space, including at effective determinant zeros.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The strict endpoint range supplies the square-summable H1 inverse weight. -/
def endpointInverseH1Weight (r : ℝ) (hr1 : r < 1/2) : Coeff 2 :=
  ⟨fun k => (Weight.sobolev (1-r) k:ℂ)⁻¹,
    Weight.inverse_sobolev_memlp (by norm_num) (by norm_num; linarith)⟩

/-- Exact normalization of the endpoint-to-H1 reciprocal symbol. -/
theorem endpointH1Symbol_weight_identity (r : ℝ) (k : ℤ) :
    (Weight.sobolev 2 k:ℂ)*(Weight.sobolev (1-r) k:ℂ)⁻¹ =
      (Weight.sobolev 1 k:ℂ)/(SpectralWeight.one.negativeSobolev r k:ℂ) := by
  have h2 : Weight.sobolev 2 k =
      Weight.sobolev (1-r) k * Weight.sobolev 1 k * Weight.sobolev r k := by
    calc
      _ = Weight.sobolev ((1-r)+1+r) k := by rw [show (1-r)+1+r = (2:ℝ) by ring]
      _ = _ := by rw [Weight.sobolev_add, Weight.sobolev_add]
  simp only [h2, Complex.ofReal_mul, SpectralWeight.negativeSobolev_apply,
    SpectralWeight.one_apply, Complex.ofReal_div, Complex.ofReal_one]
  let A : ℂ := (Weight.sobolev (1-r) k:ℂ)
  let B : ℂ := (Weight.sobolev 1 k:ℂ)
  let C : ℂ := (Weight.sobolev r k:ℂ)
  have hA : A ≠ 0 := (Weight.sobolev (1-r)).complex_ne_zero k
  change (A*B*C)*A⁻¹ = B/(1/C)
  calc
    _ = (A*A⁻¹)*(B*C) := by ring
    _ = _ := by simp [hA, div_eq_mul_inv]

/-- The total square-summable normalized complementary symbol. -/
def endpointH1SymbolFamily (r : ℝ) (hr1 : r < 1/2) (n : ℕ) (z : ℂ) : Coeff 2 :=
  Coeff.holderProduct (p := ⊤) (r := 2) (q := 2)
    (hillOrderTwoSymbolFamily n z) (endpointInverseH1Weight r hr1)

/-- Exact H1 symbol on the entire corrected closed strip. -/
theorem endpointH1SymbolFamily_apply (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n) (k : ℤ) :
    endpointH1SymbolFamily r hr1 n z k =
      ((Weight.sobolev 1 k:ℂ)/(SpectralWeight.one.negativeSobolev r k:ℂ))*
        reducedHillSymbol n hn z hz k := by
  change hillOrderTwoSymbolFamily n z k * (Weight.sobolev (1-r) k:ℂ)⁻¹ = _
  rw [hillOrderTwoSymbolFamily_eq_symbol n hn z hz k]
  calc
    _ = ((Weight.sobolev 2 k:ℂ)*(Weight.sobolev (1-r) k:ℂ)⁻¹)*
        reducedHillSymbol n hn z hz k := by ring
    _ = _ := by rw [endpointH1Symbol_weight_identity]

/-- The H1-normalized symbol is analytic in the l2 norm, even at strip boundary points. -/
theorem analyticAt_endpointH1SymbolFamily (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    AnalyticAt ℂ (endpointH1SymbolFamily r hr1 n) z := by
  let P : Coeff ⊤ →L[ℂ] Coeff 2 →L[ℂ] Coeff 2 := Coeff.holderProduct
  change AnalyticAt ℂ ((P.flip (endpointInverseH1Weight r hr1)) ∘ hillOrderTwoSymbolFamily n) z
  exact ((P.flip (endpointInverseH1Weight r hr1)).analyticAt _).comp
    (analyticAt_hillOrderTwoSymbolFamily n hn z hz)

/-- A total complementary inverse family with values in the original physical H1 domain. -/
def endpointH1ResolventFamily (r : ℝ) (hr1 : r < 1/2) (n : ℕ) (z : ℂ) :
    WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ →L[ℂ]
      FourierLebesgueSpace (2:ℝ) 1 2 :=
  (sobolevCoefficients 1 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((WeightedCoeff.weightIsometry (Weight.sobolev 1) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (((Coeff.holderProduct (p := ⊤) (r := 2) (q := 2)).flip
        (endpointH1SymbolFamily r hr1 n z)).comp
          (WeightedCoeff.weightIsometry (SpectralWeight.one.negativeSobolev r) ⊤).toContinuousLinearEquiv.toContinuousLinearMap))

/-- Every original Fourier coefficient is the exact reduced inverse coefficient. -/
theorem endpointH1ResolventFamily_coefficient (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (k : ℤ) :
    (endpointH1ResolventFamily r hr1 n z a).val (mode (-k)) =
      reducedHillSymbol n hn z hz k * a.val k := by
  change ((sobolevCoefficients 1 2) ((sobolevCoefficients 1 2).symm _)).val k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change ((SpectralWeight.one.negativeSobolev r k:ℂ)*a.val k*
    endpointH1SymbolFamily r hr1 n z k)/(Weight.sobolev 1 k:ℂ) = _
  rw [endpointH1SymbolFamily_apply r hr1 n hn z hz k]
  let W : ℂ := (SpectralWeight.one.negativeSobolev r k:ℂ)
  let V : ℂ := (Weight.sobolev 1 k:ℂ)
  have hW : W ≠ 0 := (SpectralWeight.one.negativeSobolev r).complex_ne_zero k
  have hV : V ≠ 0 := (Weight.sobolev 1).complex_ne_zero k
  change (W*a.val k*((V/W)*reducedHillSymbol n hn z hz k))/V = _
  calc
    _ = (W/W)*(V/V)*(reducedHillSymbol n hn z hz k*a.val k) := by ring
    _ = _ := by rw [div_self hW, div_self hV, one_mul, one_mul]

/-- Equality on the whole original H1 space, rather than just a coefficient bound. -/
theorem endpointH1ResolventFamily_eq (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    endpointH1ResolventFamily r hr1 n z =
      endpointReducedHillResolventH1Original SpectralWeight.one r hr1 n hn z hz := by
  apply ContinuousLinearMap.ext
  intro a
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  rw [endpointH1ResolventFamily_coefficient r hr1 n hn z hz,
    endpointReducedHillResolventH1Original_coefficient]

/-- Analyticity in the bounded-operator norm from endpoint data into original H1. -/
theorem analyticAt_endpointH1ResolventFamily (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    AnalyticAt ℂ (endpointH1ResolventFamily r hr1 n) z := by
  let P : Coeff ⊤ →L[ℂ] Coeff 2 →L[ℂ] Coeff 2 := Coeff.holderProduct
  have hP := (P.flip.analyticAt (endpointH1SymbolFamily r hr1 n z)).comp
    (analyticAt_endpointH1SymbolFamily r hr1 n hn z hz)
  exact SchurComplement.analyticAt_compCLM analyticAt_const
    (SchurComplement.analyticAt_compCLM analyticAt_const
      (SchurComplement.analyticAt_compCLM hP analyticAt_const))

/-- The H1 and Wiener analytic families represent exactly the same distribution. -/
theorem endpointH1ResolventFamily_toWiener (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    (endpointH1ToWiener r hr1).comp (endpointH1ResolventFamily r hr1 n z) =
      endpointWienerResolventFamily r hr1 n z := by
  rw [endpointH1ResolventFamily_eq r hr1 n hn z hz,
    endpointWienerResolventFamily_eq r hr1 n hn z hz]

/-- The free physical pencil applied to the analytic complement leaves precisely
the original forcing with its two resonant modes removed. -/
theorem endpointH1ResolventFamily_free_residual (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) :
    z • singularHillDomainInclusion (endpointH1ResolventFamily r hr1 n z a) -
      singularHillLaplacian (endpointH1ResolventFamily r hr1 n z a) =
      endpointHillHminusOne SpectralWeight.one r hr1 a -
        singularHillDomainInclusion (endpointHillH1Modes n
          (hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n a)) := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  change z * (singularHillDomainInclusion _).val (mode (-k)) -
    (singularHillLaplacian _).val (mode (-k)) =
      (endpointHillHminusOne SpectralWeight.one r hr1 a).val (mode (-k)) -
        (singularHillDomainInclusion _).val (mode (-k))
  rw [singularHillDomainInclusion_coefficient, singularHillLaplacian_coefficient,
    endpointHillHminusOne_coefficient, singularHillDomainInclusion_coefficient,
    endpointHillH1Modes_coefficient, endpointH1ResolventFamily_coefficient r hr1 n hn z hz]
  change z * (reducedHillSymbol n hn z hz k * a.val k) -
    (freeHillValue k:ℂ) * (reducedHillSymbol n hn z hz k * a.val k) =
      a.val k - ((if k = (n:ℤ) then a.val n else 0) +
        (if k = -(n:ℤ) then a.val (-(n:ℤ)) else 0))
  by_cases hkp : k = (n:ℤ)
  · subst k
    simp [reducedHillSymbol, show (n:ℤ) ≠ -(n:ℤ) by omega]
  by_cases hkm : k = -(n:ℤ)
  · subst k
    simp [reducedHillSymbol, show -(n:ℤ) ≠ (n:ℤ) by omega]
  have hk : k.natAbs ≠ n := fun he => ((hill_resonance_iff n k).mp he).elim hkp hkm
  simp only [if_neg hkp, if_neg hkm, zero_add, sub_zero, reducedHillSymbol, if_neg hk]
  rw [← sub_mul, ← mul_assoc, mul_inv_cancel₀ (freeHill_denominator_ne_zero hn hz hk), one_mul]

end NLS.KdV
