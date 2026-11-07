import NLS.KdV.PseudomeasureWideAnalytic
import NLS.KdV.PseudomeasureH1Analytic

/-! The same analytic H1 complementary inverse on the full printed strip,
including both exact coefficient and full physical residual identities. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

theorem endpointWienerResolventFamily_eq_wide (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n) :
    endpointWienerResolventFamily r hr1 n z = (endpointH1ToWiener r hr1).comp
      (wideEndpointHillResolventH1 SpectralWeight.one r hr1 n hn z hz) := by
  ext a
  apply Subtype.ext
  funext k
  rw [endpointWienerResolventFamily_apply_wide r hr1 n hn z hz]
  exact ((endpointH1ToWiener_apply r hr1 _ k).trans
    (wideEndpointHillResolventH1_coefficient SpectralWeight.one r hr1 n hn z hz a k)).symm


theorem endpointH1SymbolFamily_apply_wide (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n) (k : ℤ) :
    endpointH1SymbolFamily r hr1 n z k =
      ((Weight.sobolev 1 k:ℂ)/(SpectralWeight.one.negativeSobolev r k:ℂ))*
        wideHillSymbol n z k := by
  change hillOrderTwoSymbolFamily n z k * (Weight.sobolev (1-r) k:ℂ)⁻¹ = _
  rw [hillOrderTwoSymbolFamily_eq_wide_symbol n hn z hz k]
  calc
    _ = ((Weight.sobolev 2 k:ℂ)*(Weight.sobolev (1-r) k:ℂ)⁻¹)*
        wideHillSymbol n z k := by ring
    _ = _ := by rw [endpointH1Symbol_weight_identity]


theorem analyticAt_endpointH1SymbolFamily_wide (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n) :
    AnalyticAt ℂ (endpointH1SymbolFamily r hr1 n) z := by
  let P : Coeff ⊤ →L[ℂ] Coeff 2 →L[ℂ] Coeff 2 := Coeff.holderProduct
  change AnalyticAt ℂ ((P.flip (endpointInverseH1Weight r hr1)) ∘ hillOrderTwoSymbolFamily n) z
  exact ((P.flip (endpointInverseH1Weight r hr1)).analyticAt _).comp
    (analyticAt_hillOrderTwoSymbolFamily_wide n hn z hz)


theorem endpointH1ResolventFamily_coefficient_wide (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (k : ℤ) :
    (endpointH1ResolventFamily r hr1 n z a).val (mode (-k)) =
      wideHillSymbol n z k * a.val k := by
  change ((sobolevCoefficients 1 2) ((sobolevCoefficients 1 2).symm _)).val k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change ((SpectralWeight.one.negativeSobolev r k:ℂ)*a.val k*
    endpointH1SymbolFamily r hr1 n z k)/(Weight.sobolev 1 k:ℂ) = _
  rw [endpointH1SymbolFamily_apply_wide r hr1 n hn z hz k]
  let W : ℂ := (SpectralWeight.one.negativeSobolev r k:ℂ)
  let V : ℂ := (Weight.sobolev 1 k:ℂ)
  have hW : W ≠ 0 := (SpectralWeight.one.negativeSobolev r).complex_ne_zero k
  have hV : V ≠ 0 := (Weight.sobolev 1).complex_ne_zero k
  change (W*a.val k*((V/W)*wideHillSymbol n z k))/V = _
  calc
    _ = (W/W)*(V/V)*(wideHillSymbol n z k*a.val k) := by ring
    _ = _ := by rw [div_self hW, div_self hV, one_mul, one_mul]


theorem endpointH1ResolventFamily_eq_wide (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n) :
    endpointH1ResolventFamily r hr1 n z =
      wideEndpointHillResolventH1 SpectralWeight.one r hr1 n hn z hz := by
  apply ContinuousLinearMap.ext
  intro a
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  rw [endpointH1ResolventFamily_coefficient_wide r hr1 n hn z hz,
    wideEndpointHillResolventH1_coefficient]


theorem analyticAt_endpointH1ResolventFamily_wide (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n) :
    AnalyticAt ℂ (endpointH1ResolventFamily r hr1 n) z := by
  let P : Coeff ⊤ →L[ℂ] Coeff 2 →L[ℂ] Coeff 2 := Coeff.holderProduct
  have hP := (P.flip.analyticAt (endpointH1SymbolFamily r hr1 n z)).comp
    (analyticAt_endpointH1SymbolFamily_wide r hr1 n hn z hz)
  exact SchurComplement.analyticAt_compCLM analyticAt_const
    (SchurComplement.analyticAt_compCLM analyticAt_const
      (SchurComplement.analyticAt_compCLM hP analyticAt_const))


theorem endpointH1ResolventFamily_toWiener_wide (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n) :
    (endpointH1ToWiener r hr1).comp (endpointH1ResolventFamily r hr1 n z) =
      endpointWienerResolventFamily r hr1 n z := by
  rw [endpointH1ResolventFamily_eq_wide r hr1 n hn z hz,
    endpointWienerResolventFamily_eq_wide r hr1 n hn z hz]


theorem endpointH1ResolventFamily_free_residual_wide (r : ℝ) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
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
    endpointHillH1Modes_coefficient, endpointH1ResolventFamily_coefficient_wide r hr1 n hn z hz]
  change z * (wideHillSymbol n z k * a.val k) -
    (freeHillValue k:ℂ) * (wideHillSymbol n z k * a.val k) =
      a.val k - ((if k = (n:ℤ) then a.val n else 0) +
        (if k = -(n:ℤ) then a.val (-(n:ℤ)) else 0))
  by_cases hkp : k = (n:ℤ)
  · subst k
    simp [wideHillSymbol, show (n:ℤ) ≠ -(n:ℤ) by omega]
  by_cases hkm : k = -(n:ℤ)
  · subst k
    simp [wideHillSymbol, show -(n:ℤ) ≠ (n:ℤ) by omega]
  have hk : k.natAbs ≠ n := fun he => ((hill_resonance_iff n k).mp he).elim hkp hkm
  simp only [if_neg hkp, if_neg hkm, zero_add, sub_zero, wideHillSymbol, if_neg hk]
  rw [← sub_mul, ← mul_assoc, mul_inv_cancel₀ (wideHill_denominator_ne_zero n hn z hz k hk), one_mul]


end NLS.KdV
