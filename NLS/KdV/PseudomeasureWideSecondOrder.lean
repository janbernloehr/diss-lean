import NLS.KdV.PseudomeasureWideH1Analytic

/-! The complementary inverse gains exactly two endpoint Sobolev orders.
The stronger infinity-space realization is the same original physical H1
distribution, rather than a different formal coefficient sequence. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

theorem endpointSecondOrder_weight_identity (r : ℝ) (k : ℤ) :
    Weight.sobolev (2-r) k=Weight.sobolev 2 k*SpectralWeight.one.negativeSobolev r k := by
  rw [SpectralWeight.negativeSobolev_eq_product,SpectralWeight.one_apply,one_mul,
    ← Weight.sobolev_add,show (2:ℝ)+ -r=2-r by ring]

def endpointSecondOrderResolventFamily (r : ℝ) (n : ℕ) (z : ℂ) :
    WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ →L[ℂ]
      WeightedCoeff (Weight.sobolev (2-r)) ⊤ :=
  (WeightedCoeff.weightIsometry (Weight.sobolev (2-r)) ⊤).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((Coeff.multiplierCLM (hillOrderTwoSymbolFamily n z)).comp
      (WeightedCoeff.weightIsometry (SpectralWeight.one.negativeSobolev r) ⊤).toContinuousLinearEquiv.toContinuousLinearMap)

theorem endpointSecondOrderResolventFamily_apply_wide (r : ℝ) (n : ℕ) (hn : 2≤n)
    (z : ℂ) (hz : z ∈ wideHillStrip n)
    (a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (k : ℤ) :
    (endpointSecondOrderResolventFamily r n z a).val k=wideHillSymbol n z k*a.val k := by
  change (hillOrderTwoSymbolFamily n z k*((SpectralWeight.one.negativeSobolev r k:ℂ)*a.val k))/
    (Weight.sobolev (2-r) k:ℂ)=_
  rw [hillOrderTwoSymbolFamily_eq_wide_symbol n hn z hz k]
  have he : (Weight.sobolev (2-r) k:ℂ)=
      (Weight.sobolev 2 k:ℂ)*(SpectralWeight.one.negativeSobolev r k:ℂ) := by
    exact_mod_cast endpointSecondOrder_weight_identity r k
  have hh : (Weight.sobolev (2-r) k:ℂ)≠0 := (Weight.sobolev (2-r)).complex_ne_zero k
  apply (div_eq_iff hh).mpr
  rw [he]
  ring

theorem endpointH1ResolventFamily_secondOrder_wide (r : ℝ) (hr1 : r<1/2)
    (n : ℕ) (hn : 2≤n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) :
    ∃ v : FourierLebesgueSpace (2:ℝ) (2-r) ⊤,
      v.val=(endpointH1ResolventFamily r hr1 n z a).val := by
  let b := endpointSecondOrderResolventFamily r n z a
  refine ⟨(sobolevCoefficients (L:=2) (2-r) ⊤).symm b,?_⟩
  apply Distribution.ext_coefficients
  intro k
  have hb := congrArg (fun x : WeightedCoeff (Weight.sobolev (2-r)) ⊤ => x.val k)
    ((sobolevCoefficients (L:=2) (2-r) ⊤).apply_symm_apply b)
  rw [sobolevCoefficients_apply] at hb
  exact hb.trans ((endpointSecondOrderResolventFamily_apply_wide r n hn z hz a k).trans
    (endpointH1ResolventFamily_coefficient_wide r hr1 n hn z hz a k).symm)

end NLS.KdV
