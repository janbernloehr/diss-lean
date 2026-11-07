import NLS.KdV.HillL2OffIndexOneSmoothing
import NLS.KdV.HillL2NativeDiagonalOneSmoothing

/-! The FULL original native complex map has one-smoothing Fourier
defect on L2 data. Actual core, on-index phase, action amplitude and
the COMPLETE infinite off-index phase are all restored. The remainder
is one global map, analytic in H3/2 near EVERY real L2 source, with
ALL original signed coefficients on ONE complex neighborhood. -/
noncomputable section
open Set Complex Filter Topology
namespace NLS.KdV

def hillL2NativeComplexFourierRemainder (q : Coeff 2) : WeightedCoeff (Weight.signedSobolev (3/2)) 2 :=
  hillL2NativeDiagonalFourierRemainder q + WeightedCoeff.signedSobolevInfinityProduct (1/2) (3/2)
    (by norm_num) (hillL2OffIndexExponentialRemainder q) (hillL2StrongNativeDiagonal q)

theorem analyticAt_hillL2NativeComplexFourierRemainder (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    AnalyticAt ℂ hillL2NativeComplexFourierRemainder q := by
  have hp : AnalyticAt ℂ (fun r : Coeff 2 => WeightedCoeff.signedSobolevInfinityProduct (1/2) (3/2)
      (by norm_num) (hillL2OffIndexExponentialRemainder r) (hillL2StrongNativeDiagonal r)) q :=
    (WeightedCoeff.analyticAt_signedSobolevInfinityProduct (1/2) (3/2) (by norm_num) _).comp
      (f := fun r : Coeff 2 => (hillL2OffIndexExponentialRemainder r,hillL2StrongNativeDiagonal r))
        ((analyticAt_hillL2OffIndexExponentialRemainder q hr).prod (analyticAt_hillL2StrongNativeDiagonal q hr))
  exact (analyticAt_hillL2NativeDiagonalFourierRemainder q hr).add hp

private theorem full_remainder_raw (q : Coeff 2) (k : ℤ)
    (hd : (hillL2NativeDiagonalFourierRemainder q).val k =
      (hillHminusNativeDiagonalMap (periodOneL2Inclusion q)).val k-WeightedCoeff.halfFourierSymbol k*q k)
    (hs : (hillL2StrongNativeDiagonal q).val k = (hillHminusNativeDiagonalMap (periodOneL2Inclusion q)).val k)
    (he : (hillL2OffIndexExponentialRemainder q).val k =
      Complex.exp (hillHminusSignedOffIndexExponent (periodOneL2Inclusion q) k)-1) :
    (hillL2NativeComplexFourierRemainder q).val k =
      (hillHminusNativeComplexMap (periodOneL2Inclusion q)).val k-WeightedCoeff.halfFourierSymbol k*q k := by
  have hc : (hillHminusNativeComplexMap (periodOneL2Inclusion q)).val k =
      Complex.exp (hillHminusSignedOffIndexExponent (periodOneL2Inclusion q) k)*
        (hillHminusNativeDiagonalMap (periodOneL2Inclusion q)).val k := by
    rw [hillHminusNativeComplexMap_from_diagonal,WeightedCoeff.exponentialSymbolEquiv_apply]
  simp only [hillL2NativeComplexFourierRemainder,WeightedCoeff.add_val,
    WeightedCoeff.signedSobolevInfinityProduct_apply,hd,hs,he,hc]
  ring

theorem eventually_hillL2NativeComplexFourierRemainder_apply (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∀ᶠ r in 𝓝 q, ∀ k : ℤ, (hillL2NativeComplexFourierRemainder r).val k =
      (hillHminusNativeComplexMap (periodOneL2Inclusion r)).val k-WeightedCoeff.halfFourierSymbol k*r k :=
  ((eventually_hillL2NativeDiagonalFourierRemainder_apply q hr).and
    ((eventually_hillL2StrongNativeDiagonal_apply q hr).and
      (eventually_hillL2OffIndexExponentialRemainder_apply q hr))).mono
        (fun r h k => full_remainder_raw r k (h.1 k) (h.2.1 k) (h.2.2 k))

theorem hillL2NativeComplexFourierRemainder_apply (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) (k : ℤ) :
    (hillL2NativeComplexFourierRemainder q).val k =
      (hillHminusNativeComplexMap (periodOneL2Inclusion q)).val k-WeightedCoeff.halfFourierSymbol k*q k :=
  (eventually_hillL2NativeComplexFourierRemainder_apply q hr).self_of_nhds k

end NLS.KdV
