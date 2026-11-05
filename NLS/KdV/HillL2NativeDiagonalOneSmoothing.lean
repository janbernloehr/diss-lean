import NLS.KdV.HillL2AmplitudeOneSmoothing
import NLS.KdV.HillL2IntrinsicFourierRemainder

/-! Restoring the ACTUAL global normalized action amplitude gives
the original native diagonal map. Its Fourier remainder is analytic
in native H3/2 near EVERY real L2 source, with all coefficients on
ONE complex neighborhood. The off-index phase remains separate. -/
noncomputable section
open Set Complex Filter Topology
namespace NLS.KdV

def hillL2NativeDiagonalFourierRemainder (q : Coeff 2) : WeightedCoeff (Weight.signedSobolev (3/2)) 2 :=
  hillL2IntrinsicFourierRemainder q + WeightedCoeff.signedSobolevInfinityProduct (1/2) (3/2)
    (by norm_num) (hillL2AmplitudeSobolevRemainder q) (hillL2StrongIntrinsicDiagonal q)

theorem analyticAt_hillL2NativeDiagonalFourierRemainder (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    AnalyticAt ℂ hillL2NativeDiagonalFourierRemainder q := by
  have hp : AnalyticAt ℂ (fun r : Coeff 2 => WeightedCoeff.signedSobolevInfinityProduct (1/2) (3/2)
      (by norm_num) (hillL2AmplitudeSobolevRemainder r) (hillL2StrongIntrinsicDiagonal r)) q :=
    (WeightedCoeff.analyticAt_signedSobolevInfinityProduct (1/2) (3/2) (by norm_num) _).comp
      (f := fun r : Coeff 2 => (hillL2AmplitudeSobolevRemainder r,hillL2StrongIntrinsicDiagonal r))
        ((analyticAt_hillL2AmplitudeSobolevRemainder q hr).prod (analyticAt_hillL2StrongIntrinsicDiagonal q hr))
  exact (analyticAt_hillL2IntrinsicFourierRemainder q hr).add hp

private theorem diagonal_remainder_raw (q : Coeff 2) (k : ℤ)
    (hq : periodOneL2Inclusion q ∈ hillHminusActionAngleNativeDomain)
    (hi : (hillL2IntrinsicFourierRemainder q).val k =
      (hillHminusIntrinsicDiagonalMap (periodOneL2Inclusion q)).val k-WeightedCoeff.halfFourierSymbol k*q k)
    (hs : (hillL2StrongIntrinsicDiagonal q).val k = (hillHminusIntrinsicDiagonalMap (periodOneL2Inclusion q)).val k)
    (ha : (hillL2AmplitudeSobolevRemainder q).val k = hillHminusNormalizedAmplitudeSymbol (periodOneL2Inclusion q) k-1) :
    (hillL2NativeDiagonalFourierRemainder q).val k =
      (hillHminusNativeDiagonalMap (periodOneL2Inclusion q)).val k-WeightedCoeff.halfFourierSymbol k*q k := by
  have hd : (hillHminusNativeDiagonalMap (periodOneL2Inclusion q)).val k =
      hillHminusNormalizedAmplitudeSymbol (periodOneL2Inclusion q) k*
        (hillHminusIntrinsicDiagonalMap (periodOneL2Inclusion q)).val k := by
    rw [hillHminusNativeDiagonalMap_from_intrinsic _ hq]
    rfl
  simp only [hillL2NativeDiagonalFourierRemainder,WeightedCoeff.add_val,
    WeightedCoeff.signedSobolevInfinityProduct_apply,hi,hs,ha,hd]
  ring

theorem eventually_hillL2NativeDiagonalFourierRemainder_apply (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∀ᶠ r in 𝓝 q, ∀ k : ℤ, (hillL2NativeDiagonalFourierRemainder r).val k =
      (hillHminusNativeDiagonalMap (periodOneL2Inclusion r)).val k-WeightedCoeff.halfFourierSymbol k*r k := by
  have hnative : ∀ᶠ r in 𝓝 q, periodOneL2Inclusion r ∈ hillHminusActionAngleNativeDomain :=
    periodOneL2Inclusion.continuous.continuousAt.tendsto.eventually
      (isOpen_hillHminusActionAngleNativeDomain.mem_nhds (real_mem_hillHminusActionAngleNativeDomain _ hr))
  exact (hnative.and ((eventually_hillL2IntrinsicFourierRemainder_apply q hr).and
    ((eventually_hillL2StrongIntrinsicDiagonal_apply q hr).and
      (eventually_hillL2AmplitudeSobolevRemainder_apply q hr)))).mono (fun r h k =>
        diagonal_remainder_raw r k h.1 (h.2.1 k) (h.2.2.1 k) (h.2.2.2 k))

theorem hillL2NativeDiagonalFourierRemainder_apply (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) (k : ℤ) :
    (hillL2NativeDiagonalFourierRemainder q).val k =
      (hillHminusNativeDiagonalMap (periodOneL2Inclusion q)).val k-WeightedCoeff.halfFourierSymbol k*q k :=
  (eventually_hillL2NativeDiagonalFourierRemainder_apply q hr).self_of_nhds k

def hillL2StrongNativeDiagonal (q : Coeff 2) : WeightedCoeff (Weight.signedSobolev (1/2)) 2 :=
  WeightedCoeff.l2FreeHalfFourier q +
    WeightedCoeff.signedOrderInclusion (1/2) (3/2) (by norm_num) 2 (hillL2NativeDiagonalFourierRemainder q)

theorem analyticAt_hillL2StrongNativeDiagonal (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    AnalyticAt ℂ hillL2StrongNativeDiagonal q :=
  (WeightedCoeff.l2FreeHalfFourier.analyticAt q).add
    (((WeightedCoeff.signedOrderInclusion (1/2) (3/2) (by norm_num) 2).analyticAt _).comp
      (analyticAt_hillL2NativeDiagonalFourierRemainder q hr))

theorem eventually_hillL2StrongNativeDiagonal_apply (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∀ᶠ r in 𝓝 q, ∀ k : ℤ, (hillL2StrongNativeDiagonal r).val k =
      (hillHminusNativeDiagonalMap (periodOneL2Inclusion r)).val k := by
  exact (eventually_hillL2NativeDiagonalFourierRemainder_apply q hr).mono (fun r h k => by
    simp only [hillL2StrongNativeDiagonal,WeightedCoeff.add_val,WeightedCoeff.l2FreeHalfFourier_apply,
      WeightedCoeff.signedOrderInclusion_apply,h k]
    ring)

theorem hillL2StrongNativeDiagonal_apply (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) (k : ℤ) :
    (hillL2StrongNativeDiagonal q).val k = (hillHminusNativeDiagonalMap (periodOneL2Inclusion q)).val k :=
  (eventually_hillL2StrongNativeDiagonal_apply q hr).self_of_nhds k

end NLS.KdV
