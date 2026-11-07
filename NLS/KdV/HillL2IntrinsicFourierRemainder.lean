import NLS.KdV.HillL2IntrinsicDiagonalOneSmoothing

/-! A single intrinsic Fourier remainder, independent of every local
patch choice. At EVERY real L2 source it is complex analytic in native
H3/2, with the ENTIRE original intrinsic-minus-free Fourier sequence
on one complex neighborhood. The intrinsic map itself is realized in H1/2. -/
noncomputable section
open Set Complex Filter Topology
namespace NLS.KdV

def hillL2IntrinsicFourierRemainder (q : Coeff 2) : WeightedCoeff (Weight.signedSobolev (3/2)) 2 :=
  WeightedCoeff.ofFunctionOrZero _ 2 (fun k =>
    (hillHminusIntrinsicDiagonalMap (periodOneL2Inclusion q)).val k - WeightedCoeff.halfFourierSymbol k * q k)

private theorem intrinsic_global_eq_local (P : HillProductEquationPatch) (r : Coeff 2)
    (h : ∀ k : ℤ, (P.l2IntrinsicDiagonalFourierRemainder r).val k =
      (hillHminusIntrinsicDiagonalMap (periodOneL2Inclusion r)).val k - WeightedCoeff.halfFourierSymbol k * r k) :
    hillL2IntrinsicFourierRemainder r = P.l2IntrinsicDiagonalFourierRemainder r :=
  WeightedCoeff.ofFunctionOrZero_eq_of_coordinates _ _ _ h

theorem analyticAt_hillL2IntrinsicFourierRemainder (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    AnalyticAt ℂ hillL2IntrinsicFourierRemainder q := by
  obtain ⟨P,U,hU,hqU,_,ha,hraw⟩ := exists_hillL2IntrinsicDiagonal_one_smoothing q hr
  have hm : ∀ᶠ r in 𝓝 q, r ∈ U := hU.mem_nhds hqU
  have he : ∀ᶠ r in 𝓝 q, P.l2IntrinsicDiagonalFourierRemainder r = hillL2IntrinsicFourierRemainder r :=
    hm.mono (fun r hrU => (intrinsic_global_eq_local P r (hraw r hrU)).symm)
  exact (ha q hqU).congr he

theorem eventually_hillL2IntrinsicFourierRemainder_apply (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∀ᶠ r in 𝓝 q, ∀ k : ℤ, (hillL2IntrinsicFourierRemainder r).val k =
      (hillHminusIntrinsicDiagonalMap (periodOneL2Inclusion r)).val k - WeightedCoeff.halfFourierSymbol k * r k := by
  obtain ⟨P,U,hU,hqU,_,_,hraw⟩ := exists_hillL2IntrinsicDiagonal_one_smoothing q hr
  have hm : ∀ᶠ r in 𝓝 q, r ∈ U := hU.mem_nhds hqU
  exact hm.mono (fun r hrU k =>
    (congrArg (fun a : WeightedCoeff (Weight.signedSobolev (3/2)) 2 => a.val k)
      (intrinsic_global_eq_local P r (hraw r hrU))).trans (hraw r hrU k))

theorem hillL2IntrinsicFourierRemainder_apply (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) (k : ℤ) :
    (hillL2IntrinsicFourierRemainder q).val k =
      (hillHminusIntrinsicDiagonalMap (periodOneL2Inclusion q)).val k - WeightedCoeff.halfFourierSymbol k * q k :=
  (eventually_hillL2IntrinsicFourierRemainder_apply q hr).self_of_nhds k

def hillL2StrongIntrinsicDiagonal (q : Coeff 2) : WeightedCoeff (Weight.signedSobolev (1/2)) 2 :=
  WeightedCoeff.l2FreeHalfFourier q +
    WeightedCoeff.signedOrderInclusion (1/2) (3/2) (by norm_num) 2 (hillL2IntrinsicFourierRemainder q)

theorem analyticAt_hillL2StrongIntrinsicDiagonal (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    AnalyticAt ℂ hillL2StrongIntrinsicDiagonal q :=
  (WeightedCoeff.l2FreeHalfFourier.analyticAt q).add
    (((WeightedCoeff.signedOrderInclusion (1/2) (3/2) (by norm_num) 2).analyticAt _).comp
      (analyticAt_hillL2IntrinsicFourierRemainder q hr))

theorem eventually_hillL2StrongIntrinsicDiagonal_apply (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∀ᶠ r in 𝓝 q, ∀ k : ℤ, (hillL2StrongIntrinsicDiagonal r).val k =
      (hillHminusIntrinsicDiagonalMap (periodOneL2Inclusion r)).val k := by
  exact (eventually_hillL2IntrinsicFourierRemainder_apply q hr).mono (fun r h k => by
    simp only [hillL2StrongIntrinsicDiagonal,WeightedCoeff.add_val,WeightedCoeff.l2FreeHalfFourier_apply,
      WeightedCoeff.signedOrderInclusion_apply,h k]
    ring)

theorem hillL2StrongIntrinsicDiagonal_apply (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) (k : ℤ) :
    (hillL2StrongIntrinsicDiagonal q).val k =
      (hillHminusIntrinsicDiagonalMap (periodOneL2Inclusion q)).val k :=
  (eventually_hillL2StrongIntrinsicDiagonal_apply q hr).self_of_nhds k

end NLS.KdV
