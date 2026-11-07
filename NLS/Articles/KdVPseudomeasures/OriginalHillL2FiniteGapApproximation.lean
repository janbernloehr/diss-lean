import NLS.Articles.KdVPseudomeasures.OriginalHillL2NativeInverse
import NLS.KdV.HillNativeFiniteGap
import NLS.Topology.DensePreimageApproximation

/-! ACTUAL finite-gap approximation in the TRUE original L2 Banach norm,
by symmetric native positive-half truncation and the actual analytic L2
local inverse. No global native inverse or imported NLS density theorem. -/
noncomputable section
open Set Filter Topology NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem hillL2FiniteGap_approximation (u : HillRealL2BanachSource) :
    ∃ G : HillRealSignedHalfTarget → HillRealL2BanachSource,
      AnalyticAt ℝ G (hillL2NativeMap u) ∧ G (hillL2NativeMap u)=u ∧
      Tendsto (fun N : ℕ => G (WeightedCoeff.fourierRealZeroTruncate
        (Weight.signedSobolev (1/2)) N (hillL2NativeMap u))) atTop (𝓝 u) ∧
      ∀ᶠ N : ℕ in atTop,
        hillL2SourceInclusion (G (WeightedCoeff.fourierRealZeroTruncate
          (Weight.signedSobolev (1/2)) N (hillL2NativeMap u))) ∈ hillRealFiniteGapLocus ∧
        hillL2NativeMap (G (WeightedCoeff.fourierRealZeroTruncate
          (Weight.signedSobolev (1/2)) N (hillL2NativeMap u)))=
            WeightedCoeff.fourierRealZeroTruncate (Weight.signedSobolev (1/2)) N (hillL2NativeMap u) := by
  obtain ⟨G,hG,hGu,_,hright⟩ := exists_hillL2NativeMap_localInverse u
  have ht := WeightedCoeff.tendsto_fourierRealZeroTruncate (p:=2) (by simp)
    (Weight.signedSobolev (1/2)) (hillL2NativeMap u)
  have hGt := hG.continuousAt.tendsto.comp ht
  rw [hGu] at hGt
  refine ⟨G,hG,hGu,hGt,?_⟩
  filter_upwards [ht.eventually hright] with N hN
  refine ⟨⟨N,fun n hn => ?_⟩,hN⟩
  apply (hillRealSignedMap_positive_eq_zero_iff_gapSquare _ n).mp
  rw [← hillL2NativeMap_apply,hN,WeightedCoeff.fourierRealZeroTruncate_apply,
    Int.natAbs_natCast,if_neg (by omega)]

private theorem exists_hillL2FiniteGap_sequence (u : HillRealL2BanachSource) :
    ∃ v : ℕ → HillRealL2BanachSource, Tendsto v atTop (𝓝 u) ∧
      ∀ᶠ N : ℕ in atTop, hillL2SourceInclusion (v N) ∈ hillRealFiniteGapLocus := by
  obtain ⟨G,_,_,hGt,hfinite⟩ := hillL2FiniteGap_approximation u
  exact ⟨fun N => G (WeightedCoeff.fourierRealZeroTruncate (Weight.signedSobolev (1/2)) N
    (hillL2NativeMap u)),hGt,hfinite.mono fun _ h => h.1⟩

/-- Actual finite-gap sources are dense in the TRUE original L2 topology,
not merely in their native Hminus-one subspace topology. -/
theorem dense_hillL2FiniteGapLocus : Dense (hillL2SourceInclusion ⁻¹' hillRealFiniteGapLocus) :=
  NLS.Topology.dense_preimage_of_approximating_sequences hillL2SourceInclusion hillRealFiniteGapLocus
    exists_hillL2FiniteGap_sequence

end NLS.Articles.KdVPseudomeasures
