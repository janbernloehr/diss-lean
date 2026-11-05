import NLS.Articles.KdVPseudomeasures.OriginalHillGlobalNativeInverse
import NLS.SequenceSpaces.FourierRealZeroTruncation

/-! Actual global finite-gap approximations in the original rough norm.
Symmetric canonical truncations preserve equality of all action products. -/
noncomputable section
open Set Filter Topology NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

def hillRoughFiniteGapApproximation (q : HillRealMeanZeroSource) (N : ℕ) : HillRealMeanZeroSource :=
  hillNativeHomeomorph.symm (fourierRealZeroTruncate (Weight.signedSobolev (-1/2)) N (hillRealSignedMap q))

theorem hillRoughFiniteGapApproximation_native (q : HillRealMeanZeroSource) (N : ℕ) :
    hillRealSignedMap (hillRoughFiniteGapApproximation q N)=
      fourierRealZeroTruncate (Weight.signedSobolev (-1/2)) N (hillRealSignedMap q) :=
  hillNativeHomeomorph.apply_symm_apply _

theorem hillRoughFiniteGapApproximation_tendsto (q : HillRealMeanZeroSource) :
    Tendsto (hillRoughFiniteGapApproximation q) atTop (𝓝 q) := by
  have h := hillNativeHomeomorph.symm.continuous.continuousAt.tendsto.comp
    (tendsto_fourierRealZeroTruncate (p := 2) (by simp) (Weight.signedSobolev (-1/2)) (hillRealSignedMap q))
  simpa only [hillRoughFiniteGapApproximation,← hillNativeHomeomorph_apply,
    hillNativeHomeomorph.symm_apply_apply,Function.comp_def] using! h

theorem hillRoughFiniteGapApproximation_mem (q : HillRealMeanZeroSource) (N : ℕ) :
    hillRoughFiniteGapApproximation q N ∈ hillRealFiniteGapLocus :=
  hillRealFiniteGap_of_map_eq_truncate _ _ N (hillRoughFiniteGapApproximation_native q N)

theorem hillRoughFiniteGapApproximation_products (p q : HillRealMeanZeroSource)
    (hp : ∀ n : ℕ+, (hillRealSignedMap p).val.val.val (n:ℤ)*(hillRealSignedMap p).val.val.val (-(n:ℤ))=
      (hillRealSignedMap q).val.val.val (n:ℤ)*(hillRealSignedMap q).val.val.val (-(n:ℤ))) (N : ℕ) :
    ∀ n : ℕ+, (hillRealSignedMap (hillRoughFiniteGapApproximation p N)).val.val.val (n:ℤ)*
        (hillRealSignedMap (hillRoughFiniteGapApproximation p N)).val.val.val (-(n:ℤ))=
      (hillRealSignedMap (hillRoughFiniteGapApproximation q N)).val.val.val (n:ℤ)*
        (hillRealSignedMap (hillRoughFiniteGapApproximation q N)).val.val.val (-(n:ℤ)) := by
  intro n
  simp only [hillRoughFiniteGapApproximation_native,fourierRealZeroTruncate_apply,Int.natAbs_neg]
  by_cases hn : (n:ℤ).natAbs < N
  · simp only [if_pos hn]
    exact hp n
  · simp only [if_neg hn,zero_mul]

end NLS.Articles.KdVPseudomeasures
