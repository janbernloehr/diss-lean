import NLS.Articles.KdVPseudomeasures.OriginalHillIntegerFiniteGapApproximation
import NLS.Articles.KdVPseudomeasures.OriginalHillNativeActionFibers

/-! Symmetric truncation of actual canonical outputs preserves equality
of ALL original action products, hence the FULL original spectrum.
The corresponding genuine finite-gap sources converge in the strong norms. -/
noncomputable section
open NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem hillIntegerFiniteGapApproximation_native_apply (s : ℕ)
    (q : RealSignedHilbert (signedStepOrder 0 s)) (N : ℕ) (k : ℤ) :
    (hillRealSignedMap (hillIntegerSourceInclusion s (hillIntegerFiniteGapApproximation s q N))).val.val.val k=
      if k.natAbs < N then ((hillIntegerSobolevEquiv s).equiv q).val.val.val k else 0 := by
  rw [hillIntegerFiniteGapApproximation_native,hillIntegerTargetInclusion_apply,fourierRealZeroTruncate_apply]

theorem hillIntegerFiniteGapApproximation_isospectral_of_products (s : ℕ)
    (p q : RealSignedHilbert (signedStepOrder 0 s))
    (hp : ∀ n : ℕ+, ((hillIntegerSobolevEquiv s).equiv p).val.val.val (n:ℤ)*
        ((hillIntegerSobolevEquiv s).equiv p).val.val.val (-(n:ℤ))=
      ((hillIntegerSobolevEquiv s).equiv q).val.val.val (n:ℤ)*
        ((hillIntegerSobolevEquiv s).equiv q).val.val.val (-(n:ℤ))) (N : ℕ) :
    originalHillPotentialOfRealSource (hillIntegerSourceInclusion s (hillIntegerFiniteGapApproximation s p N)) ∈
      originalIsospectralSet (originalHillPotentialOfRealSource
        (hillIntegerSourceInclusion s (hillIntegerFiniteGapApproximation s q N))) := by
  apply originalHillPotentialOfRealSource_isospectral_of_native_products
  intro n
  simp only [hillIntegerFiniteGapApproximation_native_apply,Int.natAbs_neg]
  by_cases hn : (n:ℤ).natAbs < N
  · simp only [if_pos hn]
    exact hp n
  · simp only [if_neg hn,zero_mul]

end NLS.Articles.KdVPseudomeasures
