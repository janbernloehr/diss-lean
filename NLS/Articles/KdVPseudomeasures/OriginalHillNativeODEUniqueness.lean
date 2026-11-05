import NLS.Articles.KdVPseudomeasures.OriginalHillRoughCanonicalFlow
import NLS.KdV.HillNativeRealCoordinateValue
import NLS.ComplexAnalysis.ScalarExponentialUniqueness

/-! Uniqueness for the genuine actual state-dependent canonical ODE.
Action conservation is DERIVED from the full signed ODE, then actual
frequency invariance reduces it to the scalar constant-rate equation.
No isospectrality or constancy of frequencies is assumed. -/
noncomputable section
open Set Complex NLS.KdV NLS.WeightedCoeff NLS.LpSequence
namespace NLS.Articles.KdVPseudomeasures

theorem hasDerivAt_hillNativeProduct_zero_of_nativeODE
    (γ : ℝ → HillRealMeanZeroSource)
    (hγ : ∀ t k, HasDerivAt (fun s : ℝ => hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (γ s)))
      (I*(oddPositiveFrequency (fun n => hillRoughKdVFrequency n (γ t)) k:ℂ)*
        hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (γ t))) t)
    (n : ℕ+) (t : ℝ) :
    HasDerivAt (fun s : ℝ => hillHminusNativeCoordinate (n:ℤ) (hillRealMeanZeroInclusion (γ s))*
      hillHminusNativeCoordinate (-(n:ℤ)) (hillRealMeanZeroInclusion (γ s))) 0 t := by
  have hd := (hγ t (n:ℤ)).mul (hγ t (-(n:ℤ)))
  rw [oddPositiveFrequency_neg,Complex.ofReal_neg] at hd
  convert! hd using 1
  ring

theorem hillNativeProducts_constant_of_nativeODE
    (γ : ℝ → HillRealMeanZeroSource)
    (hγ : ∀ t k, HasDerivAt (fun s : ℝ => hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (γ s)))
      (I*(oddPositiveFrequency (fun n => hillRoughKdVFrequency n (γ t)) k:ℂ)*
        hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (γ t))) t)
    (n : ℕ+) (t : ℝ) :
    (hillRealSignedMap (γ t)).val.val.val (n:ℤ)*(hillRealSignedMap (γ t)).val.val.val (-(n:ℤ))=
      (hillRealSignedMap (γ 0)).val.val.val (n:ℤ)*(hillRealSignedMap (γ 0)).val.val.val (-(n:ℤ)) := by
  simp only [hillRealSignedMap_apply_nativeCoordinate]
  exact isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
    (fun s _ => (hasDerivAt_hillNativeProduct_zero_of_nativeODE γ hγ n s).differentiableAt.differentiableWithinAt)
    (fun s _ => (hasDerivAt_hillNativeProduct_zero_of_nativeODE γ hγ n s).deriv) (mem_univ t) (mem_univ 0)

theorem hillRoughKdVFrequency_constant_of_nativeODE
    (γ : ℝ → HillRealMeanZeroSource)
    (hγ : ∀ t k, HasDerivAt (fun s : ℝ => hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (γ s)))
      (I*(oddPositiveFrequency (fun n => hillRoughKdVFrequency n (γ t)) k:ℂ)*
        hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (γ t))) t)
    (n : ℕ+) (t : ℝ) :
    hillRoughKdVFrequency n (γ t)=hillRoughKdVFrequency n (γ 0) :=
  hillRoughKdVFrequency_eq_of_native_products n (γ t) (γ 0)
    (fun m => hillNativeProducts_constant_of_nativeODE γ hγ m t)

theorem hillNativeCoordinate_exp_of_nativeODE
    (γ : ℝ → HillRealMeanZeroSource)
    (hγ : ∀ t k, HasDerivAt (fun s : ℝ => hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (γ s)))
      (I*(oddPositiveFrequency (fun n => hillRoughKdVFrequency n (γ t)) k:ℂ)*
        hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (γ t))) t)
    (k : ℤ) (t : ℝ) :
    hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (γ t))=
      exp ((I*(oddPositiveFrequency (fun n => hillRoughKdVFrequency n (γ 0)) k:ℂ))*(t:ℂ))*
        hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (γ 0)) := by
  refine NLS.ComplexAnalysis.eq_exp_mul_of_hasDerivAt
    (I*(oddPositiveFrequency (fun n => hillRoughKdVFrequency n (γ 0)) k:ℂ))
    (fun s : ℝ => hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (γ s))) ?_ t
  intro s
  have hd := hγ s k
  have hf : (fun n => hillRoughKdVFrequency n (γ s))=(fun n => hillRoughKdVFrequency n (γ 0)) :=
    funext (fun n => hillRoughKdVFrequency_constant_of_nativeODE γ hγ n s)
  rw [hf] at hd
  exact hd

theorem hillRealCurve_eq_canonicalFlow_of_nativeODE
    (γ : ℝ → HillRealMeanZeroSource)
    (hγ : ∀ t k, HasDerivAt (fun s : ℝ => hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (γ s)))
      (I*(oddPositiveFrequency (fun n => hillRoughKdVFrequency n (γ t)) k:ℂ)*
        hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (γ t))) t)
    (t : ℝ) : γ t=hillRoughCanonicalKdVFlow (γ 0) t := by
  apply injective_hillRealSignedMap
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [hillRoughCanonicalKdVFlow_native,fourierRealZeroPhaseFlow_apply,
    hillRealSignedMap_apply_nativeCoordinate,hillRealSignedMap_apply_nativeCoordinate,
    hillNativeCoordinate_exp_of_nativeODE γ hγ k t]
  congr 2
  push_cast
  ring

end NLS.Articles.KdVPseudomeasures
