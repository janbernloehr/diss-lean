import NLS.SequenceSpaces.PhysicalPositiveCompletionExponent
import NLS.SequenceSpaces.Multiplier

/-! # Bounded positive multipliers on the original real weighted lp spaces

Only positive coefficients enter the diagonal inverse identity. Physical
Fourier reality supplies every negative coefficient, and zero mean fixes zero.
-/
noncomputable section
set_option autoImplicit false
open Complex
open scoped ENNReal
namespace NLS

theorem physicalRealMeanZeroWeightedExponent_ext_positive
    {w : Weight} {p : ℝ≥0∞} [Fact (1≤p)]
    {a b : physicalRealMeanZeroWeightedExponent w p}
    (h : ∀ n : ℤ, 0<n → a.val.val n=b.val.val n) : a=b := by
  apply Subtype.ext
  apply Subtype.ext
  funext n
  rcases lt_trichotomy 0 n with hn|hn|hn
  · exact h n hn
  · subst n
    exact a.property.2.trans b.property.2.symm
  · have he := h (-n) (by omega)
    have ha := a.property.1 (-n)
    have hb := b.property.1 (-n)
    simpa only [neg_neg] using ha.trans ((congrArg (starRingEnd ℂ) he).trans hb.symm)

namespace WeightedCoeff
variable (w v : Weight) (p : ℝ≥0∞) [Fact (1≤p)]

def physicalPositiveMultiplier (hv : ∀ n : ℤ, v (-n)=v n) (m : Coeff ⊤) :
    physicalRealMeanZeroWeightedExponent w p →L[ℝ]
      physicalRealMeanZeroWeightedExponent v p :=
  (physicalPositiveRealLift v p hv).comp
    (((Coeff.multiplierCLM (p := p) m).restrictScalars ℝ).comp
      (((weightIsometry w p).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
        (physicalRealMeanZeroWeightedExponent w p).subtypeL))

theorem physicalPositiveMultiplier_apply_positive
    (hv : ∀ n : ℤ, v (-n)=v n) (m : Coeff ⊤)
    (a : physicalRealMeanZeroWeightedExponent w p) (n : ℤ) (hn : 0<n) :
    (physicalPositiveMultiplier w v p hv m a).val.val n=
      m n*((w n : ℂ)*a.val.val n)/(v n : ℂ) := by
  change (physicalPositiveRealLift v p hv
    (Coeff.multiplierCLM m ((weightIsometry w p) a.val))).val.val n=_
  rw [physicalPositiveRealLift_apply]
  simp only [hn,show ¬0< -n by omega,↓reduceIte,map_zero,add_zero,
    Coeff.multiplierCLM_apply,Coeff.multiplier_apply]
  rfl

def physicalPositiveMultiplierEquiv
    (hw : ∀ n : ℤ, w (-n)=w n) (hv : ∀ n : ℤ, v (-n)=v n)
    (m r : Coeff ⊤) (hmr : ∀ n : ℤ, 0<n → m n*r n=1) :
    physicalRealMeanZeroWeightedExponent w p ≃L[ℝ]
      physicalRealMeanZeroWeightedExponent v p :=
  ContinuousLinearEquiv.equivOfInverse (physicalPositiveMultiplier w v p hv m)
    (physicalPositiveMultiplier v w p hw r)
    (by
      intro a
      apply physicalRealMeanZeroWeightedExponent_ext_positive
      intro n hn
      rw [physicalPositiveMultiplier_apply_positive v w p hw r _ n hn,
        physicalPositiveMultiplier_apply_positive w v p hv m _ n hn]
      have hm := hmr n hn
      have hw0 := w.complex_ne_zero n
      have hv0 := v.complex_ne_zero n
      field_simp
      linear_combination a.val.val n * hm)
    (by
      intro a
      apply physicalRealMeanZeroWeightedExponent_ext_positive
      intro n hn
      rw [physicalPositiveMultiplier_apply_positive w v p hv m _ n hn,
        physicalPositiveMultiplier_apply_positive v w p hw r _ n hn]
      have hm := hmr n hn
      have hw0 := w.complex_ne_zero n
      have hv0 := v.complex_ne_zero n
      field_simp
      linear_combination a.val.val n * hm)

end WeightedCoeff
end NLS
