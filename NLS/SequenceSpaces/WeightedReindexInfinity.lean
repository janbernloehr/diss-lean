import NLS.SequenceSpaces.WeightedInsertion

/-! Arbitrary reindexing is contractive at infinity, with the exact
pullback weight. No injectivity or finite-exponent assumption is needed. -/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff

def reindexInfinity (f : ℤ → ℤ) (a : Coeff ⊤) : Coeff ⊤ :=
  ⟨fun n => a (f n),by
    apply memℓp_infty
    exact ⟨‖a‖,by rintro _ ⟨n,rfl⟩; exact lp.norm_apply_le_norm (by simp) a (f n)⟩⟩

theorem norm_reindexInfinity_le (f : ℤ → ℤ) (a : Coeff ⊤) : ‖reindexInfinity f a‖ ≤ ‖a‖ := by
  apply lp.norm_le_of_forall_le (norm_nonneg a)
  intro n
  exact lp.norm_apply_le_norm (by simp) a (f n)

def reindexInfinityCLM (f : ℤ → ℤ) : Coeff ⊤ →L[ℂ] Coeff ⊤ :=
  LinearMap.mkContinuous
    { toFun := reindexInfinity f
      map_add' := fun a b => by ext n; rfl
      map_smul' := fun c a => by ext n; rfl }
    1 (fun a => by
      change ‖reindexInfinity f a‖ ≤ 1*‖a‖
      simpa only [one_mul] using norm_reindexInfinity_le f a)

end NLS.Coeff
namespace NLS.WeightedCoeff

def reindexInfinityCLM (w : Weight) (f : ℤ → ℤ) :
    WeightedCoeff w ⊤ →L[ℂ] WeightedCoeff (w.pullback f) ⊤ :=
  (weightIsometry (w.pullback f) ⊤).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((Coeff.reindexInfinityCLM f).comp (weightIsometry w ⊤).toContinuousLinearEquiv.toContinuousLinearMap)

theorem reindexInfinityCLM_apply (w : Weight) (f : ℤ → ℤ) (a : WeightedCoeff w ⊤) (n : ℤ) :
    (reindexInfinityCLM w f a).val n=a.val (f n) := by
  change ((w (f n):ℂ)*a.val (f n))/(w (f n):ℂ)=_
  exact mul_div_cancel_left₀ _ (w.complex_ne_zero (f n))

theorem norm_reindexInfinityCLM_le (w : Weight) (f : ℤ → ℤ) (a : WeightedCoeff w ⊤) :
    ‖reindexInfinityCLM w f a‖ ≤ ‖a‖ := by
  change ‖(weightIsometry (w.pullback f) ⊤).symm (Coeff.reindexInfinity f (weightIsometry w ⊤ a))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (Coeff.norm_reindexInfinity_le f _).trans_eq ((weightIsometry w ⊤).norm_map a)

end NLS.WeightedCoeff
