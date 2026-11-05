import NLS.SequenceSpaces.WeightedInsertion
import NLS.SequenceSpaces.PeriodDoubling

/-! Restriction to the even modes in EVERY Banach sequence exponent,
with the exact pulled-back weight. It inverts zero insertion on its
entire even-supported range, including exponent one and infinity. -/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

def periodHalveCLM : Coeff p →L[ℂ] Coeff p :=
  LinearMap.mkContinuous
    { toFun := periodHalve
      map_add' := fun a b => by ext n; rfl
      map_smul' := fun c a => by ext n; rfl }
    1 (fun a => by
      change ‖periodHalve a‖ ≤ 1*‖a‖
      simpa only [one_mul] using norm_periodHalve_le a)

theorem periodHalveCLM_apply (a : Coeff p) (n : ℤ) : periodHalveCLM p a n = a (2*n) := rfl

end NLS.Coeff
namespace NLS.WeightedCoeff
variable (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)]

def periodHalveCLM : WeightedCoeff w p →L[ℂ] WeightedCoeff (w.pullback (Coeff.parityEmbedding 0)) p :=
  (weightIsometry (w.pullback (Coeff.parityEmbedding 0)) p).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((Coeff.periodHalveCLM p).comp (weightIsometry w p).toContinuousLinearEquiv.toContinuousLinearMap)

theorem periodHalveCLM_apply (a : WeightedCoeff w p) (n : ℤ) :
    (periodHalveCLM w p a).val n = a.val (2*n) := by
  change ((w (2*n):ℂ)*a.val (2*n))/(w ((Coeff.parityEmbedding 0) n):ℂ) = _
  simp only [Coeff.parityEmbedding_apply,add_zero]
  exact mul_div_cancel_left₀ _ (w.complex_ne_zero _)

theorem norm_periodHalveCLM_le (a : WeightedCoeff w p) : ‖periodHalveCLM w p a‖ ≤ ‖a‖ := by
  change ‖(weightIsometry (w.pullback (Coeff.parityEmbedding 0)) p).symm
    (Coeff.periodHalve (weightIsometry w p a))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (Coeff.norm_periodHalve_le _).trans_eq ((weightIsometry w p).norm_map a)

theorem periodHalveCLM_insertIsometry (a : WeightedCoeff (w.pullback (Coeff.parityEmbedding 0)) p) :
    periodHalveCLM w p (insertIsometry w (Coeff.parityEmbedding 0) a) = a := by
  apply Subtype.ext
  funext n
  rw [periodHalveCLM_apply]
  simpa only [Coeff.parityEmbedding_apply,add_zero] using insertIsometry_image w (Coeff.parityEmbedding 0) a n

theorem insertIsometry_periodHalveCLM (a : WeightedCoeff w p) (ha : ∀ n : ℤ, a.val (2*n+1)=0) :
    insertIsometry w (Coeff.parityEmbedding 0) (periodHalveCLM w p a) = a := by
  apply Subtype.ext
  funext k
  by_cases hk : k % 2 = 0
  · have he : k = 2*(k/2) := by omega
    rw [he]
    have h := insertIsometry_image w (Coeff.parityEmbedding 0) (periodHalveCLM w p a) (k/2)
    simp only [Coeff.parityEmbedding_apply,add_zero] at h
    exact h.trans (periodHalveCLM_apply w p a (k/2))
  · have he : k = 2*(k/2)+1 := by omega
    rw [he,ha]
    apply insertIsometry_outside
    rintro ⟨n,hn⟩
    change 2*n+0 = 2*(k/2)+1 at hn
    omega

end NLS.WeightedCoeff
