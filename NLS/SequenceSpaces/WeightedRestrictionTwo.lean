import NLS.SequenceSpaces.WeightedInsertion

/-! Bounded coefficient restriction along an index embedding in weighted l2. -/
noncomputable section
open scoped ENNReal
namespace NLS
namespace Coeff

/-- Restrict a square-summable sequence along an arbitrary integer embedding. -/
def restrictTwo (e : ℤ ↪ ℤ) (a : Coeff 2) : Coeff 2 :=
  ⟨fun n => a (e n), by
    apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
    exact ((lp.memℓp a).summable (by norm_num)).comp_injective e.injective⟩

@[simp] theorem restrictTwo_apply (e : ℤ ↪ ℤ) (a : Coeff 2) (n : ℤ) :
    restrictTwo e a n = a (e n) := rfl

theorem norm_restrictTwo_le (e : ℤ ↪ ℤ) (a : Coeff 2) : ‖restrictTwo e a‖ ≤ ‖a‖ := by
  apply lp.norm_le_of_forall_sum_le (by norm_num : 0 < (2:ℝ≥0∞).toReal) (norm_nonneg a)
  intro S
  simpa only [restrictTwo_apply, Finset.sum_map] using
    lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2:ℝ≥0∞).toReal) a (S.map e)

/-- Raw l2 restriction as a bounded complex-linear map. -/
def restrictTwoCLM (e : ℤ ↪ ℤ) : Coeff 2 →L[ℂ] Coeff 2 :=
  LinearMap.mkContinuous
    { toFun := restrictTwo e
      map_add' := fun a b => by ext n; rfl
      map_smul' := fun c a => by ext n; rfl }
    1 (fun a => by change ‖restrictTwo e a‖ ≤ 1*‖a‖; simpa only [one_mul] using norm_restrictTwo_le e a)

end Coeff
namespace WeightedCoeff

/-- The exact target weight under restriction is its pullback along the index map. -/
def restrictTwoCLM (w : Weight) (e : ℤ ↪ ℤ) :
    WeightedCoeff w 2 →L[ℂ] WeightedCoeff (w.pullback e) 2 :=
  (weightIsometry (w.pullback e) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((Coeff.restrictTwoCLM e).comp (weightIsometry w 2).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem restrictTwoCLM_apply (w : Weight) (e : ℤ ↪ ℤ)
    (a : WeightedCoeff w 2) (n : ℤ) : (restrictTwoCLM w e a).val n = a.val (e n) := by
  change ((w (e n):ℂ)*a.val (e n))/(w (e n):ℂ) = _
  exact mul_div_cancel_left₀ _ (w.complex_ne_zero (e n))

theorem norm_restrictTwoCLM_le (w : Weight) (e : ℤ ↪ ℤ) (a : WeightedCoeff w 2) :
    ‖restrictTwoCLM w e a‖ ≤ ‖a‖ := by
  change ‖(weightIsometry (w.pullback e) 2).symm
    (Coeff.restrictTwo e (weightIsometry w 2 a))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (Coeff.norm_restrictTwo_le e _).trans_eq ((weightIsometry w 2).norm_map a)

/-- Restriction is a left inverse to the exact weighted insertion. -/
theorem restrictTwoCLM_insertIsometry (w : Weight) (e : ℤ ↪ ℤ)
    (a : WeightedCoeff (w.pullback e) 2) : restrictTwoCLM w e (insertIsometry w e a) = a := by
  apply Subtype.ext
  funext n
  rw [restrictTwoCLM_apply, insertIsometry_image]

/-- Insertion recovers the entire original sequence when all omitted entries vanish. -/
theorem insertIsometry_restrictTwoCLM (w : Weight) (e : ℤ ↪ ℤ) (a : WeightedCoeff w 2)
    (ha : ∀ k : ℤ, k ∉ Set.range e → a.val k = 0) :
    insertIsometry w e (restrictTwoCLM w e a) = a := by
  apply Subtype.ext
  funext k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨n, rfl⟩ := hk
    rw [insertIsometry_image, restrictTwoCLM_apply]
  · rw [insertIsometry_outside _ _ _ k hk, ha k hk]

end WeightedCoeff
end NLS
