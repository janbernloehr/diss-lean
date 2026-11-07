import NLS.SequenceSpaces.OddPositiveScalarExtension
import NLS.SequenceSpaces.PositiveScalarInfinity
import NLS.SequenceSpaces.LocallyBoundedRealization

/-! Locally uniformly bounded analytic positive samples have their
literal odd extension analytic in the bounded-sequence Banach space. -/
noncomputable section
open Set NLS.LpSequence
open scoped ENNReal
namespace NLS.Coeff

theorem norm_oddPositiveScalarExtension_le (u : ℕ+ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ n, ‖u n‖ ≤ C) (k : ℤ) : ‖oddPositiveScalarExtension u k‖ ≤ 2*C := by
  exact (norm_sub_le _ _).trans (by
    have h := norm_positiveScalarExtension_le u C hC hu k
    have h' := norm_positiveScalarExtension_le u C hC hu (-k)
    linarith)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticOnNhd_positiveScalarExtension (u : ℕ+ → E → ℂ) {U : Set E}
    (hu : ∀ n, AnalyticOnNhd ℂ (u n) U) (k : ℤ) :
    AnalyticOnNhd ℂ (fun q => positiveScalarExtension (fun n => u n q) k) U := by
  by_cases hk : k ∈ range positiveEmbedding
  · obtain ⟨n,rfl⟩ := hk
    change AnalyticOnNhd ℂ (fun q => positiveScalarExtension (fun n => u n q) ((n:ℕ):ℤ)) U
    simpa only [positiveScalarExtension_apply] using hu n
  · simp only [positiveScalarExtension_zero_of_not_mem_range _ k hk]
    exact analyticOnNhd_const

theorem analyticOnNhd_oddPositiveScalarExtension (u : ℕ+ → E → ℂ) {U : Set E}
    (hu : ∀ n, AnalyticOnNhd ℂ (u n) U) (k : ℤ) :
    AnalyticOnNhd ℂ (fun q => oddPositiveScalarExtension (fun n => u n q) k) U :=
  (analyticOnNhd_positiveScalarExtension u hu k).sub
    (analyticOnNhd_positiveScalarExtension u hu (-k))

theorem analytic_odd_realization_of_local_bounds (u : ℕ+ → E → ℂ) {U : Set E}
    (hU : IsOpen U) (hu : ∀ n, AnalyticOnNhd ℂ (u n) U)
    (hb : ∀ q ∈ U, ∃ V : Set E, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ V, ∀ n, ‖u n a‖ ≤ C) :
    (∀ q ∈ U, ∀ k, ofFunctionOrZero ⊤ (oddPositiveScalarExtension (fun n => u n q)) k =
      oddPositiveScalarExtension (fun n => u n q) k) ∧
    AnalyticOnNhd ℂ (fun q => ofFunctionOrZero ⊤ (oddPositiveScalarExtension (fun n => u n q))) U := by
  apply analytic_realization_of_local_bounds _ hU (analyticOnNhd_oddPositiveScalarExtension u hu)
  intro q hq
  obtain ⟨V,hV,hqV,hVU,C,hC,hb⟩ := hb q hq
  refine ⟨V,hV,hqV,hVU,2*C,?_⟩
  intro a ha
  have hpoint := norm_oddPositiveScalarExtension_le (fun n => u n a) C hC (hb a ha)
  have hm : Memℓp (oddPositiveScalarExtension (fun n => u n a)) ⊤ :=
    memℓp_infty ⟨2*C,by rintro _ ⟨k,rfl⟩; exact hpoint k⟩
  refine ⟨⟨_,hm⟩,fun _ => rfl,?_⟩
  exact lp.norm_le_of_forall_le (by positivity) hpoint

end NLS.Coeff
