import NLS.SequenceSpaces.LocallyBoundedRealization

/-! Even extension of positive samples with unit central coefficient.
Local uniform bounds realize analytic positive families as actual bounded
signed sequences, preserving the literal samples at both signs. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff

def evenUnitExtension (u : ℕ+ → ℂ) (k : ℤ) : ℂ :=
  if hk : k=0 then 1 else u ⟨k.natAbs,Int.natAbs_pos.mpr hk⟩

theorem evenUnitExtension_zero (u : ℕ+ → ℂ) : evenUnitExtension u 0=1 := by
  simp [evenUnitExtension]

theorem evenUnitExtension_positive (u : ℕ+ → ℂ) (n : ℕ+) :
    evenUnitExtension u ((n:ℕ):ℤ)=u n := by
  have hn : ((n:ℕ):ℤ) ≠ 0 := by exact_mod_cast n.ne_zero
  simp only [evenUnitExtension,dif_neg hn,Int.natAbs_natCast]
  exact congrArg u (PNat.coe_injective rfl)

theorem evenUnitExtension_negative (u : ℕ+ → ℂ) (n : ℕ+) :
    evenUnitExtension u (-((n:ℕ):ℤ))=u n := by
  have hn : -((n:ℕ):ℤ) ≠ 0 := by exact_mod_cast neg_ne_zero.mpr (by exact_mod_cast n.ne_zero : (n:ℤ) ≠ 0)
  simp only [evenUnitExtension,dif_neg hn,Int.natAbs_neg,Int.natAbs_natCast]
  exact congrArg u (PNat.coe_injective rfl)

theorem norm_evenUnitExtension_le (u : ℕ+ → ℂ) (C : ℝ) (hC : 1 ≤ C)
    (hu : ∀ n, ‖u n‖ ≤ C) (k : ℤ) : ‖evenUnitExtension u k‖ ≤ C := by
  unfold evenUnitExtension
  split_ifs
  · simpa only [norm_one] using hC
  · exact hu _

theorem evenUnitExtension_inv (u : ℕ+ → ℂ) (k : ℤ) :
    evenUnitExtension (fun n => (u n)⁻¹) k = (evenUnitExtension u k)⁻¹ := by
  unfold evenUnitExtension
  split_ifs <;> simp only [inv_one]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticOnNhd_evenUnitExtension (u : ℕ+ → E → ℂ) {U : Set E}
    (hu : ∀ n, AnalyticOnNhd ℂ (u n) U) (k : ℤ) :
    AnalyticOnNhd ℂ (fun q => evenUnitExtension (fun n => u n q) k) U := by
  by_cases hk : k=0
  · subst k
    simp only [evenUnitExtension_zero]
    exact analyticOnNhd_const
  · simpa only [evenUnitExtension,dif_neg hk] using hu ⟨k.natAbs,Int.natAbs_pos.mpr hk⟩

theorem analytic_evenUnit_realization_of_local_bounds (u : ℕ+ → E → ℂ) {U : Set E}
    (hU : IsOpen U) (hu : ∀ n, AnalyticOnNhd ℂ (u n) U)
    (hb : ∀ q ∈ U, ∃ V : Set E, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∀ a ∈ V, ∀ n, ‖u n a‖ ≤ C) :
    (∀ q ∈ U, ∀ k, ofFunctionOrZero ⊤ (evenUnitExtension (fun n => u n q)) k =
      evenUnitExtension (fun n => u n q) k) ∧
    AnalyticOnNhd ℂ (fun q => ofFunctionOrZero ⊤ (evenUnitExtension (fun n => u n q))) U := by
  apply analytic_realization_of_local_bounds _ hU (analyticOnNhd_evenUnitExtension u hu)
  intro q hq
  obtain ⟨V,hV,hqV,hVU,C,hC,hb⟩ := hb q hq
  refine ⟨V,hV,hqV,hVU,C,?_⟩
  intro a ha
  have hpoint := norm_evenUnitExtension_le (fun n => u n a) C hC (hb a ha)
  have hm : Memℓp (evenUnitExtension (fun n => u n a)) ⊤ :=
    memℓp_infty ⟨C,by rintro _ ⟨k,rfl⟩; exact hpoint k⟩
  refine ⟨⟨_,hm⟩,fun _ => rfl,?_⟩
  exact lp.norm_le_of_forall_le (zero_le_one.trans hC) hpoint

end NLS.Coeff
