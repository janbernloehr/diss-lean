import NLS.SequenceSpaces.BoundedCoordinateAnalytic
import NLS.SequenceSpaces.PositiveFourierInverseMajorant

/-! # A bounded positive scalar family as one native Banach analytic symbol -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem exists_positive_bounded_analytic_lift (U : Set E) (hU : IsOpen U)
    (f : ℕ+ → E → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ n : ℕ+, AnalyticOnNhd ℂ (f n) U)
    (hb : ∀ q∈U, ∀ n : ℕ+, ‖f n q‖ ≤ C) :
    ∃ M : E → Coeff ⊤, AnalyticOnNhd ℂ M U ∧
      ∀ q∈U, ‖M q‖ ≤ C ∧ (∀ j : ℤ, j ≤ 0 → M q j=0) ∧
        ∀ n : ℕ+, M q (n : ℤ)=f n q := by
  classical
  let a (q : E) : ℤ → ℂ := positiveFamilyCoordinates (fun n => f n q)
  have hab (q : E) (hq : q∈U) (j : ℤ) : ‖a q j‖ ≤ C := by
    by_cases hj : 0 < j
    · simpa only [a,positiveFamilyCoordinates,dif_pos hj] using hb q hq (positivePoleIndex j hj)
    · simp only [a,positiveFamilyCoordinates,dif_neg hj,norm_zero]
      exact hC
  have hm (q : E) (hq : q∈U) : Memℓp (a q) ⊤ :=
    memℓp_infty ⟨C,by rintro _ ⟨j,rfl⟩; exact hab q hq j⟩
  let M : E → Coeff ⊤ := fun q => ofFunctionOrZero ⊤ (a q)
  have hval (q : E) (hq : q∈U) (j : ℤ) : M q j=a q j :=
    ofFunctionOrZero_apply_of_mem ⊤ _ (hm q hq) j
  have hMb (q : E) (hq : q∈U) : ‖M q‖ ≤ C := by
    apply lp.norm_le_of_forall_le hC
    intro j
    rw [hval q hq j]
    exact hab q hq j
  have hMa (j : ℤ) : AnalyticOnNhd ℂ (fun q => M q j) U := by
    intro q hq
    have he : (fun u => a u j) =ᶠ[𝓝 q] (fun u => M u j) := by
      filter_upwards [hU.mem_nhds hq] with u hu
      exact (hval u hu j).symm
    apply AnalyticAt.congr (f := fun u => a u j) ?_ he
    by_cases hj : 0 < j
    · simpa only [a,positiveFamilyCoordinates,dif_pos hj] using ha (positivePoleIndex j hj) q hq
    · simpa only [a,positiveFamilyCoordinates,dif_neg hj] using
        (analyticAt_const (v := (0 : ℂ)) (𝕜 := ℂ) (x := q))
  refine ⟨M,analyticOnNhd_of_bounded_coordinatewise M hU hMa C hMb,?_⟩
  intro q hq
  refine ⟨hMb q hq,?_,?_⟩
  · intro j hj
    rw [hval q hq j]
    simp only [a,positiveFamilyCoordinates,dif_neg (not_lt.mpr hj)]
  · intro n
    rw [hval q hq (n : ℤ)]
    exact positiveFamilyCoordinates_nat (fun k => f k q) n

end NLS.Coeff
