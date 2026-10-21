import NLS.ZakharovShabat.WKBBoundaryLeadingFactors

/-! # Exact next-phase leading factors

The normalized leading combination factors into two inverse initial-coordinate multipliers with the correct boundary sign.
-/

noncomputable section
open Complex
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The inverse initial-coordinate factor in the boundary next-phase equation. -/
def wkbBoundaryNextLeadingFactor (θ : BoundaryCondition) (p : ℂ) : ℂ :=
  (1-extensionSign θ*p)⁻¹

/-- The next-phase factor is bounded and its error from one is controlled
by the small initial coordinate. -/
theorem norm_wkbBoundaryNextLeadingFactor_bounds (θ : BoundaryCondition) (p : ℂ)
    (hp : ‖p‖ ≤ 1/2) :
    ‖wkbBoundaryNextLeadingFactor θ p‖ ≤ 2 ∧
      ‖wkbBoundaryNextLeadingFactor θ p-1‖ ≤ 2*‖p‖ := by
  have hη : ‖extensionSign θ‖ = 1 := by cases θ <;> norm_num [extensionSign]
  obtain ⟨hp0,hpi⟩ := norm_inv_one_sub_mul_le_two (extensionSign θ) p
    (by simpa only [norm_mul,hη,one_mul] using hp)
  refine ⟨hpi,?_⟩
  have he : wkbBoundaryNextLeadingFactor θ p-1 =
      (extensionSign θ*p)*(1-extensionSign θ*p)⁻¹ := by
    unfold wkbBoundaryNextLeadingFactor
    field_simp [hp0]
    ring
  rw [he,norm_mul,norm_mul,hη,one_mul]
  exact (mul_le_mul_of_nonneg_left hpi (norm_nonneg p)).trans_eq (by ring)

/-- The normalized two-integral term factors into two multipliers near
one, with the exact boundary sign. -/
theorem wkb_boundary_next_leading_combination (θ : BoundaryCondition) (p q S T : ℂ)
    (hp : ‖p‖ ≤ 1/2) (hq : ‖q‖ ≤ 1/2) :
    ((q-extensionSign θ)*S+(extensionSign θ-p)*T)/(2*(1+p*q-extensionSign θ*(p+q))) =
      -(extensionSign θ/2)*(wkbBoundaryNextLeadingFactor θ p*S-
        wkbBoundaryNextLeadingFactor θ q*T) := by
  have hη : ‖extensionSign θ‖ = 1 := by cases θ <;> norm_num [extensionSign]
  have hp0 := (norm_inv_one_sub_mul_le_two (extensionSign θ) p
    (by simpa only [norm_mul,hη,one_mul] using hp)).1
  have hq0 := (norm_inv_one_sub_mul_le_two (extensionSign θ) q
    (by simpa only [norm_mul,hη,one_mul] using hq)).1
  have he : 1+p*q-extensionSign θ*(p+q) =
      (1-extensionSign θ*p)*(1-extensionSign θ*q) := by
    cases θ <;> simp only [extensionSign] <;> ring
  rw [he]
  unfold wkbBoundaryNextLeadingFactor
  cases θ <;> simp only [extensionSign,one_mul,neg_one_mul,sub_neg_eq_add] at hp0 hq0 ⊢ <;>
    field_simp [hp0,hq0] <;> ring

end NLS.ZakharovShabat
