import NLS.ZakharovShabat.NLSWKBBoundaryPhaseElimination

/-! # Bounds on the exact phase-elimination multipliers

The leading-integral factors are bounded and differ from one by a controlled multiple of the initial coordinates. The separated-model coefficient has the same small factor.
-/

noncomputable section
open Complex
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The exact coefficient of the first leading integral after eliminating
and dividing out the separated WKB phase. The second coefficient swaps p and q. -/
def wkbBoundaryLeadingFactor (θ : BoundaryCondition) (p q : ℂ) : ℂ :=
  (1-extensionSign θ*q)*(1-extensionSign θ*p)⁻¹*(1-p*q)⁻¹

/-- The phase-elimination multipliers are bounded and differ from one
by at most a constant times the two initial coordinates. -/
theorem norm_wkbBoundaryLeadingFactor_bounds (θ : BoundaryCondition) (p q : ℂ)
    (hp : ‖p‖ ≤ 1/2) (hq : ‖q‖ ≤ 1/2) :
    ‖wkbBoundaryLeadingFactor θ p q‖ ≤ 6 ∧
      ‖wkbBoundaryLeadingFactor θ p q-1‖ ≤ 6*(‖p‖+‖q‖) := by
  have hη : ‖extensionSign θ‖ = 1 := by cases θ <;> norm_num [extensionSign]
  have hpη : ‖extensionSign θ*p‖ ≤ 1/2 := by simpa only [norm_mul,hη,one_mul] using hp
  obtain ⟨hp0,hpi⟩ := norm_inv_one_sub_mul_le_two (extensionSign θ) p hpη
  have hpq : ‖p*q‖ ≤ 1/2 := by
    rw [norm_mul]
    nlinarith [norm_nonneg p,norm_nonneg q]
  obtain ⟨hd,hdi⟩ := norm_inv_one_sub_mul_le_two p q hpq
  have hq1 : ‖1-extensionSign θ*q‖ ≤ 3/2 := by
    apply (norm_sub_le _ _).trans
    rw [norm_one,norm_mul,hη,one_mul]
    linarith
  constructor
  · unfold wkbBoundaryLeadingFactor
    rw [norm_mul,norm_mul]
    calc
      _ ≤ ((3/2)*2)*2 := mul_le_mul (mul_le_mul hq1 hpi (norm_nonneg _) (by norm_num)) hdi
        (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  · have he : wkbBoundaryLeadingFactor θ p q-1 =
        (extensionSign θ*(p-q)*(1-extensionSign θ*p)⁻¹+p*q)*(1-p*q)⁻¹ := by
      unfold wkbBoundaryLeadingFactor
      have hd' : 1-q*p ≠ 0 := by simpa only [mul_comm] using hd
      field_simp [hp0,hd,hd']
      ring
    rw [he,norm_mul]
    have hn : ‖extensionSign θ*(p-q)*(1-extensionSign θ*p)⁻¹+p*q‖ ≤ 3*(‖p‖+‖q‖) := by
      apply (norm_add_le _ _).trans
      simp only [norm_mul,hη,one_mul]
      have hm := mul_le_mul (norm_sub_le p q) hpi (norm_nonneg _) (by positivity : 0 ≤ ‖p‖+‖q‖)
      have hprod : ‖p‖*‖q‖ ≤ ‖p‖ := mul_le_of_le_one_right (norm_nonneg _) (by linarith)
      nlinarith [norm_nonneg q]
    exact (mul_le_mul hn hdi (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- The remaining separated-model coefficient is small by the same
initial-coordinate factor, so a pointwise separated error gains one order. -/
theorem norm_wkb_boundary_separated_factor_le (θ : BoundaryCondition) (p q : ℂ)
    (hp : ‖p‖ ≤ 1/2) (hq : ‖q‖ ≤ 1/2) :
    ‖(-2*I*(p-q))/(1+p*q-extensionSign θ*(p+q))‖ ≤ 8*(‖p‖+‖q‖) := by
  have hi := (norm_inv_wkb_boundary_phase_factor_le_four θ p q hp hq).2
  rw [div_eq_mul_inv,norm_mul,norm_mul,norm_mul]
  norm_num only [norm_neg,norm_ofNat,norm_I,mul_one]
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left (norm_sub_le p q) (by norm_num : (0:ℝ) ≤ 2))
    hi (norm_nonneg _) (by positivity : 0 ≤ 2*(‖p‖+‖q‖))
  exact hh.trans_eq (by ring)

end NLS.ZakharovShabat
