import NLS.SequenceSpaces.WeightedMultiplier

/-! Reciprocal bounded Fourier multipliers give a genuine Banach-space
linear equivalence, including exponent infinity. -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def weightedMultiplierEquiv (w v : Weight) (m r : ℤ → ℂ) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hm : ∀ k, v k*‖m k‖ ≤ C*w k) (hr : ∀ k, w k*‖r k‖ ≤ D*v k)
    (hprod : ∀ k, m k*r k=1) : WeightedCoeff w p ≃L[ℂ] WeightedCoeff v p where
  toFun := weightedMultiplierCLM w v m C hC hm
  invFun := weightedMultiplierCLM v w r D hD hr
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv a := by
    apply Subtype.ext
    funext k
    change r k*(m k*a.val k)=a.val k
    rw [← mul_assoc,mul_comm (r k),hprod,one_mul]
  right_inv a := by
    apply Subtype.ext
    funext k
    change m k*(r k*a.val k)=a.val k
    rw [← mul_assoc,hprod,one_mul]
  continuous_toFun := (weightedMultiplierCLM w v m C hC hm).continuous
  continuous_invFun := (weightedMultiplierCLM v w r D hD hr).continuous

theorem weightedMultiplierEquiv_apply (w v : Weight) (m r : ℤ → ℂ) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hm : ∀ k, v k*‖m k‖ ≤ C*w k) (hr : ∀ k, w k*‖r k‖ ≤ D*v k)
    (hprod : ∀ k, m k*r k=1) (a : WeightedCoeff w p) (k : ℤ) :
    (weightedMultiplierEquiv w v m r C D hC hD hm hr hprod a).val k=m k*a.val k := rfl

theorem weightedMultiplierEquiv_symm_apply (w v : Weight) (m r : ℤ → ℂ) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hm : ∀ k, v k*‖m k‖ ≤ C*w k) (hr : ∀ k, w k*‖r k‖ ≤ D*v k)
    (hprod : ∀ k, m k*r k=1) (a : WeightedCoeff v p) (k : ℤ) :
    ((weightedMultiplierEquiv w v m r C D hC hD hm hr hprod).symm a).val k=r k*a.val k := rfl

end NLS.WeightedCoeff
