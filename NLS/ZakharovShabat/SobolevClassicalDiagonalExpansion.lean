import NLS.ZakharovShabat.SobolevClassicalDiagonalCarrier
import NLS.ZakharovShabat.SobolevWKBFirstCarrierExpansion

/-! # First-order expansion of both actual diagonal entries

The actual fundamental diagonals have the explicit mass-primitive corrections with quadratic inverse-frequency errors throughout the physical period.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- Both actual diagonal fundamental entries have their explicit first
mass-primitive corrections with quadratic inverse-frequency errors,
uniformly on original complex Hs balls and the whole physical period. -/
theorem exists_uniform_classical_diagonal_first_order_expansion
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H → ∀ t : Icc (0:ℝ) 1,
        ‖(classicalSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z (1,0) t).1-
          exp (-I*z*t.val)*(1-(2*I*z)⁻¹*nlsWKBMassPrimitive a b t)‖ ≤ C*‖(2*I*z)⁻¹‖^2 ∧
        ‖(classicalSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z (0,1) t).2-
          exp (I*z*t.val)*(1+(2*I*z)⁻¹*nlsWKBMassPrimitive a b t)‖ ≤ C*‖(2*I*z)⁻¹‖^2 := by
  obtain ⟨C₁,hC₁,hactual⟩ := exists_uniform_classical_diagonal_carrier_error_bound s hs R hR H
  obtain ⟨C₂,hC₂,hcarrier⟩ := exists_uniform_nlsWKB_first_carrier_expansion_bound s hs R hR H
  refine ⟨C₁+C₂,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hz hzH t
  obtain ⟨hA,hB⟩ := hactual ab hab a b ha hb hpa hpb hca hcb z hz hzH t
  obtain ⟨hC,hD⟩ := hcarrier ab hab a b ha hb hpa hpb hca hcb z hz hzH t t.property
  have hcombine (u v r : ℂ) (hu : ‖u-v‖ ≤ C₁*‖(2*I*z)⁻¹‖^2)
      (hv : ‖v-r‖ ≤ C₂*‖(2*I*z)⁻¹‖^2) : ‖u-r‖ ≤ (C₁+C₂)*‖(2*I*z)⁻¹‖^2 := by
    calc
      _ = ‖(u-v)+(v-r)‖ := by congr 1; ring
      _ ≤ ‖u-v‖+‖v-r‖ := norm_add_le _ _
      _ ≤ C₁*‖(2*I*z)⁻¹‖^2+C₂*‖(2*I*z)⁻¹‖^2 := add_le_add hu hv
      _ = _ := by ring
  exact ⟨hcombine _ _ _ hA hC,hcombine _ _ _ hB hD⟩

end NLS.ZakharovShabat
