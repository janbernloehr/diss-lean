import NLS.ZakharovShabat.SobolevWKBSecondColumn
import NLS.ZakharovShabat.ClassicalBasisReconstruction

/-! # Uniform invertibility of the WKB initial basis

One threshold on each original Sobolev ball controls both initial coordinates and the inverse determinant, including empty H0 truncation.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- Lower off-diagonal coordinate of the first WKB initial vector. -/
def nlsWKBInitialLower (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  (nlsWKBVector a b N z 0).2

/-- Upper off-diagonal coordinate of the second WKB initial vector. -/
def nlsWKBInitialUpper (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  (nlsWKBSecondVector a b N z 0).1

@[simp] theorem nlsWKBVector_initial (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) :
    nlsWKBVector a b N z 0 = (1,nlsWKBInitialLower a b N z) := by
  simp [nlsWKBInitialLower,nlsWKBVector]

@[simp] theorem nlsWKBSecondVector_initial (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) :
    nlsWKBSecondVector a b N z 0 = (nlsWKBInitialUpper a b N z,1) := by
  simp [nlsWKBInitialUpper,nlsWKBSecondVector,nlsWKBVector]

/-- The initial WKB basis is uniformly invertible outside one source-ball
frequency threshold. This also includes the empty H0 truncation. -/
theorem exists_uniform_nlsWKB_initial_basis_bounds
    (s N : ℕ) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, T ≤ ‖z‖ →
        ‖nlsWKBInitialLower a b N z‖ ≤ 1/2 ∧
        ‖nlsWKBInitialUpper a b N z‖ ≤ 1/2 ∧
        1-nlsWKBInitialLower a b N z*nlsWKBInitialUpper a b N z ≠ 0 ∧
        ‖(1-nlsWKBInitialLower a b N z*nlsWKBInitialUpper a b N z)⁻¹‖ ≤ 2 := by
  obtain ⟨B,hB,h⟩ := exists_uniform_nlsRiccatiApproximation_bound s N hNs R hR
  have hsmall (ab : SobolevSource s) (hab : ‖ab‖ ≤ R) (a b : ℝ → ℂ)
      (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
      (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
      (hca : ∀ j, ab.1.val j = periodOneCoefficient a j)
      (hcb : ∀ j, ab.2.val j = periodOneCoefficient b j)
      (z : ℂ) (hz : B+1 ≤ ‖z‖) : ‖nlsWKBInitialLower a b N z‖ ≤ 1/2 := by
    have hzn : 1 ≤ ‖z‖ := by linarith
    have hw : ‖(2*I*z)⁻¹‖ ≤ 1 := by
      simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
      apply inv_le_one_of_one_le₀
      linarith
    have hh := h ab hab a b ha hb hpa hpb hca hcb (2*I*z)⁻¹ hw 0
    simp only [nlsWKBInitialLower,nlsWKBVector,nlsWKBCarrier_zero,
      mul_one,norm_mul,norm_neg,norm_I,one_mul]
    apply hh.trans
    simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*‖z‖)).mpr
    linarith
  refine ⟨B+1,by linarith,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hz
  have hp := hsmall ab hab a b ha hb hpa hpb hca hcb z hz
  let cd : SobolevSource s := (-ab.2,-ab.1)
  have hcd : ‖cd‖ ≤ R := by simpa only [cd,Prod.norm_def,norm_neg,max_comm] using hab
  have hc1 (j : ℤ) : cd.1.val j = periodOneCoefficient (-b) j := by
    simpa only [cd,WeightedCoeff.neg_val,periodOneCoefficient_neg] using congrArg Neg.neg (hcb j)
  have hc2 (j : ℤ) : cd.2.val j = periodOneCoefficient (-a) j := by
    simpa only [cd,WeightedCoeff.neg_val,periodOneCoefficient_neg] using congrArg Neg.neg (hca j)
  have hq : ‖nlsWKBInitialUpper a b N z‖ ≤ 1/2 := by
    change ‖nlsWKBInitialLower (-b) (-a) N (-z)‖ ≤ _
    exact hsmall cd hcd (-b) (-a) hb.neg ha.neg
      (by intro x; change -b (x+1) = -b x; rw [hpb x])
      (by intro x; change -a (x+1) = -a x; rw [hpa x]) hc1 hc2 (-z) (by simpa using hz)
  have hpq : ‖nlsWKBInitialLower a b N z*nlsWKBInitialUpper a b N z‖ ≤ 1/2 := by
    rw [norm_mul]
    have hm := mul_le_mul hp hq (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1/2)
    linarith
  exact ⟨hp,hq,norm_inv_one_sub_mul_le_two _ _ hpq⟩

end NLS.ZakharovShabat
