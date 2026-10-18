import NLS.ZakharovShabat.SobolevWKBInitialBasis

/-! # Uniform decay of both WKB initial coordinates

Both initial coordinates retain an inverse-frequency factor on original Sobolev balls, through the full truncation order.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- Both off-diagonal initial coordinates have one inverse-frequency
factor, uniformly on the original Sobolev ball and through N=s. -/
theorem exists_uniform_nlsWKB_initial_coordinate_decay
    (s N : ℕ) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ →
        ‖nlsWKBInitialLower a b N z‖ ≤ B*‖(2*I*z)⁻¹‖ ∧
        ‖nlsWKBInitialUpper a b N z‖ ≤ B*‖(2*I*z)⁻¹‖ := by
  obtain ⟨B,hB,h⟩ := exists_uniform_nlsRiccatiApproximation_bound s N hNs R hR
  have hsmall (ab : SobolevSource s) (hab : ‖ab‖ ≤ R) (a b : ℝ → ℂ)
      (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
      (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
      (hca : ∀ j, ab.1.val j = periodOneCoefficient a j)
      (hcb : ∀ j, ab.2.val j = periodOneCoefficient b j)
      (z : ℂ) (hz : 1 ≤ ‖z‖) : ‖nlsWKBInitialLower a b N z‖ ≤ B*‖(2*I*z)⁻¹‖ := by
    have hw : ‖(2*I*z)⁻¹‖ ≤ 1 := by
      simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
      apply inv_le_one_of_one_le₀
      linarith
    simpa only [nlsWKBInitialLower,nlsWKBVector,nlsWKBCarrier_zero,
      mul_one,norm_mul,norm_neg,norm_I,one_mul] using h ab hab a b ha hb hpa hpb hca hcb (2*I*z)⁻¹ hw 0
  refine ⟨B,hB,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hz
  refine ⟨hsmall ab hab a b ha hb hpa hpb hca hcb z hz,?_⟩
  let cd : SobolevSource s := (-ab.2,-ab.1)
  have hcd : ‖cd‖ ≤ R := by simpa only [cd,Prod.norm_def,norm_neg,max_comm] using hab
  have hc1 (j : ℤ) : cd.1.val j = periodOneCoefficient (-b) j := by
    simpa only [cd,WeightedCoeff.neg_val,periodOneCoefficient_neg] using congrArg Neg.neg (hcb j)
  have hc2 (j : ℤ) : cd.2.val j = periodOneCoefficient (-a) j := by
    simpa only [cd,WeightedCoeff.neg_val,periodOneCoefficient_neg] using congrArg Neg.neg (hca j)
  have hq := hsmall cd hcd (-b) (-a) hb.neg ha.neg
    (fun x => congrArg Neg.neg (hpb x)) (fun x => congrArg Neg.neg (hpa x)) hc1 hc2 (-z) (by simpa using hz)
  change ‖nlsWKBInitialLower (-b) (-a) N (-z)‖ ≤ _
  simpa only [mul_neg,inv_neg,norm_neg] using hq

end NLS.ZakharovShabat
