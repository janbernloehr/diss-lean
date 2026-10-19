import NLS.ZakharovShabat.SobolevWKBNextForcingExpansion
import NLS.ZakharovShabat.SobolevRiccatiPhysicalBounds

/-! # The original Sobolev bound for the next forcing density

The explicit next WKB forcing density has a uniform physical L2 bound on original Hs balls through the full truncation order.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The next forcing density has a uniform physical L2 bound on the
original Hs ball through N=s. Its top derivative is multiplied only by
the bounded mass primitive. -/
theorem exists_uniform_nlsWKBNextForcingDensity_L2_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      Real.sqrt (∫ x in (0:ℝ)..1, ‖nlsWKBNextForcingDensity a b N x‖^2) ≤ L := by
  obtain ⟨A,hA,hpot⟩ := exists_uniform_first_potential_pointwise_bound s hs R hR
  obtain ⟨C,hC,hres⟩ := exists_uniform_nlsRiccatiResidual_next_order_bounds s N hs hNs R hR
  obtain ⟨L,hL,hL2⟩ := exists_uniform_nlsRiccatiDensity_L2_bound s N hNs R hR
  refine ⟨2*C+2*A^2*L,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb
  let ρ := nlsRiccatiDensity a b N
  let f := nlsWKBNextForcingDensity a b N
  have hρ : Continuous ρ := (contDiff_nlsRiccatiDensity a b ha hb N).continuous
  have hf : Continuous f := continuous_nlsWKBNextForcingDensity a b ha hb N
  have hP (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : ‖nlsWKBMassPrimitive a b x‖ ≤ A^2 :=
    norm_nlsWKBMassPrimitive_le a b A hA
      (hpot ab hab a b ha hb hpa hpb hca hcb)
      (hpot (ab.2,ab.1) (by simpa only [Prod.norm_def,max_comm] using hab)
        b a hb ha hpb hpa hcb hca) x hx
  have hpoint (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : ‖f x‖^2 ≤ 2*C^2+2*A^4*‖ρ x‖^2 := by
    have hc := (hres ab hab a b ha hb hpa hpb hca hcb x).1
    have hn : ‖f x‖ ≤ C+A^2*‖ρ x‖ := by
      dsimp only [f,nlsWKBNextForcingDensity]
      rw [norm_mul,norm_I,one_mul]
      apply (norm_add_le _ _).trans
      rw [norm_mul]
      have hh := mul_le_mul_of_nonneg_left (hP x hx) (norm_nonneg (ρ x))
      dsimp only [ρ] at hh ⊢
      linarith
    have hh := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (C-A^2*‖ρ x‖)]
  have hρnonneg : 0 ≤ ∫ x in (0:ℝ)..1, ‖ρ x‖^2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)
  have hρsq : (∫ x in (0:ℝ)..1, ‖ρ x‖^2) ≤ L^2 := by
    have hh := hL2 ab hab a b ha hb hpa hpb hca hcb
    nlinarith [Real.sq_sqrt hρnonneg,Real.sqrt_nonneg (∫ x in (0:ℝ)..1, ‖ρ x‖^2)]
  have hsq : (∫ x in (0:ℝ)..1, ‖f x‖^2) ≤ 2*C^2+2*A^4*L^2 := by
    calc
      _ ≤ ∫ x in (0:ℝ)..1, 2*C^2+2*A^4*‖ρ x‖^2 := by
        apply intervalIntegral.integral_mono_on (by norm_num) ((hf.norm.pow 2).intervalIntegrable 0 1)
          ((by fun_prop : Continuous (fun x => 2*C^2+2*A^4*‖ρ x‖^2)).intervalIntegrable 0 1) hpoint
      _ = 2*C^2+2*A^4*(∫ x in (0:ℝ)..1, ‖ρ x‖^2) := by
        have h₁ : IntervalIntegrable (fun _ : ℝ => 2*C^2) volume 0 1 := continuous_const.intervalIntegrable 0 1
        have h₂ : IntervalIntegrable (fun x : ℝ => 2*A^4*‖ρ x‖^2) volume 0 1 :=
          (continuous_const.mul (hρ.norm.pow 2)).intervalIntegrable 0 1
        rw [intervalIntegral.integral_add h₁ h₂,intervalIntegral.integral_const_mul]
        simp
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hρsq (by positivity))
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  nlinarith [mul_nonneg hC (mul_nonneg (sq_nonneg A) hL)]

end NLS.ZakharovShabat
