import NLS.ZakharovShabat.SobolevWKBLeadingOscillatoryComparison
import NLS.Fourier.PiLatticeCoefficient

/-! # The exact lattice Fourier term in the WKB endpoint error

At every nonzero signed pi-lattice index the leading integral is the original Riccati density coefficient, with no normalization factor.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The actual endpoint error has the original top-density Fourier
coefficient as its leading term at every nonzero signed lattice index. -/
theorem exists_uniform_nlsWKB_lattice_endpoint_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ n : ℤ, n ≠ 0 →
        ‖nlsWKBVector a b N ((Real.pi:ℂ)*n) 1-
          classicalSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous)
            ((Real.pi:ℂ)*n) (nlsWKBVector a b N ((Real.pi:ℂ)*n) 0) 1-
          (0,-I*((2*I*((Real.pi:ℂ)*n))⁻¹)^N*exp (I*((Real.pi:ℂ)*n))*
            (sobolevRiccatiDensity s ab N hNs).val n)‖ ≤
            C*‖(2*I*((Real.pi:ℂ)*n))⁻¹‖^(N+1) := by
  obtain ⟨C,hC,h⟩ := exists_uniform_nlsWKB_leading_oscillatory_error_bound s N hs hNs R hR 0
  refine ⟨C,hC,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb n hn
  have hnabs : (1:ℝ) ≤ |(n:ℝ)| := by
    have hi : 1 ≤ n.natAbs := Int.natAbs_pos.mpr hn
    have hr : (1:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast hi
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hr
  have hzn : 1 ≤ ‖(Real.pi:ℂ)*n‖ := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_intCast]
    nlinarith [Real.pi_gt_three]
  have he := h ab hab a b ha hb hpa hpb hca hcb ((Real.pi:ℂ)*n) hzn (by simp) ⟨1,⟨zero_le_one,le_rfl⟩⟩
  simp only [Complex.ofReal_one,mul_one] at he
  rw [integral_pi_lattice_eq_periodOneCoefficient,
    ← sobolevRiccatiDensity_eq_classical_coefficients s ab a b ha hb hpa hpb hca hcb N hNs n] at he
  exact he

end NLS.ZakharovShabat
