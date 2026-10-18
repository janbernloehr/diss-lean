import NLS.ZakharovShabat.SourceSquaredGapReciprocalRows
import NLS.SequenceSpaces.WeightedReciprocalSquareDecay

/-! # Weighted squared-gap row decay

A weighted Hilbert gap majorant gives inverse-square-bracket decay of the full actual squared-gap reciprocal row.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A weighted Hilbert gap sequence gives inverse-square decay of the entire actual squared-gap row. -/
theorem sourceSquaredGapReciprocalRow_weighted_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (G : Coeff 2)
    (hG : ∀ m : ℤ, (1+|(m:ℝ)|)*‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ ≤ ‖G m‖)
    (n : ℤ) :
    (1+|(n:ℝ)|)^2*(∑' m, sourceSquaredGapReciprocalTerm hp hp1 ψ n m) ≤ 4*‖G‖^2 := by
  let H := Coeff.holderProduct (q := 1) G G
  let u : ℤ → ℂ := fun m => (sourceSquaredGapReciprocalTerm hp hp1 ψ n m : ℂ)
  have hH (m : ℤ) : ‖H m‖ = ‖G m‖^2 := by
    simp only [H,Coeff.holderProduct_apply,norm_mul,pow_two]
  have hterm (m : ℤ) : sourceSquaredGapReciprocalTerm hp hp1 ψ n m =
      ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2*
        ‖Coeff.shift n (Coeff.puncturedLattice 2 (by norm_num)) m‖^2 := by
    rw [Coeff.norm_shift_puncturedLattice_apply]
    by_cases hm : m=n
    · simp [sourceSquaredGapReciprocalTerm,hm]
    · simp only [sourceSquaredGapReciprocalTerm,if_neg hm,
        Real.rpow_neg (abs_nonneg _),Real.rpow_two,inv_pow]
  have hnorm (m : ℤ) : ‖u m‖ = sourceSquaredGapReciprocalTerm hp hp1 ψ n m := by
    rw [show u m = (sourceSquaredGapReciprocalTerm hp hp1 ψ n m : ℂ) from rfl,
      Complex.norm_real,Real.norm_of_nonneg (by rw [hterm]; positivity)]
  have hu (m : ℤ) : ‖u m‖ ≤ 1*‖H m‖/(1+|(m:ℝ)|)^2*
      ‖Coeff.shift n (Coeff.puncturedLattice 2 (by norm_num)) m‖^2 := by
    rw [hnorm,hterm,one_mul,hH]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply (le_div_iff₀ (by positivity)).mpr
    have h := pow_le_pow_left₀ (by positivity) (hG m) 2
    simpa only [mul_pow,mul_comm] using h
  obtain ⟨_,hb⟩ := Coeff.summable_norm_reciprocal_sq_of_weighted_l1 H u n 1 (by norm_num) hu
  simp only [hnorm,mul_one] at hb
  have hHnorm : ‖H‖ ≤ ‖G‖^2 := by
    simpa only [H,pow_two] using Coeff.norm_holderProduct_le (q := 1) G G
  exact hb.trans (mul_le_mul_of_nonneg_left hHnorm (by norm_num : (0:ℝ) ≤ 4))

end NLS.ZakharovShabat
