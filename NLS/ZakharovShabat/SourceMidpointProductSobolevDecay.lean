import NLS.ZakharovShabat.SourceMidpointProductFullDiscSup
import NLS.ZakharovShabat.SourceSingleRootMidpointBounds
import NLS.SequenceSpaces.WeightedReciprocalDecay
import NLS.ComplexAnalysis.SignedProductEstimates

/-! # Weighted decay of the actual midpoint product

A weighted Hilbert numerator controls the full midpoint product uniformly in the selected index and spectral point under the stated separation estimate.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A weighted Hilbert numerator gives inverse-bracket decay of the actual midpoint product. -/
theorem norm_sourceMidpointProductRow_weighted_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (α G : Coeff 2) (hG : ∀ m : ℤ, (1+|(m:ℝ)|)*‖α m‖ ≤ ‖G m‖)
    (n : ℤ) (z : ℂ) (C : ℝ) (hC : 1 ≤ C)
    (hsep : ∀ m : ℤ, m ≠ n → |((n-m:ℤ):ℝ)| ≤ C*
      ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z‖) :
    (1+|(n:ℝ)|)*‖sourceMidpointProductRow hp hp1 ψ α n z‖ ≤
      (4*C*‖G‖)*Real.exp (4*C*‖G‖) := by
  let u : ℤ → ℂ := fun m => if m=n then 0 else α m/
    (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z)
  have hC0 : 0 ≤ C := by linarith
  have hu (m : ℤ) : ‖u m‖ ≤ C*‖G m‖/(1+|(m:ℝ)|)*
      ‖Coeff.shift n (Coeff.puncturedLattice 2 (by norm_num)) m‖ := by
    rw [Coeff.norm_shift_puncturedLattice_apply]
    by_cases hm : m=n
    · simp only [u,if_pos hm,norm_zero,mul_zero,le_refl]
    have hg : ‖α m‖ ≤ ‖G m‖/(1+|(m:ℝ)|) :=
      (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hG m)
    dsimp only [u]
    rw [if_neg hm]
    calc
      _ ≤ C*(‖α m‖/|((m-n:ℤ):ℝ)|) :=
        norm_midpoint_displacement_div_le C hC n m (Ne.symm hm) _ _ _ (hsep m hm)
      _ ≤ C*((‖G m‖/(1+|(m:ℝ)|))/|((m-n:ℤ):ℝ)|) := by gcongr
      _ = _ := by rw [if_neg hm]; ring
  obtain ⟨hs,hb⟩ := Coeff.summable_norm_reciprocal_of_weighted_hilbert G u n C hC0 hu
  let S := ∑' m, ‖u m‖
  let K := 4*C*‖G‖
  have hS : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
  have hSK : S ≤ K := (by nlinarith [abs_nonneg (n:ℝ)] : S ≤ (1+|(n:ℝ)|)*S).trans hb
  have hprod : ‖(∏' m, (1+u m))-1‖ ≤ S*Real.exp K := by
    have h := NLS.ComplexAnalysis.norm_tprod_one_add_sub_one_le_exp_sub_one_le u hs
    exact h.1.trans (h.2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hSK) hS))
  change (1+|(n:ℝ)|)*‖(∏' m, (1+u m))-1‖ ≤ K*Real.exp K
  calc
    _ ≤ (1+|(n:ℝ)|)*(S*Real.exp K) := mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = ((1+|(n:ℝ)|)*S)*Real.exp K := by ring
    _ ≤ K*Real.exp K := mul_le_mul_of_nonneg_right hb (Real.exp_pos K).le

end NLS.ZakharovShabat
