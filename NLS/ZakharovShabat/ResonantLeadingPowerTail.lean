import NLS.SequenceSpaces.SampledPowerTail
import NLS.ZakharovShabat.WeightedContraction

/-!
# The leading signed Fourier-mode power tail

Both resonant leading coefficients have a convergent weighted power sum,
with no extra potential-norm factor. The sum is bounded by the exact pair
Fourier tail at any cutoff no larger than twice the resonance cutoff.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Combined weighted power of the two signed leading resonant coefficients. -/
def resonantLeadingPower (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) : ℝ :=
  (w (2*n)*‖φ.fst.val (-(2*n))‖)^p.toReal + (w (2*n)*‖φ.snd.val (2*n)‖)^p.toReal

/-- The leading coefficient power tail is summable with the exact pair-tail budget. -/
theorem resonantLeadingPower_tail_summable_and_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N M : ℕ) (hM : M ≤ 2*N) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then resonantLeadingPower w φ n else 0) ∧
      (∑' n : ℤ, if N ≤ n.natAbs then resonantLeadingPower w φ n else 0) ≤
        ‖weightedPairFourierTail w.toWeight M φ‖^p.toReal := by
  obtain ⟨hs₁,hb₁⟩ := Coeff.sampled_fourierTail_power hp (WeightedCoeff.weightEquiv w.toWeight p φ.fst)
    (fun n : ℤ => -(2*n)) (by intro x y h; change -(2*x) = -(2*y) at h; omega) N M (by intro n hn; omega)
  obtain ⟨hs₂,hb₂⟩ := Coeff.sampled_fourierTail_power hp (WeightedCoeff.weightEquiv w.toWeight p φ.snd)
    (fun n : ℤ => 2*n) (by intro x y h; change 2*x = 2*y at h; omega) N M (by intro n hn; omega)
  have he₁ (n : ℤ) : ‖WeightedCoeff.weightEquiv w.toWeight p φ.fst (-(2*n))‖ = w (2*n)*‖φ.fst.val (-(2*n))‖ := by
    simp [WeightedCoeff.weightEquiv_apply, Complex.norm_real, Real.norm_of_nonneg (w.positive _).le, w.apply_neg]
  have he₂ (n : ℤ) : ‖WeightedCoeff.weightEquiv w.toWeight p φ.snd (2*n)‖ = w (2*n)*‖φ.snd.val (2*n)‖ := by
    simp [WeightedCoeff.weightEquiv_apply, Complex.norm_real, Real.norm_of_nonneg (w.positive _).le]
  simp only [he₁] at hs₁ hb₁
  simp only [he₂] at hs₂ hb₂
  rw [← WeightedCoeff.weightEquiv_fourierTail, ← WeightedCoeff.norm_eq] at hb₁ hb₂
  have he : (fun n : ℤ => if N ≤ n.natAbs then resonantLeadingPower w φ n else 0) =
      (fun n : ℤ => if N ≤ n.natAbs then (w (2*n)*‖φ.fst.val (-(2*n))‖)^p.toReal else 0) +
      (fun n : ℤ => if N ≤ n.natAbs then (w (2*n)*‖φ.snd.val (2*n)‖)^p.toReal else 0) := by
    funext n
    by_cases hn : N ≤ n.natAbs <;> simp [resonantLeadingPower, hn]
  rw [he]
  refine ⟨hs₁.add hs₂, ?_⟩
  exact (hs₁.tsum_add hs₂).le.trans ((add_le_add hb₁ hb₂).trans_eq
    (norm_withLp_prod_rpow hp (weightedPairFourierTail w.toWeight M φ)).symm)

end NLS.ZakharovShabat
