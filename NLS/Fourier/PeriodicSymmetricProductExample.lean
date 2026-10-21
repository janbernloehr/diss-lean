import NLS.Fourier.PeriodicDistributionConvolutionProduct
import Mathlib.Analysis.PSeries

/-! # Symmetric convergence is strictly weaker for original Fourier products -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.Fourier

theorem harmonicCoefficient_polynomial :
    Asymptotics.IsBigO cofinite (fun k : ℤ => (k:ℂ)⁻¹) (fun k : ℤ => |(k:ℝ)|^0) := by
  apply polynomial_isBigO_of_bracket_bound _ 0 1 (by norm_num)
  intro k
  simp only [pow_zero,mul_one,norm_inv]
  by_cases hk : k = 0
  · simp [hk]
  · have h : (1:ℝ) ≤ |(k:ℝ)| := by exact_mod_cast Int.one_le_abs hk
    simpa only [Complex.norm_intCast] using inv_le_one_of_one_le₀ h

theorem harmonicCoefficient_symmetric_sum (N : ℕ) :
    (∑ k ∈ Finset.Icc (-(N:ℤ)) N, (k:ℂ)⁻¹) = 0 := by
  have he : (∑ k ∈ Finset.Icc (-(N:ℤ)) N, (k:ℂ)⁻¹) =
      ∑ k ∈ Finset.Icc (-(N:ℤ)) N, ((-k:ℤ):ℂ)⁻¹ := by
    apply Finset.sum_bij (fun k _ => -k)
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    · intro a ha b hb he
      omega
    · intro b hb
      refine ⟨-b,?_,by simp⟩
      simp only [Finset.mem_Icc] at hb ⊢
      omega
    · intro k hk
      simp
  simp only [Int.cast_neg,inv_neg,Finset.sum_neg_distrib] at he
  have htwo : (2:ℂ) * (∑ k ∈ Finset.Icc (-(N:ℤ)) N, (k:ℂ)⁻¹) = 0 := by
    linear_combination he
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem harmonicCoefficient_not_summable : ¬ Summable (fun k : ℤ => (k:ℂ)⁻¹) := by
  intro h
  have hs : Summable (fun n : ℕ => ((n:ℤ):ℂ)⁻¹) := h.comp_injective
    (by intro a b hab; change (a:ℤ) = (b:ℤ) at hab; omega : Function.Injective (fun n : ℕ => (n:ℤ)))
  have hr := Complex.reCLM.summable hs
  apply Real.not_summable_natCast_inv
  simpa using hr

namespace SmoothPeriodicTest.Distribution
variable {L : ℝ} [Fact (0 < L)]

def harmonicDistribution : Distribution L :=
  Classical.choose (existsUnique_of_polynomial_isBigO (L := L) (fun k : ℤ => (k:ℂ)⁻¹) 0
    harmonicCoefficient_polynomial)

@[simp] theorem harmonicDistribution_coefficient (n : ℤ) :
    harmonicDistribution (L := L) (mode (-n)) = (n:ℂ)⁻¹ :=
  (Classical.choose_spec (existsUnique_of_polynomial_isBigO (L := L) _ 0
    harmonicCoefficient_polynomial)).1 n

theorem hasSymmetricFourierProduct_evaluation_harmonic :
    HasSymmetricFourierProduct (evaluation (L := L) 0) harmonicDistribution 0 := by
  intro n
  simp only [evaluation_zero_coefficient,harmonicDistribution_coefficient,one_mul,
    harmonicCoefficient_symmetric_sum]
  exact tendsto_const_nhds

theorem not_hasFourierProduct_evaluation_harmonic (w : Distribution L) :
    ¬ HasFourierProduct (evaluation (L := L) 0) harmonicDistribution w := by
  intro h
  apply harmonicCoefficient_not_summable
  simpa only [evaluation_zero_coefficient,harmonicDistribution_coefficient,one_mul] using (h 0).summable

end SmoothPeriodicTest.Distribution
end NLS.Fourier
