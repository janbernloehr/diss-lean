import NLS.SequenceSpaces.UniformHolderTails
import Mathlib.Order.Filter.AtTopBot.Interval

/-!
# Absolute and uniform convergence under two Hölder bounds

Two actual coefficient sequences may contribute to a scalar majorant.
For a fixed finite-exponent multiplier, bounded families have uniformly
small absolute tails and their symmetric sums converge uniformly.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] in
/-- A sum of two Hölder majorants gives absolute convergence and a
quantitative bound for the complete absolute sum. -/
theorem summable_norm_of_two_holder_bounds
    (hc : p.toReal.HolderConjugate q.toReal) (a d : Coeff p) (b : Coeff q)
    (u : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ m, ‖u m‖ ≤ C * (‖a m‖ + ‖d m‖) * ‖b m‖) :
    Summable (fun m => ‖u m‖) ∧
      (∑' m, ‖u m‖) ≤ C * (‖a‖ + ‖d‖) * ‖b‖ := by
  have ha := lp.tsum_mul_le_mul_norm hc a b
  have hd := lp.tsum_mul_le_mul_norm hc d b
  have hs : Summable (fun m => C * (‖a m‖ * ‖b m‖ + ‖d m‖ * ‖b m‖)) :=
    (ha.1.add hd.1).mul_left C
  have hdom (m : ℤ) : ‖u m‖ ≤ C * (‖a m‖ * ‖b m‖ + ‖d m‖ * ‖b m‖) := by
    convert hu m using 1
    ring
  have habs := hs.of_nonneg_of_le (fun m => norm_nonneg _) hdom
  refine ⟨habs, (habs.tsum_le_tsum hdom hs).trans ?_⟩
  rw [tsum_mul_left, ha.1.tsum_add hd.1]
  calc
    _ ≤ C * (‖a‖ * ‖b‖ + ‖d‖ * ‖b‖) :=
      mul_le_mul_of_nonneg_left (add_le_add ha.2 hd.2) hC
    _ = _ := by ring

/-- Uniform absolute tail estimates make symmetric scalar sums
uniformly Cauchy, without assumptions on individual terms. -/
theorem uniformCauchySeqOn_sum_of_absolute_tails {X : Type*}
    (u : X → ℤ → ℂ) (S : Set X) (D : ℕ → ℝ)
    (hD : Tendsto D atTop (𝓝 0))
    (htail : ∀ N : ℕ, ∀ x ∈ S, ∀ s : Finset ℤ,
      (∀ m ∈ s, N ≤ m.natAbs) → (∑ m ∈ s, ‖u x m‖) ≤ D N) :
    UniformCauchySeqOn
      (fun (N : ℕ) x => ∑ m ∈ Finset.Icc (-(N : ℤ)) N, u x m) atTop S := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hD.eventually (gt_mem_nhds hε))
  refine ⟨N,fun i hi j hj x hx => ?_⟩
  have hle (a b : ℕ) (hab : a ≤ b) (ha : N ≤ a) :
      dist (∑ m ∈ Finset.Icc (-(b : ℤ)) b, u x m)
        (∑ m ∈ Finset.Icc (-(a : ℤ)) a, u x m) < ε := by
    have hs : Finset.Icc (-(a : ℤ)) a ⊆ Finset.Icc (-(b : ℤ)) b := by
      intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      constructor <;> omega
    rw [dist_eq_norm, ← Finset.sum_sdiff hs, add_sub_cancel_right]
    apply (norm_sum_le _ _).trans_lt
    apply (htail N x hx _ ?_).trans_lt (hN N le_rfl)
    intro m hm
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hm
    omega
  rcases le_total i j with hij | hji
  · rw [dist_comm]
    exact hle i j hij hi
  · exact hle j i hji hj

/-- A fixed finite-exponent multiplier gives uniform convergence
control for sums dominated by two norm-bounded coefficient families. -/
theorem uniformCauchySeqOn_two_holder_sums {X : Type*}
    (a d : X → Coeff p) (b : Coeff q) (hq : q ≠ ⊤)
    (u : X → ℤ → ℂ) (S : Set X) (C R : ℝ) (hC : 0 ≤ C)
    (had : ∀ x ∈ S, ‖a x‖ + ‖d x‖ ≤ R)
    (hu : ∀ x ∈ S, ∀ m, ‖u x m‖ ≤ C * (‖a x m‖ + ‖d x m‖) * ‖b m‖) :
    UniformCauchySeqOn
      (fun (N : ℕ) x => ∑ m ∈ Finset.Icc (-(N : ℤ)) N, u x m) atTop S := by
  apply uniformCauchySeqOn_sum_of_absolute_tails u S
    (fun N => C * R * ‖fourierTail N b‖)
    (by simpa using tendsto_const_nhds.mul ((tendsto_fourierTail hq b).norm))
  intro N x hx s hs
  have hsum : (∑ m ∈ s, ‖u x m‖) ≤
      C * ((∑ m ∈ s, ‖a x m * b m‖) + (∑ m ∈ s, ‖d x m * b m‖)) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro m _
    simpa only [norm_mul, mul_add, add_mul, mul_assoc] using hu x hx m
  calc
    _ ≤ C * ((∑ m ∈ s, ‖a x m * b m‖) + (∑ m ∈ s, ‖d x m * b m‖)) := hsum
    _ ≤ C * (‖a x‖ * ‖fourierTail N b‖ + ‖d x‖ * ‖fourierTail N b‖) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (sum_norm_holderProduct_tail_le (a x) b N s hs)
        (sum_norm_holderProduct_tail_le (d x) b N s hs)) hC
    _ = C * (‖a x‖ + ‖d x‖) * ‖fourierTail N b‖ := by ring
    _ ≤ C * R * ‖fourierTail N b‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (had x hx) hC) (norm_nonneg _)

end NLS.Coeff
