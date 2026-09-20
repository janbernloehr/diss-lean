import NLS.ZakharovShabat.CriticalRootCounts
import NLS.ComplexAnalysis.RealDiameterDiscs

/-!
# Real barriers for critical-root counts

Enlarging a cutoff strictly puts every central label in the interior.
A real diameter whose endpoints avoid the labels has a zero-free boundary
at a real-type potential, so it can be used in Rouché count comparisons.
-/

noncomputable section
open Set Complex Metric
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : PairSpace p} {hφ : φ ∈ pairParitySubspace 0}
variable {N : ℕ} {ξ : ℤ → ℂ}

/-- At a strictly larger cutoff every central label is strictly inside the disc. -/
theorem CriticalPointLabeling.norm_lt_larger_centralRadius
    (h : CriticalPointLabeling hp hp1 φ hφ N ξ) (K : ℕ) (hK : N < K)
    (n : ℤ) (hn : n.natAbs ≤ K) : ‖ξ n‖ < centralCircleRadius K := by
  by_cases hnN : n.natAbs ≤ N
  · have hb : ‖ξ n‖ ≤ centralCircleRadius N := by simpa using h.central_mem n hnN
    apply hb.trans_lt
    unfold centralCircleRadius
    have hc := mul_lt_mul_of_pos_right (show (N : ℝ) < (K : ℝ) by exact_mod_cast hK) Real.pi_pos
    linarith
  · have hd : ‖ξ n-(Real.pi : ℂ)*n‖ < Real.pi/4 := by
      simpa only [mem_ball, dist_eq_norm] using (h.distant n (by omega)).1
    have hc : ‖(Real.pi : ℂ)*n‖ ≤ Real.pi*K := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_intCast]
      apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      rw [← Int.cast_abs, ← Int.natCast_natAbs]
      exact_mod_cast hn
    have ht := norm_le_norm_sub_add (ξ n) ((Real.pi : ℂ)*n)
    unfold centralCircleRadius
    nlinarith [Real.pi_pos]

/-- Real endpoints avoiding all central labels give a zero-free circle at a real-type potential. -/
theorem CriticalPointLabeling.realDiameterSphere_nonzero_of_realType
    (h : CriticalPointLabeling hp hp1 φ hφ N ξ) (hreal : IsRealType φ)
    (K : ℕ) (hK : N ≤ K) (a b : ℝ)
    (ha : -centralCircleRadius K ≤ a) (hb : b ≤ centralCircleRadius K)
    (hneA : ∀ n : ℤ, n.natAbs ≤ K → (ξ n).re ≠ a)
    (hneB : ∀ n : ℤ, n.natAbs ≤ K → (ξ n).re ≠ b) :
    ∀ z ∈ sphere (((a+b)/2 : ℝ) : ℂ) ((b-a)/2), deriv (canonicalDiscriminant hp φ) z ≠ 0 := by
  intro z hz hzero
  have hc := realDiameterDisc_subset_closedBall a b (centralCircleRadius K) ha hb
    (sphere_subset_closedBall hz)
  obtain ⟨n,rfl⟩ := (h.exhaustive z).mp hzero
  have hn := (h.mem_larger_central_iff K hK n).mp hc
  have him := discriminant_critical_im_eq_zero_of_realType hp hp1 φ hφ hreal hzero
  rcases re_eq_endpoints_of_mem_realDiameterSphere a b (ξ n) him hz with he | he
  · exact hneA n hn he
  · exact hneB n hn he

end NLS.ZakharovShabat
