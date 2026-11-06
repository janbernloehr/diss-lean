import NLS.KdV.HillHminusOneCanonicalTailLocalization
import NLS.KdV.HillHminusOneRealGapContours
import NLS.ComplexAnalysis.RealGapCircleNesting

/-! # Uniform nesting of the actual H^-1 high integration circles

The small canonical tail errors and the quadratic free-energy spacing
force large adjacent bands. The standard free-centered source circle
then lies inside the canonical midpoint circle, and both enclose exactly
the same actual gap cut.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem freeHillValue_prev_spacing_ge_ten (n : ℕ) (hn : 2 ≤ n) :
    10*(n : ℝ) ≤ freeHillValue n-freeHillValue (n-1 : ℕ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi : 9 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hmul := mul_le_mul_of_nonneg_right hpi (show 0 ≤ 2*(n : ℝ)-1 by linarith)
  have he : freeHillValue n-freeHillValue (n-1 : ℕ) = Real.pi^2*(2*(n : ℝ)-1) := by
    simp only [freeHillValue,Int.cast_natCast,Nat.cast_sub (show 1 ≤ n by omega),Nat.cast_one]
    push_cast
    ring
  rw [he]
  nlinarith

theorem freeHillValue_next_spacing_ge_ten (n : ℕ) (hn : 2 ≤ n) :
    10*(n : ℝ) ≤ freeHillValue (n+1 : ℕ)-freeHillValue n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi : 9 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hmul := mul_le_mul_of_nonneg_right hpi (show 0 ≤ 2*(n : ℝ)+1 by linarith)
  have he : freeHillValue (n+1 : ℕ)-freeHillValue n = Real.pi^2*(2*(n : ℝ)+1) := by
    simp only [freeHillValue,Int.cast_natCast,Nat.cast_add,Nat.cast_one]
    push_cast
    ring
  rw [he]
  nlinarith

theorem hillHminus_tail_circle_nesting_of_localization
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (N n : ℕ)
    (hN : 2 ≤ N) (hn : N+1 ≤ n)
    (hloc : ∀ k : ℕ, N ≤ k →
      |hillHminusRealLabels q hr (2*k-1)-freeHillValue k| ≤ (k : ℝ)/8 ∧
      |hillHminusRealLabels q hr (2*k)-freeHillValue k| ≤ (k : ℝ)/8) :
    closedBall (freeHillValue n : ℂ) (n : ℝ) ⊆
        closedBall (hillHminusRealGapCenter q hr n : ℂ)
          (hillHminusRealGapHalfLength q hr n+hillHminusRealGapCollar q hr n) ∧
      segment ℝ (hillHminusRealLabels q hr (2*n-1) : ℂ) (hillHminusRealLabels q hr (2*n) : ℂ) ⊆
        ball (freeHillValue n : ℂ) (n : ℝ) := by
  have hn2 : 2 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨ha,hb⟩ := hloc n (by omega)
  have hprev := (hloc (n-1) (by omega)).2
  have hnext := (hloc (n+1) (by omega)).1
  have hcastPrev : ((n-1 : ℕ) : ℝ) = (n : ℝ)-1 := by
    rw [Nat.cast_sub (show 1 ≤ n by omega),Nat.cast_one]
  have hcastNext : ((n+1 : ℕ) : ℝ) = (n : ℝ)+1 := by push_cast; rfl
  rw [show 2*(n-1)=2*n-2 by omega,hcastPrev] at hprev
  rw [show 2*(n+1)-1=2*n+1 by omega,hcastNext] at hnext
  have hleft : 8*(n : ℝ) ≤ hillHminusRealLabels q hr (2*n-1)-hillHminusRealLabels q hr (2*n-2) := by
    have h₁ := abs_le.mp ha
    have h₂ := abs_le.mp hprev
    have hgap := freeHillValue_prev_spacing_ge_ten n hn2
    linarith
  have hright : 8*(n : ℝ) ≤ hillHminusRealLabels q hr (2*n+1)-hillHminusRealLabels q hr (2*n) := by
    have h₁ := abs_le.mp hb
    have h₂ := abs_le.mp hnext
    have hgap := freeHillValue_next_spacing_ge_ten n hn2
    linarith
  have he := real_gap_comparison_circle_nesting (freeHillValue n)
    (hillHminusRealLabels q hr (2*n-2)) (hillHminusRealLabels q hr (2*n-1))
    (hillHminusRealLabels q hr (2*n)) (hillHminusRealLabels q hr (2*n+1)) (n : ℝ) hnpos
    (monotone_hillHminusRealLabels q hr (show 2*n-1 ≤ 2*n by omega)) ha hb hleft hright
  simpa only [hillHminusRealGapCenter,hillHminusRealGapHalfLength,hillHminusRealGapCollar] using he

end NLS.KdV
