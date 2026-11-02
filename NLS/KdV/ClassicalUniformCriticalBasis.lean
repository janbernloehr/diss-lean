import NLS.KdV.ClassicalHighCriticalPoints
import NLS.KdV.ClassicalCriticalNumerator

/-! # An actual infinite Hill numerator basis on one neighborhood

Uniform high critical points and finitely many free simple critical charts
give one open complex potential neighborhood supporting every positive
mode. Filled division then gives an entire jointly analytic numerator for
every mode on that same neighborhood. These basis elements are not yet
the solution of the infinite period normalization equations.
-/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.KdV

/-- A finite head of free-normalized charts joined to the intrinsic high tail. -/
def classicalHillUniformCriticalPoint (N : ℕ) (n : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) : ℂ :=
  if (n : ℕ) ≤ N then classicalHillLocalCriticalPoint n q else classicalHillHighCriticalPoint q n

/-- One neighborhood precedes every positive index. The tail also retains
the actual source-root contour coverage on that neighborhood. -/
theorem exists_classicalHill_uniform_critical_family :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ), 0 < N ∧ IsOpen V ∧ 0 ∈ V ∧
      (∀ n : ℕ+, classicalHillUniformCriticalPoint N n 0 = freeHillEnergy n ∧
        AnalyticOnNhd ℂ (classicalHillUniformCriticalPoint N n) V ∧
        ∀ q ∈ V,
          deriv (classicalHillDiscriminant q) (classicalHillUniformCriticalPoint N n q) = 0 ∧
          deriv (deriv (classicalHillDiscriminant q)) (classicalHillUniformCriticalPoint N n q) ≠ 0) ∧
      ∀ n : ℕ+, N < (n : ℕ) → ∀ q ∈ V,
        ∀ z ∈ sphere ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4),
          (z^2,q) ∈ classicalHillContinuationDomain := by
  obtain ⟨N,W,hN,hW,h0W,hhigh⟩ := exists_analytic_classicalHillHighCriticalPoints 0
  let U : Fin (N+1) → Set (NLS.LinearVolterra.Curve ℂ) := fun i =>
    if hi : 0 < i.val then classicalHillLocalCriticalDomain ⟨i.val,hi⟩ else univ
  have hU (i : Fin (N+1)) : IsOpen (U i) ∧ (0 : NLS.LinearVolterra.Curve ℂ) ∈ U i := by
    by_cases hi : 0 < i.val
    · simpa only [U, dif_pos hi] using
        ⟨(classicalHillLocalCritical_spec ⟨i.val,hi⟩).1,
          (classicalHillLocalCritical_spec ⟨i.val,hi⟩).2.1⟩
    · simp only [U, dif_neg hi]
      exact ⟨isOpen_univ,mem_univ _⟩
  let V := W ∩ ⋂ i, U i
  have hV : IsOpen V := hW.inter (isOpen_iInter_of_finite fun i => (hU i).1)
  have h0V : (0 : NLS.LinearVolterra.Curve ℂ) ∈ V :=
    ⟨h0W,mem_iInter.mpr (fun i => (hU i).2)⟩
  have hlow (n : ℕ+) (hn : (n : ℕ) ≤ N) : V ⊆ classicalHillLocalCriticalDomain n := by
    intro q hq
    have hi := mem_iInter.mp hq.2 (⟨(n : ℕ),Nat.lt_succ_of_le hn⟩ : Fin (N+1))
    simpa only [U, dif_pos n.pos] using! hi
  refine ⟨N,V,hN,hV,h0V,?_,?_⟩
  · intro n
    by_cases hn : (n : ℕ) ≤ N
    · obtain ⟨_,_,hfree,han,hcrit⟩ := classicalHillLocalCritical_spec n
      have he : classicalHillUniformCriticalPoint N n = classicalHillLocalCriticalPoint n := by
        funext q
        exact if_pos hn
      rw [he]
      exact ⟨hfree,han.mono (hlow n hn),fun q hq => hcrit q (hlow n hn hq)⟩
    · have hnn : N < (n : ℕ) := Nat.lt_of_not_ge hn
      have hdata := hhigh n hnn
      have hmem : freeHillEnergy n ∈
          (fun z : ℂ => z^2) '' closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) := by
        refine ⟨(Real.pi : ℂ)*(n : ℕ),mem_closedBall_self (by positivity),?_⟩
        dsimp only [freeHillEnergy]
        push_cast
        ring
      have hfree : classicalHillHighCriticalPoint 0 n = freeHillEnergy n :=
        (((hdata.2.2 0 h0W).2.2.2.1 (freeHillEnergy n) hmem).mp
          (deriv_classicalHillDiscriminant_free_energy n)).symm
      have he : classicalHillUniformCriticalPoint N n = (fun q => classicalHillHighCriticalPoint q n) := by
        funext q
        exact if_neg hn
      rw [he]
      exact ⟨hfree,hdata.2.1.mono inter_subset_left,fun q hq =>
        ⟨(hdata.2.2 q hq.1).2.1,(hdata.2.2 q hq.1).2.2.1⟩⟩
  intro n hn q hq z hz
  exact (hhigh n hn).2.2 q hq.1 |>.2.2.2.2 z hz

/-- Entire basis numerator with the moving critical factor removed. -/
def classicalHillUniformNumerator (N : ℕ) (n : ℕ+)
    (t : ℂ × NLS.LinearVolterra.Curve ℂ) : ℂ :=
  (2*(n : ℂ)*Real.pi)*ComplexAnalysis.parametricMovingDividedDifference
    classicalHillDiscriminantDerivative (classicalHillUniformCriticalPoint N n) t

/-- An actual infinite numerator basis on a single neighborhood of zero.
Each filled center is nonzero; each entire free slice is the already
period-normalized free numerator. No infinite coefficient inverse is assumed. -/
theorem exists_classicalHill_uniform_numerator_basis :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ), 0 < N ∧ IsOpen V ∧ 0 ∈ V ∧
      (∀ n : ℕ+, AnalyticOnNhd ℂ (classicalHillUniformNumerator N n) (univ ×ˢ V) ∧
        (∀ z : ℂ, classicalHillUniformNumerator N n (z,0) = classicalHillFreePsi n z) ∧
        ∀ q ∈ V,
          (∀ z : ℂ, (z-classicalHillUniformCriticalPoint N n q)*classicalHillUniformNumerator N n (z,q) =
            (2*(n : ℂ)*Real.pi)*deriv (classicalHillDiscriminant q) z) ∧
          classicalHillUniformNumerator N n (classicalHillUniformCriticalPoint N n q,q) ≠ 0) ∧
      ∀ n : ℕ+, N < (n : ℕ) → ∀ q ∈ V,
        ∀ z ∈ sphere ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4),
          (z^2,q) ∈ classicalHillContinuationDomain := by
  obtain ⟨N,V,hN,hV,h0V,hcritical,hcover⟩ := exists_classicalHill_uniform_critical_family
  have hF : AnalyticOnNhd ℂ classicalHillDiscriminantDerivative (univ ×ˢ V) :=
    analyticOnNhd_classicalHillDiscriminantDerivative.mono (subset_univ _)
  refine ⟨N,V,hN,hV,h0V,?_,hcover⟩
  intro n
  obtain ⟨hfree,hμ,hcrit⟩ := hcritical n
  have hB := ComplexAnalysis.analyticOnNhd_parametricMovingDividedDifference _ _ hV hF hμ
  refine ⟨analyticOnNhd_const.mul hB,?_,?_⟩
  · intro z
    rw [classicalHillUniformNumerator,
      ComplexAnalysis.parametricMovingDividedDifference_eq_dslope _ _ hF hμ z 0 h0V,hfree]
    rfl
  intro q hq
  refine ⟨?_,?_⟩
  · intro z
    have he := ComplexAnalysis.parametricMovingDividedDifference_mul _ _ hF hμ z q hq
    change (z-classicalHillUniformCriticalPoint N n q)*
      ComplexAnalysis.parametricMovingDividedDifference _ _ (z,q) =
        deriv (classicalHillDiscriminant q) z-
          deriv (classicalHillDiscriminant q) (classicalHillUniformCriticalPoint N n q) at he
    rw [(hcrit q hq).1, sub_zero] at he
    dsimp only [classicalHillUniformNumerator]
    linear_combination (2*(n : ℂ)*Real.pi)*he
  · dsimp only [classicalHillUniformNumerator]
    rw [ComplexAnalysis.parametricMovingDividedDifference_center _ _ hF q hq]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast n.ne_zero)) (by exact_mod_cast Real.pi_ne_zero)) (hcrit q hq).2

end NLS.KdV
