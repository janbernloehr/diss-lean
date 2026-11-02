import NLS.KdV.HillHminusOneCriticalPoints
import NLS.KdV.HillHminusOneAnnulusCoverage
import NLS.ComplexAnalysis.AnalyticSimpleCriticalBranch
import NLS.ComplexAnalysis.ParametricDividedDifference

/-! # An actual entire critical numerator basis in the complex Hminus1 norm

Finitely many implicit critical charts join the uniform actual Miura tail.
One rough-open neighborhood precedes all positive basis indices.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminus_local_critical_point (n : ℕ+) :
    ∃ mu : PeriodOneHminusOne → ℂ, ∃ V : Set PeriodOneHminusOne,
      IsOpen V ∧ 0 ∈ V ∧ mu 0 = freeHillEnergy n ∧ AnalyticOnNhd ℂ mu V ∧
        ∀ q ∈ V, deriv (hillHminusDiscriminant q) (mu q) = 0 ∧
          deriv (deriv (hillHminusDiscriminant q)) (mu q) ≠ 0 := by
  have he : hillHminusDiscriminant 0 = classicalHillDiscriminant 0 := by
    funext lambda
    rw [hillHminusDiscriminant_zero,classicalHillDiscriminant_zero]
  apply exists_analytic_simple_critical_branch
    (fun t : ℂ × PeriodOneHminusOne => hillHminusDiscriminant t.2 t.1)
    analyticOnNhd_hillHminusDiscriminant_joint (freeHillEnergy n) 0
  · change deriv (hillHminusDiscriminant 0) (freeHillEnergy n) = 0
    rw [he]
    exact deriv_classicalHillDiscriminant_free_energy n
  · change deriv (deriv (hillHminusDiscriminant 0)) (freeHillEnergy n) ≠ 0
    rw [he]
    exact deriv_deriv_classicalHillDiscriminant_free_energy_ne_zero n

def hillHminusLocalCriticalPoint (n : ℕ+) : PeriodOneHminusOne → ℂ :=
  (exists_hillHminus_local_critical_point n).choose

def hillHminusLocalCriticalDomain (n : ℕ+) : Set PeriodOneHminusOne :=
  (exists_hillHminus_local_critical_point n).choose_spec.choose

theorem hillHminusLocalCritical_spec (n : ℕ+) :
    IsOpen (hillHminusLocalCriticalDomain n) ∧ 0 ∈ hillHminusLocalCriticalDomain n ∧
      hillHminusLocalCriticalPoint n 0 = freeHillEnergy n ∧
      AnalyticOnNhd ℂ (hillHminusLocalCriticalPoint n) (hillHminusLocalCriticalDomain n) ∧
      ∀ q ∈ hillHminusLocalCriticalDomain n,
        deriv (hillHminusDiscriminant q) (hillHminusLocalCriticalPoint n q) = 0 ∧
        deriv (deriv (hillHminusDiscriminant q)) (hillHminusLocalCriticalPoint n q) ≠ 0 :=
  (exists_hillHminus_local_critical_point n).choose_spec.choose_spec

def hillHminusUniformCriticalPoint (C : HillHminusMiuraChart) (N : ℕ) (n : ℕ+)
    (q : PeriodOneHminusOne) : ℂ :=
  if (n : ℕ) ≤ N then hillHminusLocalCriticalPoint n q else C.energyCritical q n

/-- Uniform rough-open critical branches with exact free energies and
actual source-sheet coverage of every sufficiently high fixed contour. -/
theorem exists_hillHminus_uniform_critical_family :
    ∃ C : HillHminusMiuraChart, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < N ∧ IsOpen V ∧ 0 ∈ V ∧ V ⊆ C.domain ∧
      (∀ n : ℕ+, hillHminusUniformCriticalPoint C N n 0 = freeHillEnergy n ∧
        AnalyticOnNhd ℂ (hillHminusUniformCriticalPoint C N n) V ∧
        ∀ q ∈ V,
          deriv (hillHminusDiscriminant q) (hillHminusUniformCriticalPoint C N n q) = 0 ∧
          deriv (deriv (hillHminusDiscriminant q)) (hillHminusUniformCriticalPoint C N n q) ≠ 0) ∧
      ∀ n : ℕ+, N < (n : ℕ) → ∀ q ∈ V,
        ∀ z ∈ sphere ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4),
          (z^2,q) ∈ hillHminusContinuationDomain := by
  obtain ⟨C,Nc,Wc,hNc,hWc,h0Wc,hWcC,hc⟩ := exists_hillHminus_high_critical_points_free
  obtain ⟨Na,Wa,_,hWa,h0Wa,hcover⟩ :=
    exists_hillHminus_high_annulus_neighborhood 0 (Real.pi/4) (by positivity)
  let N := max Nc Na
  let U : Fin (N+1) → Set PeriodOneHminusOne := fun i =>
    if hi : 0 < i.val then hillHminusLocalCriticalDomain ⟨i.val,hi⟩ else univ
  have hU (i : Fin (N+1)) : IsOpen (U i) ∧ (0 : PeriodOneHminusOne) ∈ U i := by
    by_cases hi : 0 < i.val
    · simpa only [U,dif_pos hi] using
        ⟨(hillHminusLocalCritical_spec ⟨i.val,hi⟩).1,(hillHminusLocalCritical_spec ⟨i.val,hi⟩).2.1⟩
    · simp only [U,dif_neg hi]
      exact ⟨isOpen_univ,mem_univ _⟩
  let V := (Wc ∩ Wa) ∩ ⋂ i, U i
  have hV : IsOpen V := (hWc.inter hWa).inter (isOpen_iInter_of_finite fun i => (hU i).1)
  have h0V : (0 : PeriodOneHminusOne) ∈ V := ⟨⟨h0Wc,h0Wa⟩,mem_iInter.mpr (fun i => (hU i).2)⟩
  have hlow (n : ℕ+) (hn : (n : ℕ) ≤ N) : V ⊆ hillHminusLocalCriticalDomain n := by
    intro q hq
    have hi := mem_iInter.mp hq.2 (⟨(n : ℕ),Nat.lt_succ_of_le hn⟩ : Fin (N+1))
    simpa only [U,dif_pos n.pos] using! hi
  refine ⟨C,N,V,hNc.trans_le (le_max_left _ _),hV,h0V,fun _ hq => hWcC hq.1.1,?_,?_⟩
  · intro n
    by_cases hn : (n : ℕ) ≤ N
    · have he : hillHminusUniformCriticalPoint C N n = hillHminusLocalCriticalPoint n := by
        funext q
        exact if_pos hn
      rw [he]
      obtain ⟨_,_,hfree,han,hcrit⟩ := hillHminusLocalCritical_spec n
      exact ⟨hfree,han.mono (hlow n hn),fun q hq => hcrit q (hlow n hn hq)⟩
    · have hnn : Nc < (n : ℕ) := (le_max_left _ _).trans_lt (Nat.lt_of_not_ge hn)
      have he : hillHminusUniformCriticalPoint C N n = (fun q => C.energyCritical q n) := by
        funext q
        exact if_neg hn
      rw [he]
      exact ⟨(hc n hnn).1,(hc n hnn).2.1.mono (fun _ hq => hq.1.1),fun q hq => (hc n hnn).2.2 q hq.1.1⟩
  intro n hn q hq z hz
  exact hcover q hq.1.2 n ((le_max_right _ _).trans hn.le) z (sphere_subset_closedBall hz)
    (mem_sphere_iff_norm.mp hz).ge

def hillHminusUniformNumerator (C : HillHminusMiuraChart) (N : ℕ) (n : ℕ+)
    (t : ℂ × PeriodOneHminusOne) : ℂ :=
  (2*(n : ℂ)*Real.pi)*parametricMovingDividedDifference
    hillHminusDiscriminantDerivative (hillHminusUniformCriticalPoint C N n) t

/-- An entire actual critical numerator basis on one Hminus1-open
neighborhood. Its filled critical centers are nonzero and its free slice
is exactly the original normalized free numerator, before all indices. -/
theorem exists_hillHminus_uniform_numerator_basis :
    ∃ C : HillHminusMiuraChart, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < N ∧ IsOpen V ∧ 0 ∈ V ∧ V ⊆ C.domain ∧
      (∀ n : ℕ+, hillHminusUniformCriticalPoint C N n 0 = freeHillEnergy n ∧
        AnalyticOnNhd ℂ (hillHminusUniformCriticalPoint C N n) V ∧
        ∀ q ∈ V, deriv (hillHminusDiscriminant q) (hillHminusUniformCriticalPoint C N n q) = 0 ∧
          deriv (deriv (hillHminusDiscriminant q)) (hillHminusUniformCriticalPoint C N n q) ≠ 0) ∧
      (∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusUniformNumerator C N n) (univ ×ˢ V) ∧
        (∀ z : ℂ, hillHminusUniformNumerator C N n (z,0) = classicalHillFreePsi n z) ∧
        ∀ q ∈ V,
          (∀ z : ℂ, (z-hillHminusUniformCriticalPoint C N n q)*hillHminusUniformNumerator C N n (z,q) =
            (2*(n : ℂ)*Real.pi)*deriv (hillHminusDiscriminant q) z) ∧
          hillHminusUniformNumerator C N n (hillHminusUniformCriticalPoint C N n q,q) ≠ 0) ∧
      ∀ n : ℕ+, N < (n : ℕ) → ∀ q ∈ V,
        ∀ z ∈ sphere ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4),
          (z^2,q) ∈ hillHminusContinuationDomain := by
  obtain ⟨C,N,V,hN,hV,h0V,hVC,hcritical,hcover⟩ := exists_hillHminus_uniform_critical_family
  have hF : AnalyticOnNhd ℂ hillHminusDiscriminantDerivative (univ ×ˢ V) :=
    analyticOnNhd_hillHminusDiscriminantDerivative.mono (subset_univ _)
  have hfree : (fun z => hillHminusDiscriminantDerivative (z,0)) = (fun z => classicalHillDiscriminantDerivative (z,0)) := by
    funext z
    change deriv (hillHminusDiscriminant 0) z = deriv (classicalHillDiscriminant 0) z
    congr 1
    funext w
    rw [hillHminusDiscriminant_zero,classicalHillDiscriminant_zero]
  refine ⟨C,N,V,hN,hV,h0V,hVC,hcritical,?_,hcover⟩
  intro n
  obtain ⟨hmu0,hmu,hcrit⟩ := hcritical n
  have hB := analyticOnNhd_parametricMovingDividedDifference _ _ hV hF hmu
  refine ⟨analyticOnNhd_const.mul hB,?_,?_⟩
  · intro z
    rw [hillHminusUniformNumerator,parametricMovingDividedDifference_eq_dslope _ _ hF hmu z 0 h0V,hmu0]
    change (2*(n : ℂ)*Real.pi)*dslope ((fun z => hillHminusDiscriminantDerivative (z,0))) (freeHillEnergy n) z = _
    rw [hfree]
    rfl
  intro q hq
  constructor
  · intro z
    have he := parametricMovingDividedDifference_mul _ _ hF hmu z q hq
    change (z-hillHminusUniformCriticalPoint C N n q)*parametricMovingDividedDifference _ _ (z,q) =
      deriv (hillHminusDiscriminant q) z-deriv (hillHminusDiscriminant q) (hillHminusUniformCriticalPoint C N n q) at he
    rw [(hcrit q hq).1,sub_zero] at he
    dsimp only [hillHminusUniformNumerator]
    linear_combination (2*(n : ℂ)*Real.pi)*he
  · dsimp only [hillHminusUniformNumerator]
    rw [parametricMovingDividedDifference_center _ _ hF q hq]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast n.ne_zero)) (by exact_mod_cast Real.pi_ne_zero)) (hcrit q hq).2

end NLS.KdV
