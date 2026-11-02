import NLS.KdV.ClassicalUniformCriticalBasis
import NLS.KdV.ClassicalCriticalPeriods
import NLS.KdV.FreeHighContourPeriods
import NLS.KdV.ClassicalHighContourMoments

/-! # The actual infinite period matrix on one potential neighborhood

A finite head uses the proved free isolating energy circles. The infinite
tail uses the quadratic images of the fixed frequency circles C(k*pi,pi/4).
Every entry is analytic on the same complex potential neighborhood, chosen
before either matrix index, and the whole free matrix is the identity.
Bounded operator realization and inversion are separate obligations.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

/-- Actual high period, including the energy Jacobian and source normalization. -/
def classicalHillUniformHighPeriod (N : ℕ) (n k : ℕ+)
    (q : NLS.LinearVolterra.Curve ℂ) : ℂ :=
  (2*(Real.pi : ℂ))⁻¹ * ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
    (classicalHillUniformNumerator N n (z^2,q)/classicalHillContinuedRoot (z^2,q))*(2*z)

/-- One compatible family: finitely many energy circles and a uniform high tail. -/
def classicalHillUniformPeriod (N : ℕ) (n k : ℕ+)
    (q : NLS.LinearVolterra.Curve ℂ) : ℂ :=
  if (k : ℕ) ≤ N then
    (2*(Real.pi : ℂ))⁻¹ * ∮ z in C(freeHillEnergy k,classicalHillFreeFrequencyRadius k),
      classicalHillUniformNumerator N n (z,q)/classicalHillContinuedRoot (z,q)
  else classicalHillUniformHighPeriod N n k q

/-- The high entry is exactly the one-form integral over the mapped energy
contour. No change of orientation or normalization is hidden in the pullback. -/
theorem classicalHillUniformHighPeriod_eq_curveIntegral (N : ℕ) (n k : ℕ+)
    (q : NLS.LinearVolterra.Curve ℂ) :
    classicalHillUniformHighPeriod N n k q = (2*(Real.pi : ℂ))⁻¹ *
      ∫ᶜ z in classicalHillHighEnergyContour k,
        holomorphicOneForm (fun z =>
          classicalHillUniformNumerator N n (z,q)/classicalHillContinuedRoot (z,q)) z := by
  let f : ℂ → ℂ := fun z =>
    classicalHillUniformNumerator N n (z,q)/classicalHillContinuedRoot (z,q)
  have hsq (z : ℂ) : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by
    simpa using! (hasDerivAt_id z).pow 2
  have hp := (holomorphicPathPullback_integral_and_integrability f
    (fun z => f (z^2)*(2*z)) (fun z : ℂ => z^2) (fun z : ℂ => 2*z) (continuous_id.pow 2)
    (circlePath ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4))
    ((circlePath_contDiffOn _ _).of_le (by norm_num))
    (fun _ _ => hsq _) (fun _ _ => rfl)).2
  rw [curveIntegral_circlePath] at hp
  change (2*(Real.pi : ℂ))⁻¹ *
    (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4), f (z^2)*(2*z)) = _
  rw [← hp]
  rfl

/-- Only a finite intersection is needed for the low contours. -/
theorem exists_classicalHill_low_contour_neighborhood (N : ℕ) :
    ∃ V : Set (NLS.LinearVolterra.Curve ℂ), IsOpen V ∧ 0 ∈ V ∧
      ∀ k : ℕ+, (k : ℕ) ≤ N → ∀ q ∈ V,
        ∀ z ∈ sphere (freeHillEnergy k) (classicalHillFreeFrequencyRadius k),
          (z,q) ∈ classicalHillContinuationDomain := by
  have hex (k : ℕ+) := exists_classicalHillContinuation_neighborhood
    (sphere (freeHillEnergy k) (classicalHillFreeFrequencyRadius k)) (isCompact_sphere _ _) 0
    (classicalHillFreeContour_in_continuationDomain k)
  let W (k : ℕ+) := Classical.choose (hex k)
  have hW (k : ℕ+) := Classical.choose_spec (hex k)
  let U : Fin (N+1) → Set (NLS.LinearVolterra.Curve ℂ) := fun i =>
    if hi : 0 < i.val then W ⟨i.val,hi⟩ else univ
  have hU (i : Fin (N+1)) : IsOpen (U i) ∧ (0 : NLS.LinearVolterra.Curve ℂ) ∈ U i := by
    by_cases hi : 0 < i.val
    · simpa only [U,dif_pos hi] using ⟨(hW ⟨i.val,hi⟩).1,(hW ⟨i.val,hi⟩).2.1⟩
    · simp only [U,dif_neg hi]
      exact ⟨isOpen_univ,mem_univ _⟩
  refine ⟨⋂ i, U i,isOpen_iInter_of_finite (fun i => (hU i).1),
    mem_iInter.mpr (fun i => (hU i).2),?_⟩
  intro k hk q hq z hz
  have hqW := mem_iInter.mp hq (⟨(k : ℕ),Nat.lt_succ_of_le hk⟩ : Fin (N+1))
  have hqw : q ∈ W k := by simpa only [U,dif_pos k.pos] using! hqW
  exact (hW k).2.2 ⟨hz,hqw⟩

/-- Both matrix indices are quantified after one neighborhood. This is
scalar-entry analyticity, not a bounded-operator analyticity assertion. -/
theorem exists_analytic_classicalHill_uniform_period_entries :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ), 0 < N ∧ IsOpen V ∧ 0 ∈ V ∧
      (∀ n : ℕ+, ∀ q ∈ V, ∀ lam : ℂ,
        (lam-classicalHillUniformCriticalPoint N n q)*classicalHillUniformNumerator N n (lam,q) =
          (2*(n : ℂ)*Real.pi)*deriv (classicalHillDiscriminant q) lam) ∧
      ∀ n k : ℕ+, AnalyticOnNhd ℂ (classicalHillUniformPeriod N n k) V ∧
        classicalHillUniformPeriod N n k 0 = if n = k then 1 else 0 := by
  obtain ⟨N,W,hN,hW,h0W,hB,hhigh⟩ := exists_classicalHill_uniform_numerator_basis
  obtain ⟨U,hU,h0U,hlow⟩ := exists_classicalHill_low_contour_neighborhood N
  let V := W ∩ U
  have hV : IsOpen V := hW.inter hU
  let D := classicalHillContinuationDomain ∩ (univ ×ˢ W)
  have hD : IsOpen D := isOpen_classicalHillContinuationDomain.inter (isOpen_univ.prod hW)
  have hI (n : ℕ+) : AnalyticOnNhd ℂ (fun t : ℂ × NLS.LinearVolterra.Curve ℂ =>
      classicalHillUniformNumerator N n t/classicalHillContinuedRoot t) D := by
    apply ((hB n).1.mono inter_subset_right).div
      (analyticOnNhd_classicalHillContinuedRoot.mono inter_subset_left)
    intro t ht
    exact classicalHillContinuedRoot_ne_zero t ht.1
  have hpi : (2*(Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  refine ⟨N,V,hN,hV,⟨h0W,h0U⟩,fun n q hq => ((hB n).2.2 q hq.1).1,?_⟩
  intro n k
  by_cases hk : (k : ℕ) ≤ N
  · have he : classicalHillUniformPeriod N n k = fun q =>
        (2*(Real.pi : ℂ))⁻¹ * ∮ z in C(freeHillEnergy k,classicalHillFreeFrequencyRadius k),
          classicalHillUniformNumerator N n (z,q)/classicalHillContinuedRoot (z,q) := by
      funext q
      exact if_pos hk
    rw [he]
    have hi := analyticOnNhd_circleIntegral_of_jointAnalytic _ hD (hI n)
      (freeHillEnergy k) (classicalHillFreeFrequencyRadius k)
      (Classical.choose_spec (exists_classicalHillFreePsi_periods k)).1.le hV
      (fun q hq z hz => ⟨hlow k hk q hq.2 z hz,mem_univ _,hq.1⟩)
    refine ⟨analyticOnNhd_const.mul hi,?_⟩
    have hfree := classicalHillFreeFrequencyMoment_zeroth n k
    simp only [classicalHillFreeFrequencyMoment,frequencyMoment,pow_zero,one_mul] at hfree
    simp only [(hB n).2.1,classicalHillContinuedRoot_base,hfree]
    split_ifs
    · exact inv_mul_cancel₀ hpi
    · exact mul_zero _
  · have he : classicalHillUniformPeriod N n k = classicalHillUniformHighPeriod N n k := by
      funext q
      exact if_neg hk
    rw [he]
    let T : ℂ × NLS.LinearVolterra.Curve ℂ → ℂ × NLS.LinearVolterra.Curve ℂ :=
      fun t => (t.1^2,t.2)
    have hT : Continuous T := by fun_prop
    have hG : AnalyticOnNhd ℂ (fun t : ℂ × NLS.LinearVolterra.Curve ℂ =>
        (classicalHillUniformNumerator N n (t.1^2,t.2)/
          classicalHillContinuedRoot (t.1^2,t.2))*(2*t.1)) (T ⁻¹' D) := by
      intro t ht
      exact ((hI n (T t) ht).comp
        (f := T) ((analyticAt_fst.pow 2).prod analyticAt_snd)).mul
          (analyticAt_const.mul analyticAt_fst)
    have hi := analyticOnNhd_circleIntegral_of_jointAnalytic _ (hD.preimage hT) hG
      ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) (by positivity) hV
      (fun q hq z hz => ⟨hhigh k (Nat.lt_of_not_ge hk) q hq.1 z hz,mem_univ _,hq.1⟩)
    refine ⟨analyticOnNhd_const.mul hi,?_⟩
    unfold classicalHillUniformHighPeriod
    simp only [(hB n).2.1,classicalHillContinuedRoot_base,
      circleIntegral_classicalHillFreePsi_frequency]
    split_ifs
    · exact inv_mul_cancel₀ hpi
    · exact mul_zero _

end NLS.KdV
