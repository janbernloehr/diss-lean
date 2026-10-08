import NLS.ZakharovShabat.PeriodOneSobolevMomentum
import NLS.ZakharovShabat.SourceSobolevHigherActionTrace

/-! # The momentum trace and the first three physical hierarchy traces

The independently defined H¹ momentum is the second Hamiltonian. Finite-gap
density and analytic uniqueness complete the three physical trace identities
on a common complex neighborhood of all real H¹ sources.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ComplexConjugate
namespace NLS.ZakharovShabat

/-- Level two sums to half the physical momentum on every real H¹ source. -/
theorem sourceSobolev_tsum_higherAction_two (a : realTypeSobolevSourceLocus) :
    (∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n 1 (sobolevSourceInclusion a.val)) =
      periodOneSobolevMomentum a.val/2 := by
  apply sourceSobolevHigherAction_trace_of_finiteGap 1 (by norm_num) _
    (continuous_periodOneSobolevMomentum.div_const 2) ?_ a
  intro b hf
  have h := sourceFiniteGap_tsum_complexHigherActions_eq_hamiltonian (by simp) (by norm_num)
    ⟨sobolevSourceInclusion b.val,b.property⟩ hf 1
  have he := periodOneSobolevMomentum_sourceFiniteGapSobolevPair (by simp) (by norm_num)
    ⟨sobolevSourceInclusion b.val,b.property⟩ hf
  rw [sourceFiniteGapSobolevPair_sobolevSource b hf] at he
  simpa only [Nat.reduceAdd,pow_one,← he] using h

/-- The physical momentum is real on the conjugate-pair H¹ real form. -/
theorem periodOneSobolevMomentum_im_zero (a : realTypeSobolevSourceLocus) :
    (periodOneSobolevMomentum a.val).im = 0 := by
  have hc : Continuous (fun b : realTypeSobolevSourceLocus =>
      periodOneSobolevMomentum b.val - conj (periodOneSobolevMomentum b.val)) :=
    (continuous_periodOneSobolevMomentum.comp continuous_subtype_val).sub
      (continuous_conj.comp (continuous_periodOneSobolevMomentum.comp continuous_subtype_val))
  have he : periodOneSobolevMomentum a.val - conj (periodOneSobolevMomentum a.val) = 0 := by
    apply eq_of_continuousOn_of_sourceSobolevFiniteGap isOpen_univ hc.continuousOn 0 ?_ a (mem_univ _)
    intro b _ hf
    have hcal := periodOneSobolevMomentum_sourceFiniteGapSobolevPair (by simp) (by norm_num)
      ⟨sobolevSourceInclusion b.val,b.property⟩ hf
    rw [sourceFiniteGapSobolevPair_sobolevSource b hf] at hcal
    rw [hcal]
    have hi := sourceFiniteGapNLSHamiltonian_im_zero (by simp) (by norm_num)
      ⟨sobolevSourceInclusion b.val,b.property⟩ hf 1
    apply sub_eq_zero.mpr
    apply Complex.ext
    · simp
    · simp only [conj_im,hi,neg_zero]
  have hi := congrArg Complex.im he
  simp only [sub_im,conj_im,zero_im] at hi
  linarith

/-- On one complex H¹ neighborhood, all three physical trace identities
hold with their literal absolutely convergent series. -/
theorem exists_local_sourceSobolev_firstThree_trace (a : realTypeSobolevSourceLocus) :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧ a.val ∈ U ∧ ∀ b ∈ U,
      ((∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n 0 (sobolevSourceInclusion b)) =
        periodOneSobolevMass b) ∧
      ((∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n 1 (sobolevSourceInclusion b)) =
        periodOneSobolevMomentum b/2) ∧
      ((∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n 2 (sobolevSourceInclusion b)) =
        periodOneSobolevHamiltonian b/4) ∧
      ∀ k : ℕ, k ≤ 2 → Summable (fun n : ℤ =>
        ‖sourceComplexHigherAction (by simp) (by norm_num) n k (sobolevSourceInclusion b)‖) := by
  have hm := eventuallyEq_sobolev_of_analyticAt_of_real_agreement a _ _
    (analyticAt_tsum_sourceSobolevHigherAction a.val a.property 1 (by norm_num))
    (analyticAt_periodOneSobolevMomentum a.val).div_const sourceSobolev_tsum_higherAction_two
  obtain ⟨V,hV,haV,htrace⟩ := exists_local_sourceSobolevHigherAction_trace a
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hm.and (hV.mem_nhds haV))
  refine ⟨ball a.val r,isOpen_ball,mem_ball_self hr,?_⟩
  intro b hb
  have ht := htrace b (hsub hb).2
  exact ⟨ht.1,(hsub hb).1,ht.2.1,ht.2.2⟩

/-- A single open complex H¹ domain contains all real sources and carries
the mass, momentum and energy traces with factors `1`, `1/2`, and `1/4`. -/
theorem exists_sourceSobolev_firstThree_trace_domain :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧
      {a | IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))} ⊆ U ∧ ∀ b ∈ U,
      ((∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n 0 (sobolevSourceInclusion b)) =
        periodOneSobolevMass b) ∧
      ((∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n 1 (sobolevSourceInclusion b)) =
        periodOneSobolevMomentum b/2) ∧
      ((∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n 2 (sobolevSourceInclusion b)) =
        periodOneSobolevHamiltonian b/4) ∧
      ∀ k : ℕ, k ≤ 2 → Summable (fun n : ℤ =>
        ‖sourceComplexHigherAction (by simp) (by norm_num) n k (sobolevSourceInclusion b)‖) := by
  choose V hV haV htrace using exists_local_sourceSobolev_firstThree_trace
  refine ⟨⋃ a : realTypeSobolevSourceLocus, V a,isOpen_iUnion hV,?_,?_⟩
  · intro a ha
    exact mem_iUnion.mpr ⟨⟨a,ha⟩,haV ⟨a,ha⟩⟩
  · intro b hb
    obtain ⟨a,ha⟩ := mem_iUnion.mp hb
    exact htrace a b ha

end NLS.ZakharovShabat
