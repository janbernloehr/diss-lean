import NLS.ZakharovShabat.SourceSobolevHigherActionAnalytic
import NLS.ZakharovShabat.SourceSobolevHamiltonianDifferential

/-! # Mass and energy higher-action traces beyond finite-gap sources

H¹ finite-gap density and analytic ℓ¹ summation prove the physical trace
identities on every real H¹ source. Real-form uniqueness extends both to
one open complex H¹ neighborhood of the full real locus.
-/
noncomputable section
open Set Metric Filter Topology
namespace NLS.ZakharovShabat

private theorem higherAction_trace_of_finiteGap (k : ℕ) (hk : k ≤ 2)
    (H : (ScalarDomain 2 × ScalarDomain 2) → ℂ) (hH : Continuous H)
    (hf : ∀ b : realTypeSobolevSourceLocus, b ∈ sourceSobolevFiniteGapLocus →
      (∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n k (sobolevSourceInclusion b.val)) = H b.val)
    (a : realTypeSobolevSourceLocus) :
    (∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n k (sobolevSourceInclusion a.val)) = H a.val := by
  have hc : Continuous (fun b : realTypeSobolevSourceLocus =>
      (∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n k (sobolevSourceInclusion b.val))-H b.val) := by
    apply continuous_iff_continuousAt.mpr
    intro b
    exact ((analyticAt_tsum_sourceSobolevHigherAction b.val b.property k hk).continuousAt.comp
      continuous_subtype_val.continuousAt).sub (hH.continuousAt.comp continuous_subtype_val.continuousAt)
  apply sub_eq_zero.mp
  exact eq_of_continuousOn_of_sourceSobolevFiniteGap isOpen_univ hc.continuousOn 0
    (fun b _ hb => sub_eq_zero.mpr (hf b hb)) a (mem_univ _)

/-- Level one sums to the actual physical mass on every real H¹ source. -/
theorem sourceSobolev_tsum_higherAction_one (a : realTypeSobolevSourceLocus) :
    (∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n 0 (sobolevSourceInclusion a.val)) =
      periodOneSobolevMass a.val := by
  apply higherAction_trace_of_finiteGap 0 (by norm_num) _ continuous_periodOneSobolevMass ?_ a
  intro b hf
  have h := sourceFiniteGap_tsum_complexHigherActions_eq_hamiltonian (by simp) (by norm_num)
    ⟨sobolevSourceInclusion b.val,b.property⟩ hf 0
  have he := periodOneSobolevMass_sourceFiniteGapSobolevPair (by simp) (by norm_num)
    ⟨sobolevSourceInclusion b.val,b.property⟩ hf
  rw [sourceFiniteGapSobolevPair_sobolevSource b hf] at he
  simpa only [Nat.zero_add,pow_zero,div_one,← he] using h

/-- Level three sums to one quarter of the actual physical H¹ energy. -/
theorem sourceSobolev_tsum_higherAction_three (a : realTypeSobolevSourceLocus) :
    (∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n 2 (sobolevSourceInclusion a.val)) =
      periodOneSobolevHamiltonian a.val/4 := by
  apply higherAction_trace_of_finiteGap 2 le_rfl _ (continuous_periodOneSobolevHamiltonian.div_const 4) ?_ a
  intro b hf
  have h := sourceFiniteGap_tsum_complexHigherActions_eq_hamiltonian (by simp) (by norm_num)
    ⟨sobolevSourceInclusion b.val,b.property⟩ hf 2
  have he := periodOneSobolevHamiltonian_sourceFiniteGapSobolevPair (by simp) (by norm_num)
    ⟨sobolevSourceInclusion b.val,b.property⟩ hf
  rw [sourceFiniteGapSobolevPair_sobolevSource b hf] at he
  norm_num at h
  exact h.trans (congrArg (fun z : ℂ => z/4) he.symm)

/-- Both literal trace identities persist on a complex neighborhood of each
real H¹ source; the three action series are absolutely convergent there. -/
theorem exists_local_sourceSobolevHigherAction_trace (a : realTypeSobolevSourceLocus) :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧ a.val ∈ U ∧
      ∀ b ∈ U,
        ((∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n 0 (sobolevSourceInclusion b)) =
          periodOneSobolevMass b) ∧
        ((∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n 2 (sobolevSourceInclusion b)) =
          periodOneSobolevHamiltonian b/4) ∧
        ∀ k : ℕ, k ≤ 2 → Summable (fun n : ℤ =>
          ‖sourceComplexHigherAction (by simp) (by norm_num) n k (sobolevSourceInclusion b)‖) := by
  have hm := eventuallyEq_sobolev_of_analyticAt_of_real_agreement a _ _
    (analyticAt_tsum_sourceSobolevHigherAction a.val a.property 0 (by norm_num))
    (analyticAt_periodOneSobolevMass a.val) sourceSobolev_tsum_higherAction_one
  have he := eventuallyEq_sobolev_of_analyticAt_of_real_agreement a _ _
    (analyticAt_tsum_sourceSobolevHigherAction a.val a.property 2 le_rfl)
    ((analyticAt_periodOneSobolevHamiltonian a.val).div_const) sourceSobolev_tsum_higherAction_three
  obtain ⟨V,hV,haV,hseries⟩ := exists_local_sourceSobolevHigherAction_tsum_analytic a.val a.property
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp ((hm.and he).and (hV.mem_nhds haV))
  refine ⟨ball a.val r,isOpen_ball,mem_ball_self hr,?_⟩
  intro b hb
  exact ⟨(hsub hb).1.1,(hsub hb).1.2,fun k hk => (hseries k hk).1 b (hsub hb).2⟩

/-- One open complex H¹ domain contains all real sources and satisfies the
mass and energy trace formulas with absolutely convergent defining series. -/
theorem exists_sourceSobolevHigherAction_trace_domain :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧
      {a | IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))} ⊆ U ∧
      ∀ b ∈ U,
        ((∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n 0 (sobolevSourceInclusion b)) =
          periodOneSobolevMass b) ∧
        ((∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n 2 (sobolevSourceInclusion b)) =
          periodOneSobolevHamiltonian b/4) ∧
        ∀ k : ℕ, k ≤ 2 → Summable (fun n : ℤ =>
          ‖sourceComplexHigherAction (by simp) (by norm_num) n k (sobolevSourceInclusion b)‖) := by
  choose V hV haV htrace using exists_local_sourceSobolevHigherAction_trace
  refine ⟨⋃ a : realTypeSobolevSourceLocus, V a,isOpen_iUnion hV,?_,?_⟩
  · intro a ha
    exact mem_iUnion.mpr ⟨⟨a,ha⟩,haV ⟨a,ha⟩⟩
  · intro b hb
    obtain ⟨a,ha⟩ := mem_iUnion.mp hb
    exact htrace a b ha

end NLS.ZakharovShabat
