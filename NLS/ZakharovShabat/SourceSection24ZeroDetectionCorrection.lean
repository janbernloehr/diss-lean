import NLS.ZakharovShabat.SourceSection24Original
import NLS.ZakharovShabat.SourceSection20MomentumBracket
import NLS.FunctionalAnalysis.ClosedDerivativeZero

/-! # The Section 24 zero-detection claim fails at level two

For a real finite-gap source with only its central gap open, the physical
momentum is constant along central-action reduction and zero at collapse.
The original level-two central action is therefore zero. Sources with any
prescribed positive central action give counterexamples inside the same
retained original domain U. Lean power one denotes printed level two.
-/
noncomputable section
open Set Filter Topology Complex
namespace NLS.ZakharovShabat
namespace SourceSection24Data
variable {W₀ W V Wa B U : Set (CoeffPair 2)}
  {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
  (Q : SourceSection24Data D A B U)
include Q

/-- An isolated open central gap has zero level-two action. -/
theorem central_levelTwo_eq_zero
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem _) 0 ≠ 0)
    (hclosed : ∀ n : ℤ, n ≠ 0 → canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n = 0) :
    sourceIndexedHigherAction (by simp) (by norm_num) 0 1 φ.val = 0 := by
  let γ := D.complex.hilbertActionReduction φ 0
  let a := (sourceRealAction (by simp) (by norm_num) φ.val φ.property 0).re
  have ha : 0 < a := SourceBirkhoffMapComplexData.hilbert_action_pos_of_gap_ne_zero φ 0 hn
  let F : ℝ → ℂ := fun t => sourceIndexedHigherAction (by simp) (by norm_num) 0 1 (γ t).val
  have ht (t : ℝ) : F t = D.complex.physicalActionReductionHamiltonian φ hf 0 2 t/2 := by
    dsimp only [F]
    rw [sourceIndexedHigherAction_eq_real (by simp) (by norm_num) (γ t)]
    have h := sourceFiniteGap_tsum_higherActions_eq_hamiltonian (by simp) (by norm_num) (γ t)
      (D.complex.hilbertActionReduction_mem_finiteGap φ hf 0 t) 1
    rw [tsum_eq_single 0] at h
    · simpa only [pow_one,Nat.reduceAdd,SourceBirkhoffMapComplexData.physicalActionReductionHamiltonian,γ] using! h
    · intro n hn'
      rw [sourceRealHigherAction_of_collapsed (by simp) (by norm_num) (γ t) n
        (D.complex.hilbertActionReduction_gap_zero_of_ne φ 0 n hn' t (hclosed n hn')) 1]
      rfl
  have hγ : Continuous (fun t => (γ t).val) :=
    continuous_subtype_val.comp (D.complex.continuous_hilbertActionReduction φ 0)
  have hc : ContinuousOn F (Icc 0 a) :=
    (Q.higherAction_analytic 0 1).continuousOn.comp hγ.continuousOn
      (fun t _ => Q.real_subset (γ t).property)
  have hd : ∀ t ∈ Ioo 0 a, HasDerivAt F 0 t := by
    intro t hta
    have hne := D.complex.hilbertActionReduction_gap_ne_zero 0 φ ha hta.2
    have hb := Q.toSourceSection20Data.finiteGap_momentum_bracket (γ t)
      (D.complex.hilbertActionReduction_mem_finiteGap φ hf 0 t) 0 hne
    have h := D.complex.hasDerivAt_physicalActionReductionHamiltonian_two
      D.previous.original_theta_common_domain φ hf 0 hn t hta.2
    rw [hb] at h
    simp only [Int.cast_zero,mul_zero,neg_zero] at h
    have h' := h.div_const (2:ℂ)
    simp only [zero_div] at h'
    exact h'.congr_of_eventuallyEq (Eventually.of_forall ht)
  have hF := NLS.FunctionalAnalysis.eq_of_hasDerivAt_zero_Icc hc hd
    (time := 0) (initial := a) ⟨le_rfl,ha.le⟩ ⟨ha.le,le_rfl⟩
  have hend : F a = 0 := by
    apply Q.toSourceSection19Data.indexedHigherAction_of_collapsed (γ a).val (Q.real_subset (γ a).property) 0 1
    have h := D.complex.hilbertActionReduction_gap_zero_at_collapse φ 0 ha
    simpa only [sourcePeriodicGapDisplacement_apply] using h
  rw [hend] at hF
  simpa only [F,γ,D.complex.hilbertActionReduction_zero] using hF

/-- Every positive central action gives an actual source in the retained U
with an open gap and a vanishing higher action at printed level two. -/
theorem exists_levelTwo_zero_of_action_pos (c : ℝ) (hc : 0 < c) :
    ∃ φ : realTypeSourceSubmodule 2, φ.val ∈ U ∧
      φ ∈ sourceFiniteGapLocus (by simp) (by norm_num) ∧
      canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 ≠ 0 ∧
      sourceIndexedAction (by simp) (by norm_num) 0 φ.val = (c:ℂ) ∧
      sourceIndexedHigherAction (by simp) (by norm_num) 0 1 φ.val = 0 := by
  obtain ⟨a,ha,_,_⟩ := exists_realSobolev_single_action 0 c hc.le
  let φ : realTypeSourceSubmodule 2 := ⟨sobolevSourceInclusion a.val,a.property⟩
  have hclosed (n : ℤ) (hn : n ≠ 0) : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0 := by
    have hz : sourceComplexAction (by simp) (by norm_num) n φ.val = 0 := by
      change sourceComplexAction (by simp) (by norm_num) n (sobolevSourceInclusion a.val) = 0
      simp [ha n,hn]
    have he := (sourceComplexAction_nonneg_and_eq_zero_iff_gap_zero
      (by simp) (by norm_num) n φ.val φ.property).2.2.mp hz
    simpa only [sourcePeriodicGapDisplacement_apply] using he
  have hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num) := by
    apply (Set.finite_singleton (0:ℤ)).subset
    intro n hn
    by_contra hn0
    exact hn (hclosed n hn0)
  have hopen : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 ≠ 0 := by
    intro hz
    have he := (sourceComplexAction_nonneg_and_eq_zero_iff_gap_zero
      (by simp) (by norm_num) 0 φ.val φ.property).2.2.mpr
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hz)
    change sourceComplexAction (by simp) (by norm_num) 0 (sobolevSourceInclusion a.val) = 0 at he
    rw [ha 0] at he
    exact (Complex.ofReal_ne_zero.mpr hc.ne') (by simpa using he)
  have haction : sourceIndexedAction (by simp) (by norm_num) 0 φ.val = (c:ℂ) := by
    rw [sourceIndexedAction_eq_sourceRealAction (by simp) (by norm_num) 0 φ.val φ.property,
      ← sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) 0 φ.val φ.property]
    simpa only [φ,ite_true] using ha 0
  exact ⟨φ,Q.real_subset φ.property,hf,hopen,haction,
    Q.central_levelTwo_eq_zero φ hf hopen hclosed⟩

/-- The printed p. 106 blanket equivalence for levels at least two is false
on every retained original domain, already at a real source and index zero. -/
theorem not_higherAction_zero_iff_gap_zero :
    ¬ ∀ ψ ∈ U, ∀ (n : ℤ) (k : ℕ), 1 ≤ k →
      (sourceIndexedHigherAction (by simp) (by norm_num) n k ψ = 0 ↔
        canonicalPeriodicGap (by simp) (by norm_num)
          (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0) := by
  obtain ⟨φ,hφ,_,hgap,_,hzero⟩ := Q.exists_levelTwo_zero_of_action_pos 1 (by norm_num)
  intro h
  exact hgap ((h φ.val hφ 0 1 le_rfl).mp hzero)
end SourceSection24Data

/-- An unconditional actual-source counterexample to the printed zero-detection claim. -/
theorem section24_levelTwo_zero_counterexample :
    ∃ φ : realTypeSourceSubmodule 2,
      φ ∈ sourceFiniteGapLocus (by simp) (by norm_num) ∧
      canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential φ.val) (periodOnePotential_mem φ.val) 0 ≠ 0 ∧
      sourceIndexedAction (by simp) (by norm_num) 0 φ.val = 1 ∧
      sourceIndexedHigherAction (by simp) (by norm_num) 0 1 φ.val = 0 := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection24_original
  obtain ⟨φ,_,hf,hgap,ha,hzero⟩ := Q.exists_levelTwo_zero_of_action_pos 1 (by norm_num)
  exact ⟨φ,hf,hgap,by simpa using ha,hzero⟩
end NLS.ZakharovShabat
