import Mathlib.Analysis.Analytic.Uniqueness
import NLS.ZakharovShabat.SobolevOddHamiltonian
import NLS.ZakharovShabat.SourceHigherSobolevTraceTransfer

/-! # Sharp odd physical trace identities on H^m

The independently defined reduced physical Hamiltonian agrees with actual
finite-gap reconstruction. Density and analytic uniqueness extend its trace
to all real H^m inputs and to a complex neighborhood of the entire real locus.
-/
noncomputable section
open Set
namespace NLS.ZakharovShabat

/-- The sharp Sobolev functional agrees with the original physical finite-gap Hamiltonian. -/
theorem sobolevOddHamiltonian_eq_finiteGap (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) (hf : a ∈ sourceHigherSobolevFiniteGapLocus m) :
    sobolevOddHamiltonian m hm a.val = sourceFiniteGapNLSHamiltonian (by simp) (by norm_num)
      ⟨higherSobolevSourceInclusion m a.val,a.property⟩ hf (2*m+1) := by
  let φ : realTypeSourceSubmodule 2 := ⟨higherSobolevSourceInclusion m a.val,a.property⟩
  obtain ⟨ha,hb⟩ := contDiff_sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf
  obtain ⟨hpa,hpb⟩ := periodic_sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf
  apply sobolevOddHamiltonian_eq_classical m hm a.val _ _ ha hb hpa hpb
  · intro j
    have h := (periodOneCoefficient_sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf j).1
    exact (higherSobolevSourceInclusion_fst m a.val j).symm.trans h.symm
  · intro j
    have h := (periodOneCoefficient_sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf j).2
    exact (higherSobolevSourceInclusion_snd m a.val j).symm.trans h.symm

/-- The H_(2m+1) trace holds on every real H^m source, with factor 4^m. -/
theorem sobolevOddHamiltonian_higherAction_trace (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    (∑' j : ℤ, sourceComplexHigherAction (by simp) (by norm_num) j (2*m)
      (higherSobolevSourceInclusion m a.val)) = sobolevOddHamiltonian m hm a.val/4^m := by
  have h := sourceHigherSobolevHigherAction_trace_of_hamiltonian m (2*m) le_rfl
    (sobolevOddHamiltonian m hm) (continuous_sobolevOddHamiltonian m hm)
    (fun b hb => sobolevOddHamiltonian_eq_finiteGap m hm b hb) a
  simpa only [pow_mul,show (2:ℂ)^2 = 4 by norm_num] using h

/-- The sharp physical trace and absolute convergence hold on a complex H^m neighborhood. -/
theorem exists_local_sobolevOddHamiltonian_trace (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    ∃ U : Set (SobolevSource m), IsOpen U ∧ a.val ∈ U ∧ ∀ b ∈ U,
      ((∑' j : ℤ, sourceComplexHigherAction (by simp) (by norm_num) j (2*m)
        (higherSobolevSourceInclusion m b)) = sobolevOddHamiltonian m hm b/4^m) ∧
      Summable (fun j : ℤ => ‖sourceComplexHigherAction (by simp) (by norm_num) j (2*m)
        (higherSobolevSourceInclusion m b)‖) := by
  have h := exists_local_sourceHigherSobolevHigherAction_hamiltonian_trace m (2*m) le_rfl
    (sobolevOddHamiltonian m hm) (fun b _ => analyticAt_sobolevOddHamiltonian m hm b)
    (fun b hb => sobolevOddHamiltonian_eq_finiteGap m hm b hb) a
  simpa only [pow_mul,show (2:ℂ)^2 = 4 by norm_num] using h

/-- One complex H^m domain contains the full real locus and satisfies the sharp odd trace. -/
theorem exists_sobolevOddHamiltonian_trace_domain (m : ℕ) (hm : 1 ≤ m) :
    ∃ U : Set (SobolevSource m), IsOpen U ∧
      {a | IsRealType (CoeffPair.toMax 2 (higherSobolevSourceInclusion m a))} ⊆ U ∧
      ∀ b ∈ U,
        ((∑' j : ℤ, sourceComplexHigherAction (by simp) (by norm_num) j (2*m)
          (higherSobolevSourceInclusion m b)) = sobolevOddHamiltonian m hm b/4^m) ∧
        Summable (fun j : ℤ => ‖sourceComplexHigherAction (by simp) (by norm_num) j (2*m)
          (higherSobolevSourceInclusion m b)‖) := by
  choose V hV haV ht using exists_local_sobolevOddHamiltonian_trace m hm
  refine ⟨⋃ a : realTypeHigherSobolevSourceLocus m, V a,isOpen_iUnion hV,?_,?_⟩
  · intro a ha
    exact mem_iUnion.mpr ⟨⟨a,ha⟩,haV ⟨a,ha⟩⟩
  · intro b hb
    obtain ⟨a,ha⟩ := mem_iUnion.mp hb
    exact ht a b ha

/-- The physical extension is independent of the chosen reduced polynomial:
any entire candidate with the same finite-gap physical values agrees everywhere. -/
theorem sobolevOddHamiltonian_unique (m : ℕ) (hm : 1 ≤ m) (H : SobolevSource m → ℂ)
    (hH : AnalyticOnNhd ℂ H univ)
    (hf : ∀ a : realTypeHigherSobolevSourceLocus m, ∀ ha : a ∈ sourceHigherSobolevFiniteGapLocus m,
      H a.val = sourceFiniteGapNLSHamiltonian (by simp) (by norm_num)
        ⟨higherSobolevSourceInclusion m a.val,a.property⟩ ha (2*m+1)) :
    H = sobolevOddHamiltonian m hm := by
  have hc : Continuous H := continuous_iff_continuousAt.mpr (fun a => (hH a (mem_univ _)).continuousAt)
  have hdiff : Continuous (fun a : realTypeHigherSobolevSourceLocus m =>
      H a.val-sobolevOddHamiltonian m hm a.val) :=
    (hc.comp continuous_subtype_val).sub ((continuous_sobolevOddHamiltonian m hm).comp continuous_subtype_val)
  have hreal (a : realTypeHigherSobolevSourceLocus m) : H a.val = sobolevOddHamiltonian m hm a.val := by
    apply sub_eq_zero.mp
    exact eq_of_continuousOn_of_sourceHigherSobolevFiniteGap m isOpen_univ hdiff.continuousOn 0
      (fun b _ hb => by rw [hf b hb,sobolevOddHamiltonian_eq_finiteGap m hm b hb,sub_self]) a (mem_univ _)
  let z : realTypeHigherSobolevSourceLocus m := ⟨0,by simp⟩
  have hA : AnalyticOnNhd ℂ (sobolevOddHamiltonian m hm) univ :=
    fun a _ => analyticAt_sobolevOddHamiltonian m hm a
  exact hH.eq_of_eventuallyEq hA
    (eventuallyEq_higherSobolev_of_analyticAt_of_real_agreement m z H (sobolevOddHamiltonian m hm)
      (hH z.val (mem_univ _)) (hA z.val (mem_univ _)) hreal)

end NLS.ZakharovShabat
