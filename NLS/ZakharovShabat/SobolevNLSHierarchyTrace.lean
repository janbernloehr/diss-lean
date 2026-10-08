import NLS.ZakharovShabat.SobolevRiccatiClassicalAgreement
import NLS.ZakharovShabat.SourceHigherSobolevTraceTransfer

/-! # All-order physical higher-action traces on Sobolev sources

The independently constructed Riccati Hamiltonians agree with the actual
smooth finite-gap hierarchy. Density and analytic uniqueness give every
trace, with factor 2^n, on real Hˢ and on common complex neighborhoods.
-/
noncomputable section
open Set
namespace NLS.ZakharovShabat

/-- Actual finite-gap reconstruction identifies every admissible Sobolev
Hamiltonian with the smooth physical Hamiltonian of the same original source. -/
theorem sobolevNLSHamiltonian_eq_finiteGap (s : ℕ)
    (a : realTypeHigherSobolevSourceLocus s) (hf : a ∈ sourceHigherSobolevFiniteGapLocus s)
    (k : ℕ) (hk : k ≤ s+1) :
    sobolevNLSHamiltonian s a.val k hk = sourceFiniteGapNLSHamiltonian (by simp) (by norm_num)
      ⟨higherSobolevSourceInclusion s a.val,a.property⟩ hf k := by
  let φ : realTypeSourceSubmodule 2 := ⟨higherSobolevSourceInclusion s a.val,a.property⟩
  obtain ⟨ha,hb⟩ := contDiff_sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf
  obtain ⟨hpa,hpb⟩ := periodic_sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf
  apply sobolevNLSHamiltonian_eq_classical s a.val _ _ ha hb hpa hpb
  · intro j
    have h := (periodOneCoefficient_sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf j).1
    exact (higherSobolevSourceInclusion_fst s a.val j).symm.trans h.symm
  · intro j
    have h := (periodOneCoefficient_sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf j).2
    exact (higherSobolevSourceInclusion_snd s a.val j).symm.trans h.symm

/-- The physical trace at every order on all real Hˢ sources, without a
finite-gap hypothesis. The action index n corresponds to Hamiltonian n+1. -/
theorem sobolevNLSHamiltonian_higherAction_trace (s n : ℕ) (hn : n ≤ s)
    (a : realTypeHigherSobolevSourceLocus s) :
    (∑' j : ℤ, sourceComplexHigherAction (by simp) (by norm_num) j n
      (higherSobolevSourceInclusion s a.val)) = sobolevNLSHamiltonian s a.val (n+1) (by omega)/2^n :=
  sourceHigherSobolevHigherAction_trace_of_hamiltonian s n (by omega)
    (fun b => sobolevNLSHamiltonian s b (n+1) (by omega))
    (continuous_sobolevNLSHamiltonian s (n+1) (by omega))
    (fun b hb => sobolevNLSHamiltonian_eq_finiteGap s b hb (n+1) (by omega)) a

/-- One complex Hˢ neighborhood carries all physical traces through order
s+1 simultaneously, with absolutely convergent defining series. -/
theorem exists_local_sobolevNLSHamiltonian_traces (s : ℕ)
    (a : realTypeHigherSobolevSourceLocus s) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a.val ∈ U ∧ ∀ b ∈ U, ∀ n : ℕ, ∀ hn : n ≤ s,
      ((∑' j : ℤ, sourceComplexHigherAction (by simp) (by norm_num) j n
        (higherSobolevSourceInclusion s b)) = sobolevNLSHamiltonian s b (n+1) (by omega)/2^n) ∧
      Summable (fun j : ℤ => ‖sourceComplexHigherAction (by simp) (by norm_num) j n
        (higherSobolevSourceInclusion s b)‖) := by
  have h (n : Fin (s+1)) := exists_local_sourceHigherSobolevHigherAction_hamiltonian_trace s n.val
    (by have := n.isLt; omega) (fun b => sobolevNLSHamiltonian s b (n.val+1) (by have := n.isLt; omega))
    (fun b _ => analyticAt_sobolevNLSHamiltonian s (n.val+1) (by have := n.isLt; omega) b)
    (fun b hb => sobolevNLSHamiltonian_eq_finiteGap s b hb (n.val+1) (by have := n.isLt; omega)) a
  choose V hV haV ht using h
  refine ⟨⋂ n : Fin (s+1), V n,isOpen_iInter_of_finite hV,mem_iInter.mpr haV,?_⟩
  intro b hb n hn
  exact ht ⟨n,Nat.lt_succ_of_le hn⟩ b (mem_iInter.mp hb ⟨n,Nat.lt_succ_of_le hn⟩)

/-- An open complex Hˢ domain contains the full real locus and satisfies
all independently defined physical hierarchy traces through order s+1. -/
theorem exists_sobolevNLSHamiltonian_trace_domain (s : ℕ) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧
      {a | IsRealType (CoeffPair.toMax 2 (higherSobolevSourceInclusion s a))} ⊆ U ∧
      ∀ b ∈ U, ∀ n : ℕ, ∀ hn : n ≤ s,
        ((∑' j : ℤ, sourceComplexHigherAction (by simp) (by norm_num) j n
          (higherSobolevSourceInclusion s b)) = sobolevNLSHamiltonian s b (n+1) (by omega)/2^n) ∧
        Summable (fun j : ℤ => ‖sourceComplexHigherAction (by simp) (by norm_num) j n
          (higherSobolevSourceInclusion s b)‖) := by
  choose V hV haV ht using exists_local_sobolevNLSHamiltonian_traces s
  refine ⟨⋃ a : realTypeHigherSobolevSourceLocus s, V a,isOpen_iUnion hV,?_,?_⟩
  · intro a ha
    exact mem_iUnion.mpr ⟨⟨a,ha⟩,haV ⟨a,ha⟩⟩
  · intro b hb
    obtain ⟨a,ha⟩ := mem_iUnion.mp hb
    exact ht a b ha

end NLS.ZakharovShabat
