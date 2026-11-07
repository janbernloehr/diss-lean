import NLS.KdV.HminusOneDirichletCentralCounting
import NLS.SequenceSpaces.OrderedFiniteEnumeration
import NLS.ComplexAnalysis.LexicographicOrder

/-! The COMPLEX native Dirichlet central root multiset and its original
positive-index lexicographic enumeration, with every algebraic repetition. -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped Classical
namespace NLS.KdV

/-- Central roots with the full ACTUAL native operator algebraic repetitions. -/
def hillHminusDirichletCentralRoots (q : PeriodOneHminusOne) (u : Coeff 2)
    (c : ℂ) (N : ℕ) : Multiset ℂ :=
  ∑ e ∈ hillHminusDirichletCentralSpectrum q u c N,
    Multiset.replicate (singularDirichletAlgebraicMultiplicity (periodOneOriginal q) e) e

/-- Every enclosed value occurs exactly as often as its native algebraic multiplicity. -/
theorem count_hillHminusDirichletCentralRoots (q : PeriodOneHminusOne) (u : Coeff 2)
    (c : ℂ) (N : ℕ) (e : ℂ) :
    (hillHminusDirichletCentralRoots q u c N).count e =
      if e ∈ hillHminusDirichletCentralSpectrum q u c N then
        singularDirichletAlgebraicMultiplicity (periodOneOriginal q) e else 0 := by
  simp [hillHminusDirichletCentralRoots,Multiset.count_sum',Multiset.count_replicate]

/-- The multiset contains precisely the actual central native spectrum. -/
theorem mem_hillHminusDirichletCentralRoots (q : PeriodOneHminusOne) (u : Coeff 2)
    (c : ℂ) (N : ℕ) (e : ℂ) :
    e ∈ hillHminusDirichletCentralRoots q u c N ↔
      e ∈ hillHminusDirichletCentralSpectrum q u c N := by
  rw [← Multiset.count_pos,count_hillHminusDirichletCentralRoots]
  by_cases he : e ∈ hillHminusDirichletCentralSpectrum q u c N
  · rw [if_pos he]
    exact iff_of_true
      ((singularDirichletAlgebraicMultiplicity_pos_iff (periodOneOriginal q) e).mpr
        (Finset.mem_filter.mp he).2) he
  · simp [he]

/-- The independently proved actual count fixes the central block's index
offset: there are exactly N slots, starting at positive index one. -/
theorem card_hillHminusDirichletCentralRoots
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (hi : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) (N : ℕ)
    (hcount : AuxiliaryCountingData (by simp)
      (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).val
      (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).property N) :
    (hillHminusDirichletCentralRoots q u c N).card = N := by
  simpa only [hillHminusDirichletCentralRoots,Multiset.card_sum,Multiset.card_replicate]
    using sum_hillHminusDirichletCentralSpectrum_multiplicity q u c hi N hcount

/-- The full complex central native root multiset has a lexicographically
nondecreasing enumeration on indices 1,...,N, preserving ALL repetitions. -/
theorem exists_ordered_hillHminusDirichletCentralRoots
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (hi : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) (N : ℕ)
    (hcount : AuxiliaryCountingData (by simp)
      (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).val
      (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).property N) :
    ∃ xi : ℕ → ℂ,
      (∑ n ∈ Finset.Icc 1 N, ({xi n} : Multiset ℂ)) =
        hillHminusDirichletCentralRoots q u c N ∧
      ∀ i ∈ Finset.Icc 1 N, ∀ j ∈ Finset.Icc 1 N,
        i ≤ j → complexLexLE (xi i) (xi j) := by
  apply NLS.exists_ordered_finset_multiset_enumeration complexLexLE
  rw [card_hillHminusDirichletCentralRoots q u c hi N hcount,Nat.card_Icc]
  omega

end NLS.KdV
