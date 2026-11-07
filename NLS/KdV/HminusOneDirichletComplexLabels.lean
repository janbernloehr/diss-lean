import NLS.KdV.HminusOneDirichletComplexAsymptotics
import Mathlib.Data.PNat.Basic

/-! Intrinsic FULL complex Dirichlet labels on the exact original positive
indices. Every native eigenvalue is listed with its actual algebraic
multiplicity; the lexicographic sequence has the literal n-times-l2 error. -/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped Classical ENNReal
namespace NLS.KdV

/-- Existence in a form that selects the complete sequence before its witnesses. -/
theorem exists_hillHminusDirichletComplexSequence (q : PeriodOneHminusOne) :
    ∃ mu : ℕ → ℂ, ∃ u : Coeff 2, ∃ c : ℂ, ∃ N : ℕ,
      HillHminusDirichletComplexLabeling q u c N mu := by
  obtain ⟨u,c,N,mu,h⟩ := exists_hillHminusDirichletComplexLabeling q
  exact ⟨mu,u,c,N,h⟩

/-- The unique complete complex sequence, internally indexed from zero. -/
def hillHminusDirichletComplexSequence (q : PeriodOneHminusOne) : ℕ → ℂ :=
  (exists_hillHminusDirichletComplexSequence q).choose

theorem hillHminusDirichletComplexSequence_spec (q : PeriodOneHminusOne) :
    ∃ u : Coeff 2, ∃ c : ℂ, ∃ N : ℕ,
      HillHminusDirichletComplexLabeling q u c N (hillHminusDirichletComplexSequence q) :=
  (exists_hillHminusDirichletComplexSequence q).choose_spec

/-- Intrinsic original positive-index complex Dirichlet labels. -/
def hillHminusDirichletComplexLabels (q : PeriodOneHminusOne) (n : ℕ+) : ℂ :=
  hillHminusDirichletComplexSequence q (Equiv.pnatEquivNat n)

/-- ALL central and high labels have the original lexicographic order. -/
theorem monotone_hillHminusDirichletComplexLabels (q : PeriodOneHminusOne) :
    Monotone (fun n : ℕ+ => complexLexKey (hillHminusDirichletComplexLabels q n)) := by
  obtain ⟨u,c,N,h⟩ := hillHminusDirichletComplexSequence_spec q
  exact h.ordered.comp OrderIso.pnatIsoNat.monotone

/-- The full intrinsic positive list exhausts the ENTIRE actual native spectrum. -/
theorem hillHminusDirichletComplexLabels_spectrum_iff (q : PeriodOneHminusOne) (e : ℂ) :
    e ∈ singularDirichletSpectrum (periodOneOriginal q) ↔
      ∃ n : ℕ+, hillHminusDirichletComplexLabels q n = e := by
  obtain ⟨u,c,N,h⟩ := hillHminusDirichletComplexSequence_spec q
  constructor
  · intro he
    obtain ⟨j,hj⟩ := (h.exhaustive e).mp he
    exact ⟨Equiv.pnatEquivNat.symm j,by simpa only [hillHminusDirichletComplexLabels,
      Equiv.apply_symm_apply] using hj⟩
  · rintro ⟨n,hn⟩
    exact (h.exhaustive e).mpr ⟨Equiv.pnatEquivNat n,hn⟩

/-- Every value has finitely many positive-index occurrences. -/
theorem finite_fiber_hillHminusDirichletComplexLabels (q : PeriodOneHminusOne) (e : ℂ) :
    {n : ℕ+ | hillHminusDirichletComplexLabels q n = e}.Finite := by
  obtain ⟨u,c,N,h⟩ := hillHminusDirichletComplexSequence_spec q
  exact (h.finite_fiber e).preimage Equiv.pnatEquivNat.injective.injOn

/-- Actual FULL native algebraic multiplicity equals the exact positive-index
occurrence count, including all complex central associated vectors. -/
theorem hillHminusDirichletComplexLabels_multiplicity (q : PeriodOneHminusOne) (e : ℂ) :
    (∑ᶠ n : ℕ+, if hillHminusDirichletComplexLabels q n = e then (1:ℕ) else 0) =
      singularDirichletAlgebraicMultiplicity (periodOneOriginal q) e := by
  obtain ⟨u,c,N,h⟩ := hillHminusDirichletComplexSequence_spec q
  change (∑ᶠ n : ℕ+, if hillHminusDirichletComplexSequence q (Equiv.pnatEquivNat n) = e
    then (1:ℕ) else 0) = _
  rw [finsum_comp_equiv Equiv.pnatEquivNat
    (f := fun j : ℕ => if hillHminusDirichletComplexSequence q j = e then (1:ℕ) else 0)]
  exact h.multiplicity e

/-- The original complex source asymptotic at the SAME positive index:
mu_n = n^2*pi^2 + n*l2_n, with every central label included. -/
theorem memlp_hillHminusDirichletComplexLabels_inverseIndex_error (q : PeriodOneHminusOne) :
    Memℓp (fun n : ℕ+ =>
      (hillHminusDirichletComplexLabels q n-((Real.pi:ℂ)*(n:ℕ))^2)/(n:ℕ)) 2 := by
  obtain ⟨u,c,N,h⟩ := hillHminusDirichletComplexSequence_spec q
  have ht := (h.inverseIndex_error.summable (by norm_num)).comp_injective
    Equiv.pnatEquivNat.injective
  apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
  simpa only [Function.comp_def,Equiv.pnatEquivNat_apply,PNat.natPred_add_one,
    hillHminusDirichletComplexLabels] using! ht

/-- The entire intrinsic positive list agrees with ANY constructed complete
complex labeling at index n-1, independently of lift and cutoff. -/
theorem hillHminusDirichletComplexLabels_eq_labeling
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ) (N : ℕ) (mu : ℕ → ℂ)
    (h : HillHminusDirichletComplexLabeling q u c N mu) (n : ℕ+) :
    hillHminusDirichletComplexLabels q n = mu (Equiv.pnatEquivNat n) := by
  obtain ⟨v,d,M,g⟩ := hillHminusDirichletComplexSequence_spec q
  exact congrFun (g.unique h) _

end NLS.KdV
