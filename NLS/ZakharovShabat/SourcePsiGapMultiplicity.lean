import NLS.ZakharovShabat.SourcePsiGapGlobalExistence
import Mathlib.Topology.Separation.Hausdorff

/-!
# Local stability of distinct gap solutions

Each solution extends to a local `C¹` branch. If two solutions differ
at a real-type source, their continuous branches remain distinct on
a neighborhood. Thus multiplicity is relatively open in the real-type
source locus.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat

/-- A real-type source admitting two distinct gap-contained psi
solutions, with potentially different valid contour families. -/
def SourcePsiGapMultiple
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) : Prop :=
  IsRealType (CoeffPair.toMax p φ) ∧
    ∃ a b : DeletedCoeff p n,
      a ≠ b ∧
      SourcePsiGapSolution hp hp1 n φ a ∧
      SourcePsiGapSolution hp hp1 n φ b

/-- Two distinct solutions persist as distinct solutions along nearby
real-type source potentials. -/
theorem eventually_SourcePsiGapMultiple_of_multiple
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hmul : SourcePsiGapMultiple hp hp1 n φ) :
    ∀ᶠ χ in 𝓝 φ,
      IsRealType (CoeffPair.toMax p χ) →
        SourcePsiGapMultiple hp hp1 n χ := by
  obtain ⟨hφ,a,b,hab,ha,hb⟩ := hmul
  obtain ⟨s,hs,hsa,hsGap⟩ :=
    exists_C1_SourcePsiGapSolution_branch hp hp1 n φ hφ a ha
  obtain ⟨t,ht,htb,htGap⟩ :=
    exists_C1_SourcePsiGapSolution_branch hp hp1 n φ hφ b hb
  have hpair : (s φ,t φ) ∈ (diagonal (DeletedCoeff p n))ᶜ := by
    simpa only [hsa,htb,mem_compl_iff,mem_diagonal_iff] using hab
  have hpairCont : ContinuousAt (fun χ : CoeffPair p => (s χ,t χ)) φ :=
    hs.continuousAt.prodMk ht.continuousAt
  have hne : ∀ᶠ χ in 𝓝 φ, s χ ≠ t χ := by
    have h := hpairCont.eventually
      (isClosed_diagonal.isOpen_compl.mem_nhds hpair)
    simpa only [mem_compl_iff,mem_diagonal_iff] using h
  filter_upwards [hsGap,htGap,hne] with χ hsχ htχ hneχ hreal
  exact ⟨hreal,s χ,t χ,hneχ,hsχ hreal,htχ hreal⟩

/-- Sources with at least two gap solutions form a relatively open
subset of the connected real-type source locus. -/
theorem isOpen_sourcePsiGapMultiple_on_realType
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    IsOpen {x : realTypeSourceLocus p |
      SourcePsiGapMultiple hp hp1 n x.val} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hlocal := eventually_SourcePsiGapMultiple_of_multiple
    hp hp1 n x.val hx
  have hlocal' := continuous_subtype_val.continuousAt.eventually hlocal
  apply hlocal'.mono
  intro y hy
  exact hy y.property

end NLS.ZakharovShabat
