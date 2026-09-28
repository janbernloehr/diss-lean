import NLS.ZakharovShabat.SourcePsiGapMultiplicity

/-!
# The canonical real gap psi root map

Global existence and uniqueness select one deleted-root vector at
every real-type source. The anchored local implicit branch agrees
with this selection on nearby real-type sources, so the selected map
is continuous and locally extends to a complex `C¹` map.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat

/-- The unique gap-contained psi root vector for a real-type source. -/
def sourcePsiGapRoot
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceLocus p) : DeletedCoeff p n :=
  Classical.choose (existsUnique_SourcePsiGapSolution_of_realType
    hp hp1 n φ.val φ.property)

/-- The canonical root vector solves the gap psi equation. -/
theorem sourcePsiGapRoot_solution
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceLocus p) :
    SourcePsiGapSolution hp hp1 n φ.val (sourcePsiGapRoot hp hp1 n φ) :=
  (Classical.choose_spec (existsUnique_SourcePsiGapSolution_of_realType
    hp hp1 n φ.val φ.property)).1

/-- Every retained canonical root lies in its assigned periodic gap. -/
theorem sourcePsiGapRoot_mem_periodicSegment
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hm : m ≠ n)
    (φ : realTypeSourceLocus p) :
    displacedRoots (sourcePsiGapRoot hp hp1 n φ : Coeff p) m ∈
      sourcePeriodicSegment hp hp1 φ.val m :=
  (sourcePsiGapRoot_solution hp hp1 n φ).1 m hm

@[simp] theorem sourcePsiGapRoot_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    sourcePsiGapRoot hp hp1 n
      (⟨0, by simp [realTypeSourceLocus]⟩ : realTypeSourceLocus p) = 0 :=
  (sourcePsiGapRoot_solution hp hp1 n
    (⟨0, by simp [realTypeSourceLocus]⟩ : realTypeSourceLocus p)).eq_zero_at_free
      hp hp1 n _

/-- Every solution at a real-type source is the canonical one. -/
theorem SourcePsiGapSolution.eq_sourcePsiGapRoot
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceLocus p) (a : DeletedCoeff p n)
    (ha : SourcePsiGapSolution hp hp1 n φ.val a) :
    a = sourcePsiGapRoot hp hp1 n φ :=
  (Classical.choose_spec (existsUnique_SourcePsiGapSolution_of_realType
    hp hp1 n φ.val φ.property)).2 a ha

/-- At each real-type source, the canonical root map agrees locally
with a complex `C¹` branch of the selected equation. -/
theorem exists_C1_local_extension_sourcePsiGapRoot
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceLocus p) :
    ∃ s : CoeffPair p → DeletedCoeff p n,
      ContDiffAt ℂ 1 s φ.val ∧
      s φ.val = sourcePsiGapRoot hp hp1 n φ ∧
      ∀ᶠ χ in 𝓝 φ.val,
        ∀ hχ : IsRealType (CoeffPair.toMax p χ),
          s χ = sourcePsiGapRoot hp hp1 n ⟨χ,hχ⟩ := by
  obtain ⟨s,hs,hsφ,hbranch⟩ :=
    exists_C1_SourcePsiGapSolution_branch hp hp1 n φ.val φ.property
      (sourcePsiGapRoot hp hp1 n φ)
      (sourcePsiGapRoot_solution hp hp1 n φ)
  refine ⟨s,hs,hsφ,?_⟩
  filter_upwards [hbranch] with χ hχ hreal
  exact SourcePsiGapSolution.eq_sourcePsiGapRoot hp hp1 n
    ⟨χ,hreal⟩ (s χ) (hχ hreal)

/-- The uniquely selected real gap roots depend continuously on the
real-type source. -/
theorem continuous_sourcePsiGapRoot
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    Continuous (sourcePsiGapRoot hp hp1 n) := by
  apply continuous_iff_continuousAt.mpr
  intro φ
  obtain ⟨s,hs,hsφ,hlocal⟩ :=
    exists_C1_local_extension_sourcePsiGapRoot hp hp1 n φ
  have hval : Tendsto (fun χ : realTypeSourceLocus p => χ.val)
      (𝓝 φ) (𝓝 φ.val) := continuous_subtype_val.continuousAt.tendsto
  have hEq : (fun χ : realTypeSourceLocus p => s χ.val) =ᶠ[𝓝 φ]
      sourcePsiGapRoot hp hp1 n := by
    have h := hval.eventually hlocal
    apply h.mono
    intro χ hχ
    exact hχ χ.property
  have hsT : Tendsto (fun χ : realTypeSourceLocus p => s χ.val)
      (𝓝 φ) (𝓝 (sourcePsiGapRoot hp hp1 n φ)) := by
    simpa only [hsφ,Function.comp_def] using hs.continuousAt.tendsto.comp hval
  exact hsT.congr' hEq

end NLS.ZakharovShabat
