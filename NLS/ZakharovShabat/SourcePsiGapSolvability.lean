import NLS.ZakharovShabat.SourcePsiGapSolutionLimit
import NLS.ZakharovShabat.SourceRealTypeConvex
import NLS.ZakharovShabat.SourcePsiFreeInitialSolution

/-!
# Solvability of the real gap psi equation

The contour family is existential data in this predicate. This makes
solvability independent of the local chart used to express the selected
equation. Compactness and local implicit continuation give sequential
stability and relative local existence on the real-type source locus.
-/

noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat

/-- A deleted-root sequence solves the selected psi equation in some
valid real-centered contour family, with retained roots in their
assigned periodic gaps. -/
def SourcePsiGapSolution
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (a : DeletedCoeff p n) : Prop :=
  (∀ m : ℤ, m ≠ n →
    displacedRoots (a : Coeff p) m ∈ sourcePeriodicSegment hp hp1 φ m) ∧
  ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
    (∀ m, (c m).im = 0) ∧
    (∀ m, 0 < R m ∧
      sourcePeriodicSegment hp hp1 φ m ⊆ ball (c m) (R m) ∧
      closedBall (c m) (R m) ⊆
        sourceStandardRootOmittedDomain hp hp1 φ m) ∧
    (∀ m,
      (sourcePsiSelectedEquationSequence hp hp1 n c R a φ : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (a : Coeff p) φ (c m) (R m)) ∧
    sourcePsiSelectedEquationSequence hp hp1 n c R a φ = 0

/-- The source potentials admitting a real gap-contained psi solution. -/
def SourcePsiGapSolvable
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) : Prop :=
  IsRealType (CoeffPair.toMax p φ) ∧
    ∃ a : DeletedCoeff p n, SourcePsiGapSolution hp hp1 n φ a

/-- The free potential supplies the initial solvable source. -/
theorem sourcePsiGapSolvable_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    SourcePsiGapSolvable hp hp1 n (0 : CoeffPair p) := by
  obtain ⟨U,hUopen,hbase,c,R,Niso,εiso,
      hdisjoint,hfilled,hcenter,hgeom,hcoord,s,V,hVopen,hVbase,
      hs,hs0,hunique,hsolution⟩ :=
    exists_local_sourcePsi_C1_branch_at_free_source hp hp1 n
  have hgap : ∀ m : ℤ, m ≠ n →
      displacedRoots (0 : Coeff p) m ∈
        sourcePeriodicSegment hp hp1 (0 : CoeffPair p) m := by
    intro m _
    rw [sourcePeriodicSegment_zero_source hp hp1 m]
    simp [displacedRoots]
  have hzero : sourcePsiSelectedEquationSequence hp hp1 n c R
      (0 : DeletedCoeff p n) (0 : CoeffPair p) = 0 := by
    simpa only [hs0] using hsolution.self_of_nhds.2
  exact ⟨by simp,(0 : DeletedCoeff p n),hgap,c,R,hcenter,
    (fun m => let h := hgeom (0,0) hbase m; ⟨h.1,h.2.1,h.2.2.1⟩),
    (hcoord (0,0) hbase),hzero⟩

/-- Limits of real-type sources with gap-contained psi solutions
remain solvable, even when their contour families vary arbitrarily. -/
theorem sourcePsiGapSolvable_of_tendsto
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (ψ : ℕ → CoeffPair p) (hψ : Tendsto ψ atTop (𝓝 φ))
    (hsol : ∀ k, SourcePsiGapSolvable hp hp1 n (ψ k)) :
    SourcePsiGapSolvable hp hp1 n φ := by
  classical
  choose a ha using fun k => (hsol k).2
  choose c hc using fun k => (ha k).2
  choose R hR using fun k => hc k
  obtain ⟨b,σ,U,c₀,R₀,hσ,hb,hgap,hUopen,hbase,
      hcenter₀,hgeom₀,hcoord₀,hC1,hzero₀,hbij,s,V,hVopen,hVbase,
      hs,hsb,hunique,hchartUnique,hbranch⟩ :=
    exists_limit_sourcePsi_gap_solution hp hp1 φ hφ ψ hψ
      (fun k => (hsol k).1) n a
      (fun k => (ha k).1) c R
      (fun k m => (hR k).1 m)
      (fun k m => (hR k).2.1 m)
      (fun k m => (hR k).2.2.1 m)
      (fun k => (hR k).2.2.2)
  exact ⟨hφ,b,hgap,c₀,R₀,hcenter₀,
    (fun m => let h := hgeom₀ (b,φ) hbase m; ⟨h.1,h.2.1,h.2.2.1⟩),
    (hcoord₀ (b,φ) hbase),hzero₀⟩

/-- A real-type solvable source has nearby real-type solvable sources.
This is relative openness expressed as a neighborhood statement. -/
theorem eventually_sourcePsiGapSolvable_of_solution
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hsol : SourcePsiGapSolvable hp hp1 n φ) :
    ∀ᶠ χ in 𝓝 φ,
      IsRealType (CoeffPair.toMax p χ) →
        SourcePsiGapSolvable hp hp1 n χ := by
  classical
  obtain ⟨hφ,a,hgap,c,R,hcenter,hgeom,hcoord,hzero⟩ := hsol
  obtain ⟨b,σ,U,c₀,R₀,hσ,hb,hbgap,hUopen,hbase,
      hcenter₀,hgeom₀,hcoord₀,hC1,hzero₀,hbij,s,V,hVopen,hVbase,
      hs,hsb,hunique,hchartUnique,hbranch⟩ :=
    exists_limit_sourcePsi_gap_solution hp hp1 φ hφ
      (fun _ : ℕ => φ) tendsto_const_nhds
      (fun _ => hφ) n (fun _ => a)
      (fun _ => hgap) (fun _ => c) (fun _ => R)
      (fun _ => hcenter) (fun _ => hgeom)
      (fun _ => hcoord) (fun _ => hzero)
  filter_upwards [hbranch] with χ hχ hreal
  have hmem := hχ.1
  have hzeroχ := hχ.2.1
  have hgapχ := (hχ.2.2 hreal).2
  exact ⟨hreal,s χ,hgapχ,c₀,R₀,hcenter₀,
    (fun m => let h := hgeom₀ (s χ,χ) hmem m; ⟨h.1,h.2.1,h.2.2.1⟩),
    (hcoord₀ (s χ,χ) hmem),hzeroχ⟩

/-- A specified real gap solution extends to a `C¹` branch of gap
solutions along all sufficiently nearby real-type sources. -/
theorem exists_C1_SourcePsiGapSolution_branch
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : DeletedCoeff p n) (hsol : SourcePsiGapSolution hp hp1 n φ a) :
    ∃ s : CoeffPair p → DeletedCoeff p n,
      ContDiffAt ℂ 1 s φ ∧ s φ = a ∧
      ∀ᶠ χ in 𝓝 φ,
        IsRealType (CoeffPair.toMax p χ) →
          SourcePsiGapSolution hp hp1 n χ (s χ) := by
  obtain ⟨hgap,c,R,hcenter,hgeom,hcoord,hzero⟩ := hsol
  obtain ⟨b,σ,U,c₀,R₀,hσ,hb,hbgap,hUopen,hbase,
      hcenter₀,hgeom₀,hcoord₀,hC1,hzero₀,hbij,s,V,hVopen,hVbase,
      hs,hsb,hunique,hchartUnique,hbranch⟩ :=
    exists_limit_sourcePsi_gap_solution hp hp1 φ hφ
      (fun _ : ℕ => φ) tendsto_const_nhds
      (fun _ => hφ) n (fun _ => a)
      (fun _ => hgap) (fun _ => c) (fun _ => R)
      (fun _ => hcenter) (fun _ => hgeom)
      (fun _ => hcoord) (fun _ => hzero)
  have hba : b = a := by
    have hb' : Tendsto (fun _ : ℕ => a) atTop (𝓝 b) := by
      simpa only [Function.comp_def] using hb
    exact tendsto_nhds_unique hb' tendsto_const_nhds
  refine ⟨s,hs,hsb.trans hba,?_⟩
  filter_upwards [hbranch] with χ hχ hreal
  exact ⟨(hχ.2.2 hreal).2,c₀,R₀,hcenter₀,
    (fun m => let h := hgeom₀ (s χ,χ) hχ.1 m; ⟨h.1,h.2.1,h.2.2.1⟩),
    (hcoord₀ (s χ,χ) hχ.1),hχ.2.1⟩

end NLS.ZakharovShabat
