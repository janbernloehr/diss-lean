import NLS.ZakharovShabat.SourcePsiGapGlobalExistence
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences

/-!
# Uniqueness of real gap psi solutions

Each solution extends to a local `C¹` branch. If two solutions differ
at a real-type source, their continuous branches remain distinct on
a neighborhood, so multiplicity is relatively open in the real-type
source locus. Compactness and chart-independent local uniqueness also
make multiplicity relatively closed. Connectedness and uniqueness at
the free source then rule out multiplicity everywhere.
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

/-- Multiplicity survives a convergent sequence of real-type sources.
Compactness supplies limits of both root families; chart-independent
local uniqueness prevents the two limits from merging. -/
theorem SourcePsiGapMultiple.of_tendsto
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (ψ : ℕ → CoeffPair p) (hψ : Tendsto ψ atTop (𝓝 φ))
    (hmul : ∀ k, SourcePsiGapMultiple hp hp1 n (ψ k)) :
    SourcePsiGapMultiple hp hp1 n φ := by
  classical
  choose a ha using fun k => (hmul k).2
  choose b hb using fun k => ha k
  have hne (k : ℕ) : a k ≠ b k := (hb k).1
  have hsolA (k : ℕ) : SourcePsiGapSolution hp hp1 n (ψ k) (a k) := (hb k).2.1
  have hsolB (k : ℕ) : SourcePsiGapSolution hp hp1 n (ψ k) (b k) := (hb k).2.2
  choose cA hcA using fun k => (hsolA k).2
  choose RA hRA using fun k => hcA k
  obtain ⟨aLim,σ,U,c₀,R₀,hσ,haT,hgapALim,hUopen,hbase,
      hcenter₀,hgeom₀,hcoord₀,hC1,hzero₀,hbij,s,V,hVopen,hVbase,
      hs,hsa,hunique,hchartUnique,_⟩ :=
    exists_limit_sourcePsi_gap_solution hp hp1 φ hφ ψ hψ
      (fun k => (hmul k).1) n a
      (fun k => (hsolA k).1) cA RA
      (fun k m => (hRA k).1 m)
      (fun k m => (hRA k).2.1 m)
      (fun k m => (hRA k).2.2.1 m)
      (fun k => (hRA k).2.2.2)
  choose cB hcB using fun k => (hsolB k).2
  choose RB hRB using fun k => hcB k
  have hψσ : Tendsto (ψ ∘ σ) atTop (𝓝 φ) :=
    hψ.comp hσ.tendsto_atTop
  obtain ⟨bLim,τ,U₁,c₁,R₁,hτ,hbT,hgapBLim,hU₁open,hbase₁,
      hcenter₁,hgeom₁,hcoord₁,_,hzero₁,_,_⟩ :=
    exists_limit_sourcePsi_gap_solution hp hp1 φ hφ
      (ψ ∘ σ) hψσ (fun k => (hmul (σ k)).1) n (b ∘ σ)
      (fun k => (hsolB (σ k)).1) (cB ∘ σ) (RB ∘ σ)
      (fun k m => (hRB (σ k)).1 m)
      (fun k m => (hRB (σ k)).2.1 m)
      (fun k m => (hRB (σ k)).2.2.1 m)
      (fun k => (hRB (σ k)).2.2.2)
  have hneqLimit : aLim ≠ bLim := by
    intro heq
    have hψστ : Tendsto (fun k => ψ (σ (τ k))) atTop (𝓝 φ) :=
      hψσ.comp hτ.tendsto_atTop
    have haT' : Tendsto (fun k => a (σ (τ k))) atTop (𝓝 aLim) := by
      simpa only [Function.comp_def] using haT.comp hτ.tendsto_atTop
    have hbT' : Tendsto (fun k => b (σ (τ k))) atTop (𝓝 aLim) := by
      rw [heq]
      simpa only [Function.comp_def] using hbT
    have hpairA : Tendsto
        (fun k => (a (σ (τ k)),ψ (σ (τ k)))) atTop (𝓝 (aLim,φ)) :=
      haT'.prodMk_nhds hψστ
    have hpairB : Tendsto
        (fun k => (b (σ (τ k)),ψ (σ (τ k)))) atTop (𝓝 (aLim,φ)) :=
      hbT'.prodMk_nhds hψστ
    have hmemA : ∀ᶠ k : ℕ in atTop,
        (a (σ (τ k)),ψ (σ (τ k))) ∈ U ∩ V :=
      hpairA.eventually ((hUopen.inter hVopen).mem_nhds ⟨hbase,hVbase⟩)
    have hmemB : ∀ᶠ k : ℕ in atTop,
        (b (σ (τ k)),ψ (σ (τ k))) ∈ U ∩ V :=
      hpairB.eventually ((hUopen.inter hVopen).mem_nhds ⟨hbase,hVbase⟩)
    obtain ⟨k,hak,hbk⟩ := (hmemA.and hmemB).exists
    have hAk := hchartUnique
      (a (σ (τ k))) (ψ (σ (τ k))) (cA (σ (τ k))) (RA (σ (τ k)))
      hak (hmul (σ (τ k))).1
      (hRA (σ (τ k))).1 (hRA (σ (τ k))).2.1
      (hRA (σ (τ k))).2.2.1 (hRA (σ (τ k))).2.2.2
    have hBk := hchartUnique
      (b (σ (τ k))) (ψ (σ (τ k))) (cB (σ (τ k))) (RB (σ (τ k)))
      hbk (hmul (σ (τ k))).1
      (hRB (σ (τ k))).1 (hRB (σ (τ k))).2.1
      (hRB (σ (τ k))).2.2.1 (hRB (σ (τ k))).2.2.2
    exact (hne (σ (τ k))) (hAk.trans hBk.symm)
  have hsolALim : SourcePsiGapSolution hp hp1 n φ aLim :=
    ⟨hgapALim, c₀,R₀,hcenter₀,
      (fun m => let h := hgeom₀ (aLim,φ) hbase m; ⟨h.1,h.2.1,h.2.2.1⟩),
      (hcoord₀ (aLim,φ) hbase),hzero₀⟩
  have hsolBLim : SourcePsiGapSolution hp hp1 n φ bLim :=
    ⟨hgapBLim, c₁,R₁,hcenter₁,
      (fun m => let h := hgeom₁ (bLim,φ) hbase₁ m; ⟨h.1,h.2.1,h.2.2.1⟩),
      (hcoord₁ (bLim,φ) hbase₁),hzero₁⟩
  exact ⟨hφ,aLim,bLim,hneqLimit,hsolALim,hsolBLim⟩

/-- Multiplicity is relatively closed on real-type sources. -/
theorem isClosed_sourcePsiGapMultiple_on_realType
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    IsClosed {x : realTypeSourceLocus p |
      SourcePsiGapMultiple hp hp1 n x.val} := by
  apply IsSeqClosed.isClosed
  intro ψ x hψ hlim
  have hval : Tendsto (fun k => (ψ k).val) atTop (𝓝 x.val) :=
    continuous_subtype_val.continuousAt.tendsto.comp hlim
  exact SourcePsiGapMultiple.of_tendsto hp hp1 n x.val x.property
    (fun k => (ψ k).val) hval hψ

/-- Every gap-contained deleted-root vector at the free source is zero,
because every free periodic gap is a singleton. -/
theorem SourcePsiGapSolution.eq_zero_at_free
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a : DeletedCoeff p n)
    (ha : SourcePsiGapSolution hp hp1 n (0 : CoeffPair p) a) :
    a = 0 := by
  apply Subtype.ext
  ext m
  by_cases hm : m = n
  · subst m
    exact a.property
  · have hroot : displacedRoots (a : Coeff p) m = (Real.pi : ℂ) * m := by
      simpa [sourcePeriodicSegment_zero_source hp hp1 m] using ha.1 m hm
    have hadd : (Real.pi : ℂ) * m + (a : Coeff p) m =
        (Real.pi : ℂ) * m + 0 := by
      simpa only [displacedRoots,add_zero] using hroot
    exact add_left_cancel hadd

/-- The free source cannot have two distinct gap solutions. -/
theorem not_SourcePsiGapMultiple_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    ¬ SourcePsiGapMultiple hp hp1 n (0 : CoeffPair p) := by
  rintro ⟨_,a,b,hab,ha,hb⟩
  exact hab ((ha.eq_zero_at_free hp hp1 n a).trans
    (hb.eq_zero_at_free hp hp1 n b).symm)

/-- A real-type source has at most one gap-contained solution of the
selected psi equation, regardless of which valid real-centered contour
family is used to express it. -/
theorem SourcePsiGapSolution.unique_of_realType
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (a b : DeletedCoeff p n)
    (ha : SourcePsiGapSolution hp hp1 n φ a)
    (hb : SourcePsiGapSolution hp hp1 n φ b) :
    a = b := by
  let S : Set (realTypeSourceLocus p) :=
    {x | SourcePsiGapMultiple hp hp1 n x.val}
  letI : ConnectedSpace (realTypeSourceLocus p) :=
    Subtype.connectedSpace (isConnected_realTypeSourceLocus (p := p))
  have hSclopen : IsClopen S :=
    ⟨isClosed_sourcePsiGapMultiple_on_realType hp hp1 n,
      isOpen_sourcePsiGapMultiple_on_realType hp hp1 n⟩
  have hSempty : S = ∅ := by
    rcases isClopen_iff.mp hSclopen with hempty | huniv
    · exact hempty
    · exfalso
      have hz : (⟨0, by simp [realTypeSourceLocus]⟩ :
          realTypeSourceLocus p) ∈ S := by
        rw [huniv]
        trivial
      exact not_SourcePsiGapMultiple_zero hp hp1 n hz
  by_contra hne
  have hx : (⟨φ,hφ⟩ : realTypeSourceLocus p) ∈ S :=
    ⟨hφ,a,b,hne,ha,hb⟩
  rw [hSempty] at hx
  exact hx

/-- Global existence and uniqueness of the gap-contained psi roots. -/
theorem existsUnique_SourcePsiGapSolution_of_realType
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃! a : DeletedCoeff p n, SourcePsiGapSolution hp hp1 n φ a := by
  obtain ⟨_,a,ha⟩ := sourcePsiGapSolvable_of_realType hp hp1 n φ hφ
  exact ⟨a,ha,fun b hb =>
    SourcePsiGapSolution.unique_of_realType hp hp1 n φ hφ b a hb ha⟩

end NLS.ZakharovShabat
