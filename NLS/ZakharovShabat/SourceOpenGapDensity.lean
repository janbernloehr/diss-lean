import NLS.ZakharovShabat.SourceFloquetGapOpeningWitness
import NLS.ZakharovShabat.SourcePeriodicMidpointGapContinuity
import NLS.ComplexAnalysis.RealAnalyticDenseNonzero

/-! # Density of sources with prescribed real gaps open

Every selected gap is open on a dense open part of the complete real
source space. Finite intersections retain density. Thus one can open
any prescribed finite set of gaps by arbitrarily small real source
perturbations, and continuous identities extend across their closures.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The real source locus on which one canonical periodic gap is open. -/
def sourceOpenGapRealLocus (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    Set (realTypeSourceSubmodule p) :=
  {φ | canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0}

theorem isOpen_sourceOpenGapRealLocus (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    IsOpen (sourceOpenGapRealLocus hp hp1 n) := by
  apply isOpen_ne.preimage
  apply continuous_iff_continuousAt.mpr
  intro φ
  have hL := continuousAt_canonicalPeriodicLeft_periodOne_of_realType hp hp1 φ.val φ.property n
  have hR := continuousAt_canonicalPeriodicRight_periodOne_of_realType hp hp1 φ.val φ.property n
  exact (hR.sub hL).comp continuous_subtype_val.continuousAt

/-- A gap cannot remain closed on a nonempty real open subset. -/
theorem dense_sourceOpenGapRealLocus (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    Dense (sourceOpenGapRealLocus hp hp1 n) := by
  let F : realTypeSourceSubmodule p → ℂ := fun φ => sourceFloquetGapOpening hp hp1 n φ.val
  have hF : AnalyticOnNhd ℝ F univ := by
    intro φ _
    exact ((analyticAt_sourceFloquetGapOpening_of_realType hp hp1 n φ.val φ.property).restrictScalars
      (𝕜 := ℝ)).comp ((realTypeSourceSubmodule p).subtypeL.analyticAt φ)
  obtain ⟨φ,hφ⟩ := exists_real_sourceFloquetGapOpening_ne_zero hp hp1 n
  have hd := NLS.ComplexAnalysis.dense_ne_zero_of_real_analytic F hF φ hφ
  apply hd.mono
  intro ψ hψ hgap
  exact hψ (sourceFloquetGapOpening_eq_zero_of_closed_gap hp hp1 n ψ.val ψ.property hgap)

/-- The source locus with every gap in a prescribed finite set open. -/
def sourceFiniteOpenGapRealLocus (hp : p ≠ ⊤) (hp1 : 1 < p) (S : Finset ℤ) :
    Set (realTypeSourceSubmodule p) :=
  {φ | ∀ n ∈ S, φ ∈ sourceOpenGapRealLocus hp hp1 n}

/-- Simultaneous openness and density, with no restriction on which
central or distant signed indices are selected. -/
theorem isOpen_and_dense_sourceFiniteOpenGapRealLocus
    (hp : p ≠ ⊤) (hp1 : 1 < p) (S : Finset ℤ) :
    IsOpen (sourceFiniteOpenGapRealLocus hp hp1 S) ∧ Dense (sourceFiniteOpenGapRealLocus hp hp1 S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have heq : sourceFiniteOpenGapRealLocus hp hp1 ∅ = univ := by ext φ; simp [sourceFiniteOpenGapRealLocus]
    rw [heq]
    exact ⟨isOpen_univ,dense_univ⟩
  | @insert n S _ ih =>
    have heq : sourceFiniteOpenGapRealLocus hp hp1 (insert n S) =
        sourceOpenGapRealLocus hp hp1 n ∩ sourceFiniteOpenGapRealLocus hp hp1 S := by
      ext φ
      simp only [sourceFiniteOpenGapRealLocus,mem_ofPred_eq,Finset.mem_insert,forall_eq_or_imp,mem_inter_iff]
    rw [heq]
    have ho := isOpen_sourceOpenGapRealLocus hp hp1 n
    exact ⟨ho.inter ih.1,(dense_sourceOpenGapRealLocus hp hp1 n).inter_of_isOpen_left ih.2 ho⟩

/-- Arbitrarily small real perturbations open all selected gaps while
retaining any given open condition at the original source. -/
theorem exists_mem_sourceFiniteOpenGapRealLocus_mem_open
    (hp : p ≠ ⊤) (hp1 : 1 < p) (S : Finset ℤ)
    (U : Set (realTypeSourceSubmodule p)) (hU : IsOpen U)
    (φ : realTypeSourceSubmodule p) (hφ : φ ∈ U) (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ ∈ sourceFiniteOpenGapRealLocus hp hp1 S, ψ ∈ U ∧ ‖ψ.val-φ.val‖ < ε := by
  obtain ⟨ψ,hψ⟩ := (isOpen_and_dense_sourceFiniteOpenGapRealLocus hp hp1 S).2.inter_open_nonempty
    (U ∩ ball φ ε) (hU.inter isOpen_ball) ⟨φ,hφ,mem_ball_self hε⟩
  exact ⟨ψ,hψ.2,hψ.1.1,by
    change ‖ψ-φ‖ < ε
    simpa only [mem_ball,dist_eq_norm] using hψ.1.2⟩

/-- A continuous scalar identity on the locus with selected gaps open
extends to every real source in its open domain, including closed gaps. -/
theorem eq_of_continuousOn_of_sourceFiniteOpenGaps
    (hp : p ≠ ⊤) (hp1 : 1 < p) (S : Finset ℤ)
    {U : Set (realTypeSourceSubmodule p)} (hU : IsOpen U)
    {H : realTypeSourceSubmodule p → ℂ} (hH : ContinuousOn H U) (c : ℂ)
    (hopen : ∀ ψ ∈ U, ψ ∈ sourceFiniteOpenGapRealLocus hp hp1 S → H ψ = c)
    (φ : realTypeSourceSubmodule p) (hφ : φ ∈ U) : H φ = c := by
  have hclosure : φ ∈ closure (sourceFiniteOpenGapRealLocus hp hp1 S ∩ U) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨ψ,hψ,hψU,hclose⟩ := exists_mem_sourceFiniteOpenGapRealLocus_mem_open hp hp1 S U hU φ hφ ε hε
    refine ⟨ψ,⟨hψ,hψU⟩,?_⟩
    rw [Subtype.dist_eq,dist_eq_norm,norm_sub_rev]
    exact hclose
  exact ((hH φ hφ).mono inter_subset_right).eq_const_of_mem_closure hclosure
    (fun ψ hψ => hopen ψ hψ.2 hψ.1)

end NLS.ZakharovShabat
