import NLS.ZakharovShabat.SourcePsiIsolatingComplexRootAtlas

/-!
# Lemma 12.10 in the source coefficient spaces

The canonical real psi root maps extend, simultaneously in every signed
deleted index, to one open simply connected neighborhood contained in
the almost-real spectral neighborhood of Lemma 10.1. Around each real
source, one source ball and one assigned disjoint isolating-disc family
place all retained roots and the moving spectral clusters. The omitted
root can be filled with the moving periodic midpoint. Actual retained
contour orthogonality holds throughout the common complex domain.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual almost-real spectral neighborhood supplied by Lemma 10.1. -/
def SourceSpectralIsolationNeighborhood (hp : p ≠ ⊤) (hp1 : 1 < p)
    (U : Set (CoeffPair p)) : Prop :=
  IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
    ∀ ψ ∈ U, ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ ψ ∈ V ∧ V ⊆ U ∧
      ∃ φ : CoeffPair p, ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
        (∀ χ ∈ V, ∀ m : ℤ,
          sourceSpectralCluster hp hp1 χ m ⊆ sourceIsolatingDisc hp hp1 φ N ε m) ∧
        (∀ χ ∈ V, ∀ m : ℤ,
          sourcePeriodicSegment hp hp1 χ m ⊆ sourceIsolatingDisc hp hp1 φ N ε m) ∧
        (∀ i j : ℤ, i ≠ j →
          Disjoint (sourceIsolatingDisc hp hp1 φ N ε i) (sourceIsolatingDisc hp hp1 φ N ε j))

/-- Complex extension, actual orthogonality, and the index-independent
local isolating-root placement asserted in Lemma 12.10. -/
structure SourcePsiIsolatingComplexExtension (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) : Prop where
  analytic : ∀ n, AnalyticOnNhd ℂ (s n) W
  real_agreement : ∀ n, ∀ φ : realTypeSourceLocus p, s n φ.val = sourcePsiGapRoot hp hp1 n φ
  contour_zero : ∀ n, ∀ ψ ∈ W, ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
    sourcePsiRealCenteredContourFamily hp hp1 ψ c R ∧
      ∀ m : ℤ, m ≠ n → sourcePsiContour hp hp1 n (s n ψ : Coeff p) ψ (c m) (R m) = 0
  isolation : ∀ φ : realTypeSourceLocus p, ∃ δ : ℝ, 0 < δ ∧
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧ ball φ.val δ ⊆ W ∧
      (∀ ψ ∈ ball φ.val δ, ∀ m : ℤ,
        sourceSpectralCluster hp hp1 ψ m ⊆ sourceIsolatingDisc hp hp1 φ.val N ε m) ∧
      (∀ i j : ℤ, i ≠ j →
        Disjoint (sourceIsolatingDisc hp hp1 φ.val N ε i) (sourceIsolatingDisc hp hp1 φ.val N ε j)) ∧
      (∀ n : ℤ, ∀ ψ ∈ ball φ.val δ,
        s n ψ ∈ sourcePsiRootPlacementSet hp hp1 φ.val N ε n) ∧
      (∀ n : ℤ, ∀ ψ ∈ ball φ.val δ,
        ∃ ξ : ℂ, ξ ∈ sourcePeriodicSegment hp hp1 ψ n ∧
          ∀ m : ℤ, displacedRoots (sourcePsiFillDeletedRoot n (s n ψ) ξ) m ∈
            sourceIsolatingDisc hp hp1 φ.val N ε m)

/-- The common simply connected extension can be constructed inside
any prescribed open complex neighborhood of the entire real locus. -/
theorem exists_sourcePsiIsolatingComplexExtension_in_open
    (hp : p ≠ ⊤) (hp1 : 1 < p) (U : Set (CoeffPair p))
    (hU : IsOpen U) (hreal : realTypeSourceLocus p ⊆ U) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsSimplyConnected W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ U ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n, SourcePsiIsolatingComplexExtension hp hp1 W s := by
  obtain ⟨A⟩ := nonempty_sourcePsiIsolatingComplexRootAtlas hp hp1 U hU hreal
  let B := A.toSourcePsiComplexRootAtlas
  refine ⟨B.domain,B.isOpen_domain,B.isSimplyConnected_domain,B.realType_subset_domain,
    A.domain_subset,B.branch,{
      analytic := B.analytic, real_agreement := B.eq_sourcePsiGapRoot_of_real,
      contour_zero := B.contour_zero, isolation := ?_
    }⟩
  intro φ
  exact ⟨(B.localBranch φ).sourceRadius,(B.localBranch φ).sourceRadius_pos,
    A.cutoff φ,A.enlargement φ,A.enlargement_pos φ,A.enlargement_le φ,
    subset_iUnion B.sourceBall φ,A.clusters φ,A.disjoint φ,A.global_placement φ,A.filled_placement φ⟩

/-- Source-space version of Lemma 12.10, with the actual spectral
neighborhood, one common complex domain, and assigned root placement. -/
theorem exists_sourcePsi_lemma12_10 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ U W : Set (CoeffPair p), SourceSpectralIsolationNeighborhood hp hp1 U ∧
      IsOpen W ∧ IsSimplyConnected W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ U ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n, SourcePsiIsolatingComplexExtension hp hp1 W s := by
  obtain ⟨U,hU,hUconn,hreal,hgeometry⟩ := exists_global_source_isolating_neighborhood hp hp1
  obtain ⟨W,hW,hWsimple,hWreal,hWU,s,hs⟩ :=
    exists_sourcePsiIsolatingComplexExtension_in_open hp hp1 U hU hreal
  exact ⟨U,W,⟨hU,hUconn,hreal,hgeometry⟩,hW,hWsimple,hWreal,hWU,s,hs⟩

namespace SourcePsiIsolatingComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual entire numerators are jointly analytic in the spectral
parameter and the complex potential on the common source domain. -/
theorem analytic_numerator_joint (hs : SourcePsiIsolatingComplexExtension hp hp1 W s) (n : ℤ) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => sourcePsiCandidate n (t.1,(s n t.2 : Coeff p)))
      (univ ×ˢ W) := by
  intro t ht
  let i : DeletedCoeff p n →L[ℂ] Coeff p := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL
  have hroot : AnalyticAt ℂ (fun u : ℂ × CoeffPair p => (s n u.2 : Coeff p)) t :=
    (i.analyticAt _).comp ((hs.analytic n t.2 ht.2).comp analyticAt_snd)
  exact (analyticOnNhd_sourcePsiCandidate hp hp1 n (t.1,(s n t.2 : Coeff p)) (mem_univ _)).comp
    (f := fun u : ℂ × CoeffPair p => (u.1,(s n u.2 : Coeff p))) (analyticAt_fst.prod hroot)

theorem entire_numerator (hs : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (n : ℤ) (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    Differentiable ℂ (fun z => sourcePsiCandidate n (z,(s n ψ : Coeff p))) := by
  intro z
  exact ((hs.analytic_numerator_joint n (z,ψ) ⟨mem_univ _,hψ⟩).comp
    (f := fun w : ℂ => (w,ψ)) (analyticAt_id.prod analyticAt_const)).differentiableAt

end SourcePsiIsolatingComplexExtension

end NLS.ZakharovShabat
