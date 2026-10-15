import NLS.ZakharovShabat.SourceLemma12_10InverseBounds
import NLS.ZakharovShabat.SourcePsiOriginalAtlasPlacement

/-!
# Lemma 12.10: one original-domain complex extension for every index

All actual Proposition 12.9 root maps extend analytically to one open
simply connected neighborhood inside the unchanged preceding domain.
The extension solves the actual original equation. Every supplied original
disk family places the roots on one smaller source neighborhood; the disks
are retained. Constructed original neighborhoods give the source assertion
on their intersections with the common complex domain. Theorem 12.1 and
all preceding Proposition 12.9 data are retained for this same family.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The common complex extension of the actual Proposition 12.9 roots,
with original equation zeros and placement in supplied original disks. -/
structure SourceLemma12_10Data (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W₀ W : Set (CoeffPair p)) (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) : Prop where
  previous : SourceProposition12_9Data hp hp1 W₀
  psi : SourceTheorem12_1Data hp hp1 W₀ W s
  subset : W ⊆ W₀
  analytic : ∀ n : ℤ, AnalyticOnNhd ℂ (s n) W
  real_agreement : ∀ n : ℤ, ∀ φ : realTypeSourceSubmodule p,
    s n φ = RealDeletedCoeff.complexCLM n (sourcePsiOriginalRootReal hp hp1 n φ)
  equation : ∀ ψ ∈ W, ∀ n : ℤ, sourcePsiOriginalEquation hp hp1 n (s n ψ) ψ = 0
  original_placement : ∀ {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ},
    SourceIsolatingNeighborhoods hp hp1 V D c → IsOpen V →
      ∀ φ : realTypeSourceLocus p, φ.val ∈ V →
        ∃ δ : ℝ, 0 < δ ∧ ball φ.val δ ⊆ W ∩ V ∧
          ∀ ψ ∈ ball φ.val δ, ∀ n m : ℤ, m ≠ n → displacedRoots (s n ψ:Coeff p) m ∈ D m

/-- All original real solutions share one open simply connected complex
extension inside the unchanged preceding source domain. -/
theorem SourceProposition12_9Data.lemma12_10
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ : Set (CoeffPair p)}
    (H : SourceProposition12_9Data hp hp1 W₀) (hW₀ : IsOpen W₀) (hR : realTypeSourceLocus p ⊆ W₀) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsSimplyConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n, SourceLemma12_10Data hp hp1 W₀ W s := by
  obtain ⟨A⟩ := nonempty_sourcePsiSquaredGapComplexRootAtlas hp hp1 W₀ hW₀ hR
  let B := A.toSourcePsiComplexRootAtlas
  let H4 := H.previous.previous.previous.previous.previous
  have H12 : SourceTheorem12_1Data hp hp1 W₀ B.domain B.branch :=
    ⟨H4.previous,A.toSourcePsiIsolatingComplexRootAtlas.domain_subset,B.analytic,B.eq_sourcePsiGapRoot_of_real,
      A.locally_uniform_squared_gap_offsets,
      fun ψ hψ n m D => A.toSourcePsiIsolatingComplexRootAtlas.periodCircle_orthogonality
        W₀ (Subset.refl _) H4.previous.psiIntegrand_joint ψ hψ n m D⟩
  refine ⟨B.domain,B.isOpen_domain,B.isSimplyConnected_domain,B.realType_subset_domain,B.branch,{
    previous := H,
    psi := H12,
    subset := H12.subset,
    analytic := H12.analytic,
    real_agreement := ?_,
    equation := H12.originalEquation_zero hW₀,
    original_placement := fun hD hV φ hφV => B.original_placement_near_real hD hV φ hφV
  }⟩
  intro n φ
  rw [sourcePsiOriginalRootReal_complex]
  exact B.eq_sourcePsiGapRoot_of_real n φ

/-- Shrink the source neighborhood while preserving its supplied original disks.
This is the source's placement assertion on the intersection with the common W. -/
theorem SourceLemma12_10Data.original_assignment
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_10Data hp hp1 W₀ W s)
    {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : realTypeSourceLocus p) (hφV : φ.val ∈ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ φ.val ∈ U ∧ U ⊆ V ∧
      SourceIsolatingNeighborhoods hp hp1 U D c ∧
      ∀ ψ ∈ W ∩ U, ∀ n m : ℤ, m ≠ n → displacedRoots (s n ψ:Coeff p) m ∈ D m := by
  obtain ⟨δ,hδ,hsub,hb⟩ := H.original_placement hD hV φ hφV
  have hUV : ball φ.val δ ⊆ V := fun _ h => (hsub h).2
  exact ⟨ball φ.val δ,isOpen_ball,isConnected_ball hδ,mem_ball_self hδ,hUV,
    hD.restrict_source hUV,fun ψ hψ => hb ψ hψ.2⟩

theorem sourceLemma12_10 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ : Set (CoeffPair p), IsOpen W₀ ∧ IsConnected W₀ ∧ realTypeSourceLocus p ⊆ W₀ ∧
      ∃ W : Set (CoeffPair p), IsOpen W ∧ IsSimplyConnected W ∧ realTypeSourceLocus p ⊆ W ∧
        ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n, SourceLemma12_10Data hp hp1 W₀ W s := by
  obtain ⟨W₀,ho,hc,hr,H⟩ := sourceProposition12_9 hp hp1
  exact ⟨W₀,ho,hc,hr,H.lemma12_10 ho hr⟩


/-- Existing original isolating families give the literal local placement
assertion, with the complex domain common to all omitted indices. -/
theorem SourceLemma12_10Data.local_original_isolation
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_10Data hp hp1 W₀ W s)
    (φ : realTypeSourceLocus p) :
    ∃ V : Set (CoeffPair p), ∃ D : ℤ → Set ℂ, ∃ c : ℝ,
      IsOpen V ∧ IsConnected V ∧ φ.val ∈ V ∧ V ⊆ W₀ ∧
      SourceIsolatingNeighborhoods hp hp1 V D c ∧
      ∀ ψ ∈ W ∩ V, ∀ n m : ℤ, m ≠ n → displacedRoots (s n ψ:Coeff p) m ∈ D m := by
  obtain ⟨N,ε,_,_,V,hV,_,hφV,c,hD⟩ :=
    exists_local_source_quantitative_isolating_discs hp hp1 φ.val φ.property
  obtain ⟨δ,hδ,hsub,hb⟩ := H.original_placement hD hV φ hφV
  refine ⟨ball φ.val δ,sourceIsolatingDisc hp hp1 φ.val N ε,c,isOpen_ball,
    isConnected_ball hδ,mem_ball_self hδ,(fun _ h => H.subset (hsub h).1),
    hD.restrict_source (fun _ h => (hsub h).2),?_⟩
  exact fun ψ hψ => hb ψ hψ.2

/-- Filling the omitted root by the moving midpoint preserves every
supplied original disk on the same common source ball. -/
theorem SourceLemma12_10Data.original_filled_placement
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_10Data hp hp1 W₀ W s)
    {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : realTypeSourceLocus p) (hφV : φ.val ∈ V) :
    ∃ δ : ℝ, 0 < δ ∧ ball φ.val δ ⊆ W ∩ V ∧
      ∀ ψ ∈ ball φ.val δ, ∀ n : ℤ,
        sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n) ∈
          sourcePsiOriginalRootPlacement D := by
  obtain ⟨δ,hδ,hsub,hb⟩ := H.original_placement hD hV φ hφV
  refine ⟨δ,hδ,hsub,?_⟩
  intro ψ hψ n m
  by_cases hmn : m = n
  · subst m
    rw [displacedRoots_sourcePsiFillDeletedRoot_same]
    exact hD.gap ψ (hsub hψ).2 n (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
  · rw [displacedRoots_sourcePsiFillDeletedRoot_other n m hmn]
    exact hb ψ hψ n m hmn

end NLS.ZakharovShabat
