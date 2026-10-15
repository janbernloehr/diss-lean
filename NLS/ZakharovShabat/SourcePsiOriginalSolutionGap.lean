import NLS.ZakharovShabat.SourcePsiOriginalRealRoot
import NLS.ZakharovShabat.SourcePsiOriginalDeletedOmega

/-!
# Gap placement and uniqueness of original equation zeros

A real zero whose retained roots lie in any original disk family has
its roots in the actual gaps, including collapsed gaps. Original circles
supply a gap-solution witness with exact coordinates. Uniqueness of gap
solutions then identifies this zero with the canonical real root map.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every placed real zero has its retained roots in their assigned gaps. -/
theorem SourceLemma12_4Data.originalRealEquation_zero_mem_gap
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_4Data hp hp1 W) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : realTypeSourceSubmodule p) (hφW : (φ:CoeffPair p) ∈ W) (hφV : (φ:CoeffPair p) ∈ V)
    (n : ℤ) (a : RealDeletedCoeff p n)
    (hplace : ∀ k : ℤ, k ≠ n → displacedRoots (RealDeletedCoeff.complexCLM n a:Coeff p) k ∈ D k)
    (hzero : sourcePsiOriginalRealEquation hp hp1 n a φ = 0) (m : ℤ) (hmn : m ≠ n) :
    displacedRoots (RealDeletedCoeff.complexCLM n a:Coeff p) m ∈ sourcePeriodicSegment hp hp1 φ m := by
  have hz : sourcePsiOriginalEquation hp hp1 n (RealDeletedCoeff.complexCLM n a) φ = 0 := by
    rw [← H.originalRealEquation_complex φ hφW φ.property n a, hzero, map_zero]
  obtain ⟨d,r,hr,he⟩ := hD.discs m
  let P := hD.periodCircle φ hφV m d r hr he
  have hc : sourcePsiEquationCoordinate hp hp1 n m
      (RealDeletedCoeff.complexCLM n a:Coeff p) φ (P.center:ℂ) P.radius = 0 := by
    rw [← H.equation φ hφW n (RealDeletedCoeff.complexCLM n a) m P, hz]
    rfl
  obtain ⟨z,hzgap,hzroot⟩ := exists_sourcePsiCandidate_zero_on_realGap_of_equation_zero
    hp hp1 φ φ.property n m hmn (RealDeletedCoeff.complexCLM n a:Coeff p)
    (fun j => by simp [displacedRoots]) P.center P.radius P.radius_pos P.gap
    P.closedBall_subset_omittedDomain P.sphere_subset_rootDomain hc
  obtain ⟨k,hkn,hk⟩ := (sourcePsiCandidate_eq_zero_iff_retained_root hp hp1 n _ z).mp hzroot
  have hkm : k = m := by
    by_contra hne
    exact Set.disjoint_left.mp (hD.disjoint k m hne)
      (hk ▸ hplace k hkn) (hD.gap φ hφV m hzgap)
  subst k
  rwa [hk]

/-- Original circles give a gap-solution witness with the actual equation coordinates. -/
theorem SourceLemma12_4Data.originalRealEquation_zero_gapSolution
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_4Data hp hp1 W) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : realTypeSourceSubmodule p) (hφW : (φ:CoeffPair p) ∈ W) (hφV : (φ:CoeffPair p) ∈ V)
    (n : ℤ) (a : RealDeletedCoeff p n)
    (hplace : ∀ k : ℤ, k ≠ n → displacedRoots (RealDeletedCoeff.complexCLM n a:Coeff p) k ∈ D k)
    (hzero : sourcePsiOriginalRealEquation hp hp1 n a φ = 0) :
    SourcePsiGapSolution hp hp1 n φ (RealDeletedCoeff.complexCLM n a) := by
  classical
  have hz : sourcePsiOriginalEquation hp hp1 n (RealDeletedCoeff.complexCLM n a) φ = 0 := by
    rw [← H.originalRealEquation_complex φ hφW φ.property n a, hzero, map_zero]
  choose d r hr he using hD.discs
  let P (m : ℤ) := hD.periodCircle φ hφV m (d m) (r m) (hr m) (he m)
  have hcoord (m : ℤ) :
      (sourcePsiSelectedEquationSequence hp hp1 n (fun j => (d j:ℂ)) r
        (RealDeletedCoeff.complexCLM n a) φ:Coeff p) m =
      sourcePsiEquationCoordinate hp hp1 n m (RealDeletedCoeff.complexCLM n a:Coeff p) φ (d m:ℂ) (r m) := by
    apply sourcePsiSelectedEquationSequence_apply_of_exists
    exact ⟨sourcePsiOriginalEquation hp hp1 n (RealDeletedCoeff.complexCLM n a) φ,
      fun j => H.equation φ hφW n _ j (P j)⟩
  refine ⟨H.originalRealEquation_zero_mem_gap hD φ hφW hφV n a hplace hzero,
    (fun j => (d j:ℂ)),r,(fun _ => by simp),
    (fun m => ⟨hr m,(P m).gap,(P m).closedBall_subset_omittedDomain⟩),hcoord,?_⟩
  apply Subtype.ext
  ext m
  rw [hcoord]
  have heq := H.equation φ hφW n (RealDeletedCoeff.complexCLM n a) m (P m)
  rw [hz] at heq
  exact heq.symm

/-- Pointwise uniqueness on any original isolating family. -/
theorem SourceLemma12_4Data.originalRealEquation_zero_unique
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_4Data hp hp1 W) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : realTypeSourceSubmodule p) (hφW : (φ:CoeffPair p) ∈ W) (hφV : (φ:CoeffPair p) ∈ V)
    (n : ℤ) (a : RealDeletedCoeff p n)
    (hplace : ∀ k : ℤ, k ≠ n → displacedRoots (RealDeletedCoeff.complexCLM n a:Coeff p) k ∈ D k)
    (hzero : sourcePsiOriginalRealEquation hp hp1 n a φ = 0) :
    a = sourcePsiOriginalRootReal hp hp1 n φ := by
  have he := (H.originalRealEquation_zero_gapSolution hD φ hφW hφV n a hplace hzero).eq_sourcePsiGapRoot
    hp hp1 n φ (RealDeletedCoeff.complexCLM n a)
  have he' := congrArg (RealDeletedCoeff.reCLM (p := p) n) he
  simpa only [RealDeletedCoeff.re_complex,sourcePsiOriginalRootReal] using he'

end NLS.ZakharovShabat
