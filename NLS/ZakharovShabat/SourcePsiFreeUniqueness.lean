import NLS.ZakharovShabat.SourcePsiFreeInitialSolution
import NLS.ZakharovShabat.SourcePsiEquationAllGapZero

/-!
# Uniqueness of the free initial psi solution

At the free potential every periodic gap is a single lattice point.
The collapsed-gap Cauchy formula sends a zero of each selected psi
coordinate to a zero of the entire numerator at that point. Retained
root placement in pairwise disjoint isolating discs then identifies the
zero with the correspondingly indexed displaced root. Thus every
retained displacement vanishes, without assuming that the roots are
real.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat

/-- On an isolated free contour family, the selected psi equation has
only the zero solution in the retained-root placement domain. -/
theorem sourcePsi_freeEquation_unique_of_isolating_contours
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (Niso : ℕ) (εiso : ℝ)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint
        (sourceIsolatingDisc hp hp1 (0 : CoeffPair p) Niso εiso i)
        (sourceIsolatingDisc hp hp1 (0 : CoeffPair p) Niso εiso j))
    (hfilled : ∀ m : ℤ, closedBall (c m) (R m) ⊆
      sourceIsolatingDisc hp hp1 (0 : CoeffPair p) Niso εiso m)
    (hgeom : ∀ m : ℤ,
      0 < R m ∧
      sourcePeriodicSegment hp hp1 (0 : CoeffPair p) m ⊆
        ball (c m) (R m) ∧
      closedBall (c m) (R m) ⊆
        sourceStandardRootOmittedDomain hp hp1 (0 : CoeffPair p) m ∧
      sphere (c m) (R m) ⊆
        sourceCanonicalRootDomain hp hp1 (0 : CoeffPair p))
    (a : DeletedCoeff p n)
    (hrootloc : a ∈ sourcePsiRootPlacementSet hp hp1
      (0 : CoeffPair p) Niso εiso n)
    (hcoord : ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R
        a (0 : CoeffPair p) : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (a : Coeff p) (0 : CoeffPair p) (c m) (R m))
    (hzero : sourcePsiSelectedEquationSequence hp hp1 n c R
      a (0 : CoeffPair p) = 0) :
    a = 0 := by
  apply Subtype.ext
  ext m
  by_cases hmn : m = n
  · subst m
    exact a.property
  · have hgap : canonicalPeriodicGap hp hp1
        (periodOnePotential (0 : CoeffPair p))
        (periodOnePotential_mem (0 : CoeffPair p)) m = 0 := by
      simp only [map_zero]
      exact canonicalPeriodicGap_zero hp hp1 m
    have hmid : sourceStandardRootMidpoint hp hp1
        (0 : CoeffPair p) m ∈ ball (c m) (R m) :=
      (hgeom m).2.1
        (sourcePeriodicMidpoint_mem_segment hp hp1 0 m)
    have hscalar : sourcePsiEquationCoordinate hp hp1 n m
        (a : Coeff p) 0 (c m) (R m) = 0 := by
      rw [← hcoord m, hzero]
      rfl
    have hnum := sourcePsiCandidate_zero_at_collapsedGap_of_equation_zero
      hp hp1 (0 : CoeffPair p) (by simp) n m hmn (a : Coeff p)
        hgap (c m) (R m) (hgeom m).1 hmid
        (hgeom m).2.2.1 (hgeom m).2.2.2 hscalar
    have hmidEq : sourceStandardRootMidpoint hp hp1
        (0 : CoeffPair p) m = (Real.pi : ℂ)*m := by
      simp only [sourceStandardRootMidpoint, map_zero]
      exact canonicalPeriodicMidpoint_zero hp hp1 m
    obtain ⟨k,hkn,hk⟩ :=
      (sourcePsiCandidate_eq_zero_iff_retained_root hp hp1 n
        (a : Coeff p) _).mp hnum
    have hmIso : (Real.pi : ℂ)*m ∈
        sourceIsolatingDisc hp hp1 0 Niso εiso m :=
      free_center_mem_sourceIsolatingDisc_of_selected_contour
        hp hp1 Niso εiso c R (fun j => (hgeom j).2.1) hfilled m
    have hkIso : (Real.pi : ℂ)*m ∈
        sourceIsolatingDisc hp hp1 0 Niso εiso k := by
      rw [← hmidEq, ← hk]
      exact hrootloc k hkn
    have hkm : k = m := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisjoint m k (Ne.symm hne))
        hmIso hkIso
    subst k
    have hroot : displacedRoots (a : Coeff p) m =
        (Real.pi : ℂ)*m := by
      simpa only [hmidEq] using hk
    have ha : (a : Coeff p) m = 0 :=
      add_left_cancel (show (Real.pi : ℂ)*m + (a : Coeff p) m =
        (Real.pi : ℂ)*m + 0 by simpa [displacedRoots] using hroot)
    simpa using ha

/-- The free source has a local `C¹` selected psi branch whose initial
value is the unique free equation zero with retained roots in the
same isolated root-placement domain. -/
theorem exists_local_sourcePsi_C1_branch_at_free_source_unique
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      ((0 : DeletedCoeff p n),(0 : CoeffPair p)) ∈ U ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        ∃ Niso : ℕ, ∃ εiso : ℝ,
        ∃ s : CoeffPair p → DeletedCoeff p n,
          ContDiffAt ℂ 1 s 0 ∧ s 0 = 0 ∧
          (∀ a : DeletedCoeff p n,
            a ∈ sourcePsiRootPlacementSet hp hp1
              (0 : CoeffPair p) Niso εiso n →
            (a,(0 : CoeffPair p)) ∈ U →
            sourcePsiSelectedEquationSequence hp hp1 n c R a 0 = 0 →
            a = 0) ∧
          ∀ᶠ ψ in 𝓝 (0 : CoeffPair p),
            (s ψ,ψ) ∈ U ∩
              sourcePsiRootPlacementDomain hp hp1
                (0 : CoeffPair p) Niso εiso n ∧
            sourcePsiSelectedEquationSequence hp hp1 n c R (s ψ) ψ = 0 := by
  obtain ⟨U,hUopen,hbase,c,R,Niso,εiso,
      hdisjoint,hfilled,_,hgeom,hcoord,s,_,_,_,hs,hs0,_,hsolution⟩ :=
    exists_local_sourcePsi_C1_branch_at_free_source hp hp1 n
  have hunique (a : DeletedCoeff p n)
      (hrootloc : a ∈ sourcePsiRootPlacementSet hp hp1
        (0 : CoeffPair p) Niso εiso n)
      (haU : (a,(0 : CoeffPair p)) ∈ U)
      (hzero : sourcePsiSelectedEquationSequence hp hp1 n c R a 0 = 0) :
      a = 0 :=
    sourcePsi_freeEquation_unique_of_isolating_contours
      hp hp1 n Niso εiso c R hdisjoint hfilled
        (hgeom (0,0) hbase) a hrootloc (hcoord (a,0) haU) hzero
  exact ⟨U,hUopen,hbase,c,R,Niso,εiso,s,hs,hs0,hunique,hsolution⟩

end NLS.ZakharovShabat
