import NLS.ZakharovShabat.SourcePsiC1ImplicitStep
import NLS.ZakharovShabat.SourcePsiFree

/-!
# The free initial solution for the selected psi equation

The local contour family used for Jacobian bijectivity surrounds each
free lattice point and lies in pairwise disjoint isolating discs.
Free-contour orthogonality therefore gives the actual selected
Banach-valued equation zero at the free source and zero deleted roots.
The `C¹` implicit theorem then starts a solution branch there.
-/

noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat

/-- The free lattice point belongs to its assigned isolating disc
whenever the selected contour contains the free periodic segment. -/
theorem free_center_mem_sourceIsolatingDisc_of_selected_contour
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (Niso : ℕ) (εiso : ℝ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hsegment : ∀ m : ℤ,
      sourcePeriodicSegment hp hp1 (0 : CoeffPair p) m ⊆
        ball (c m) (R m))
    (hfilled : ∀ m : ℤ, closedBall (c m) (R m) ⊆
      sourceIsolatingDisc hp hp1 (0 : CoeffPair p) Niso εiso m)
    (m : ℤ) :
    (Real.pi : ℂ)*m ∈
      sourceIsolatingDisc hp hp1 (0 : CoeffPair p) Niso εiso m := by
  have hmseg : (Real.pi : ℂ)*m ∈
      sourcePeriodicSegment hp hp1 (0 : CoeffPair p) m := by
    rw [sourcePeriodicSegment_zero_source hp hp1 m]
    simp
  exact hfilled m (ball_subset_closedBall (hsegment m hmseg))

/-- A selected free contour avoids every other free periodic gap
when the assigned isolating discs are pairwise disjoint. -/
theorem selected_free_contour_avoids_other_gap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (Niso : ℕ) (εiso : ℝ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hsegment : ∀ m : ℤ,
      sourcePeriodicSegment hp hp1 (0 : CoeffPair p) m ⊆
        ball (c m) (R m))
    (hfilled : ∀ m : ℤ, closedBall (c m) (R m) ⊆
      sourceIsolatingDisc hp hp1 (0 : CoeffPair p) Niso εiso m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint
        (sourceIsolatingDisc hp hp1 (0 : CoeffPair p) Niso εiso i)
        (sourceIsolatingDisc hp hp1 (0 : CoeffPair p) Niso εiso j))
    (n m : ℤ) (hmn : m ≠ n) :
    closedBall (c m) (R m) ⊆
      (sourcePeriodicSegment hp hp1 (0 : CoeffPair p) n)ᶜ := by
  intro z hz
  rw [mem_compl_iff, sourcePeriodicSegment_zero_source hp hp1 n]
  intro hzn
  have hzn' : z = (Real.pi : ℂ)*n := mem_singleton_iff.mp hzn
  have hzm : z ∈ sourceIsolatingDisc hp hp1
      (0 : CoeffPair p) Niso εiso m := hfilled m hz
  have hznIso : z ∈ sourceIsolatingDisc hp hp1
      (0 : CoeffPair p) Niso εiso n := by
    rw [hzn']
    exact free_center_mem_sourceIsolatingDisc_of_selected_contour
      hp hp1 Niso εiso c R hsegment hfilled n
  exact Set.disjoint_left.mp (hdisjoint m n hmn) hzm hznIso

/-- At the free source, all coordinates of the selected psi equation
vanish on any pairwise isolated selected contour family. -/
theorem sourcePsiSelectedEquationSequence_zero_of_isolating_contours
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (Niso : ℕ) (εiso : ℝ)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hR : ∀ m : ℤ, 0 < R m)
    (hsegment : ∀ m : ℤ,
      sourcePeriodicSegment hp hp1 (0 : CoeffPair p) m ⊆
        ball (c m) (R m))
    (hcircle : ∀ m : ℤ,
      sphere (c m) (R m) ⊆
        sourceCanonicalRootDomain hp hp1 (0 : CoeffPair p))
    (hfilled : ∀ m : ℤ, closedBall (c m) (R m) ⊆
      sourceIsolatingDisc hp hp1 (0 : CoeffPair p) Niso εiso m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint
        (sourceIsolatingDisc hp hp1 (0 : CoeffPair p) Niso εiso i)
        (sourceIsolatingDisc hp hp1 (0 : CoeffPair p) Niso εiso j))
    (hcoord : ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R
        (0 : DeletedCoeff p n) (0 : CoeffPair p) : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (0 : Coeff p) (0 : CoeffPair p) (c m) (R m)) :
    sourcePsiSelectedEquationSequence hp hp1 n c R
      (0 : DeletedCoeff p n) (0 : CoeffPair p) = 0 := by
  apply Subtype.ext
  ext m
  rw [hcoord m]
  by_cases hmn : m = n
  · subst m
    simp [sourcePsiEquationCoordinate]
  · have havoid := selected_free_contour_avoids_other_gap
      hp hp1 Niso εiso c R hsegment hfilled hdisjoint n m hmn
    have hfree := sourcePsiFreeContour_off_diagonal
      hp hp1 n (c m) (R m) (hR m).le (hcircle m) havoid
    rw [sourcePsiEquationCoordinate,
      sourcePsiContour_zero hp hp1 n (c m) (R m) (hR m).le,
      hfree]
    simp

/-- The free potential and zero root displacements start a local
`C¹` solution branch of the actual selected Banach-valued equation.
The branch remains in the same open retained-root domain near zero. -/
theorem exists_local_sourcePsi_C1_branch_at_free_source
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      ((0 : DeletedCoeff p n),(0 : CoeffPair p)) ∈ U ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        ∃ Niso : ℕ, ∃ εiso : ℝ,
        (∀ i j : ℤ, i ≠ j →
          Disjoint
            (sourceIsolatingDisc hp hp1 (0 : CoeffPair p) Niso εiso i)
            (sourceIsolatingDisc hp hp1 (0 : CoeffPair p) Niso εiso j)) ∧
        (∀ m : ℤ, closedBall (c m) (R m) ⊆
          sourceIsolatingDisc hp hp1 (0 : CoeffPair p) Niso εiso m) ∧
        (∀ t ∈ U, ∀ m : ℤ,
          0 < R m ∧
          sourcePeriodicSegment hp hp1 t.2 m ⊆ ball (c m) (R m) ∧
          closedBall (c m) (R m) ⊆
            sourceStandardRootOmittedDomain hp hp1 t.2 m ∧
          sphere (c m) (R m) ⊆
            sourceCanonicalRootDomain hp hp1 t.2) ∧
        (∀ t ∈ U, ∀ m : ℤ,
          (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
            sourcePsiEquationCoordinate hp hp1 n m
              (t.1 : Coeff p) t.2 (c m) (R m)) ∧
        ∃ s : CoeffPair p → DeletedCoeff p n,
          ContDiffAt ℂ 1 s 0 ∧ s 0 = 0 ∧
          ∀ᶠ ψ in 𝓝 (0 : CoeffPair p),
            (s ψ,ψ) ∈ U ∩
              sourcePsiRootPlacementDomain hp hp1
                (0 : CoeffPair p) Niso εiso n ∧
            sourcePsiSelectedEquationSequence hp hp1 n c R (s ψ) ψ = 0 := by
  obtain ⟨U,hUopen,hbase,c,R,Niso,εiso,
      hdisjoint,hfilled,hgeom,hcoord,hC1,hbij⟩ :=
    exists_local_sourcePsi_selectedJacobian_bijective
      hp hp1 (0 : CoeffPair p) (by simp) n (0 : DeletedCoeff p n)
  have hR (m : ℤ) : 0 < R m :=
    (hgeom (0,0) hbase m).1
  have hsegment (m : ℤ) :
      sourcePeriodicSegment hp hp1 (0 : CoeffPair p) m ⊆
        ball (c m) (R m) :=
    (hgeom (0,0) hbase m).2.1
  have hcircle (m : ℤ) :
      sphere (c m) (R m) ⊆
        sourceCanonicalRootDomain hp hp1 (0 : CoeffPair p) :=
    (hgeom (0,0) hbase m).2.2.2
  have hcoord0 (m : ℤ) :
      (sourcePsiSelectedEquationSequence hp hp1 n c R
        (0 : DeletedCoeff p n) (0 : CoeffPair p) : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (0 : Coeff p) (0 : CoeffPair p) (c m) (R m) :=
    hcoord (0,0) hbase m
  have hzero : sourcePsiSelectedEquationSequence hp hp1 n c R
      (0 : DeletedCoeff p n) (0 : CoeffPair p) = 0 :=
    sourcePsiSelectedEquationSequence_zero_of_isolating_contours
      hp hp1 n Niso εiso c R hR hsegment hcircle
        hfilled hdisjoint hcoord0
  have hrootloc : (0 : DeletedCoeff p n) ∈
      sourcePsiRootPlacementSet hp hp1 (0 : CoeffPair p) Niso εiso n := by
    intro j _
    have hj := free_center_mem_sourceIsolatingDisc_of_selected_contour
      hp hp1 Niso εiso c R hsegment hfilled j
    simpa [displacedRoots] using hj
  have hroots : ∀ j : ℤ,
      (displacedRoots ((0 : DeletedCoeff p n) : Coeff p) j).im = 0 := by
    intro j
    simp [displacedRoots,Complex.mul_im]
  have hF : ContDiffAt ℂ 1
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2)
      ((0 : DeletedCoeff p n),(0 : CoeffPair p)) :=
    hC1.contDiffAt (hUopen.mem_nhds hbase)
  obtain ⟨s,hs,hs0,hzeros⟩ := exists_C1_sourcePsi_local_solution
    hp hp1 n c R 0 0 hF hzero
      (hbij 0 0 hbase (by simp) hroots hrootloc)
  have hDopen : IsOpen (U ∩
      sourcePsiRootPlacementDomain hp hp1
        (0 : CoeffPair p) Niso εiso n) :=
    hUopen.inter (isOpen_sourcePsiRootPlacementDomain
      hp hp1 (0 : CoeffPair p) Niso εiso n)
  have hplacement : ∀ᶠ ψ in 𝓝 (0 : CoeffPair p),
      (s ψ,ψ) ∈ U ∩
        sourcePsiRootPlacementDomain hp hp1
          (0 : CoeffPair p) Niso εiso n := by
    have hcontinuous : ContinuousAt
        (fun ψ : CoeffPair p => (s ψ,ψ)) 0 :=
      hs.continuousAt.prodMk continuousAt_id
    apply hcontinuous.eventually
    apply hDopen.mem_nhds
    simpa only [hs0,sourcePsiRootPlacementDomain] using
      (show ((0 : DeletedCoeff p n),(0 : CoeffPair p)) ∈
        U ∩ sourcePsiRootPlacementDomain hp hp1
          (0 : CoeffPair p) Niso εiso n from ⟨hbase,hrootloc⟩)
  refine ⟨U,hUopen,hbase,c,R,Niso,εiso,
    hdisjoint,hfilled,hgeom,hcoord,s,hs,hs0,?_⟩
  filter_upwards [hplacement,hzeros] with ψ hψ hψzero
  exact ⟨hψ,hψzero⟩

end NLS.ZakharovShabat
