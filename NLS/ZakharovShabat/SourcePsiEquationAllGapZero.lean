import NLS.ZakharovShabat.SourcePsiEquationCollapsedGapZero
import NLS.ZakharovShabat.SourcePsiSelectedKernelGapZeroSequence
import NLS.ZakharovShabat.SourcePsiDeletedProductNonzero
import NLS.ZakharovShabat.SourcePsiIsolatingRootSeparation
import NLS.ZakharovShabat.SourcePsiGlobalEquationAnalytic

/-!
# Zeros of a solved psi equation lie in the selected periodic gaps

The actual numerator has exactly its retained displaced roots as
zeros. A vanishing scalar equation gives a numerator zero in the
selected gap, whether that gap is open or collapsed. Disjoint
isolating discs identify its index with the selected root.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The entire psi numerator has precisely the retained displaced
roots as zeros, with no localization hypothesis. -/
theorem sourcePsiCandidate_eq_zero_iff_retained_root
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : Coeff p) (z : ℂ) :
    sourcePsiCandidate n (z,a) = 0 ↔
      ∃ k : ℤ, k ≠ n ∧ displacedRoots a k = z := by
  constructor
  · intro hz
    by_contra hnone
    have hother : ∀ k : ℤ, k ≠ n → z ≠ displacedRoots a k := by
      intro k hkn he
      exact hnone ⟨k,hkn,he.symm⟩
    have hprod := jointDeletedSingleSpectralProduct_ne_zero_of_off_other
      hp hp1 n z a hother
    change (-2 : ℂ) * jointDeletedSingleSpectralProduct n (z,a) = 0 at hz
    exact hprod ((mul_eq_zero.mp hz).resolve_left (by norm_num))
  · rintro ⟨k,hkn,hk⟩
    rw [← hk]
    exact sourcePsiCandidate_other_root hp hp1 n k hkn a

/-- A vanishing scalar psi equation at a real-type source gives a
zero of its entire numerator in the selected periodic gap. -/
theorem exists_sourcePsiCandidate_zero_on_realGap_of_equation_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (hmn : m ≠ n) (a : Coeff p)
    (hroots : ∀ j : ℤ, (displacedRoots a j).im = 0)
    (x R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball (x:ℂ) R)
    (hdom : closedBall (x:ℂ) R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere (x:ℂ) R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (hzero : sourcePsiEquationCoordinate hp hp1 n m
      a ψ (x:ℂ) R = 0) :
    ∃ μ ∈ sourcePeriodicSegment hp hp1 ψ m,
      sourcePsiCandidate n (μ,a) = 0 := by
  rcases sourcePeriodicGap_eq_zero_or_open hp hp1 ψ hψ m with hgap | hopen
  · let τ := sourceStandardRootMidpoint hp hp1 ψ m
    have hmid : τ ∈ ball (x:ℂ) R :=
      hseg (sourcePeriodicMidpoint_mem_segment hp hp1 ψ m)
    have hzeroτ := sourcePsiCandidate_zero_at_collapsedGap_of_equation_zero
      hp hp1 ψ hψ n m hmn a hgap (x:ℂ) R hR hmid hdom hcircle hzero
    exact ⟨τ,sourcePeriodicMidpoint_mem_segment hp hp1 ψ m,hzeroτ⟩
  · obtain ⟨μ,hμ,hzeroμ⟩ :=
      exists_sourcePsiCandidate_zero_on_openGap_of_equation_zero
        hp hp1 ψ hψ n m hmn a hroots hopen x R hR hseg hdom
          hcircle hzero
    exact ⟨μ,sourceStandardRoot_gapSegment_subset_periodicSegment
      hp hp1 ψ m hμ,hzeroμ⟩

/-- At a real solution with retained roots in pairwise disjoint
isolating discs, the selected root lies in its periodic gap. This is
the root-placement conclusion used at the start of Proposition 12.9. -/
theorem displacedRoot_mem_periodicSegment_of_psiEquation_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (N : ℕ) (ε : ℝ)
    (n m : ℤ) (hmn : m ≠ n) (a : Coeff p)
    (hroots : ∀ j : ℤ, (displacedRoots a j).im = 0)
    (hsegIso : sourcePeriodicSegment hp hp1 ψ m ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hrootloc : ∀ k : ℤ, k ≠ n →
      displacedRoots a k ∈ sourceIsolatingDisc hp hp1 φ N ε k)
    (hdisjoint : ∀ k : ℤ, k ≠ m →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε m)
        (sourceIsolatingDisc hp hp1 φ N ε k))
    (x R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball (x:ℂ) R)
    (hdom : closedBall (x:ℂ) R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere (x:ℂ) R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (hzero : sourcePsiEquationCoordinate hp hp1 n m
      a ψ (x:ℂ) R = 0) :
    displacedRoots a m ∈ sourcePeriodicSegment hp hp1 ψ m := by
  obtain ⟨μ,hμ,hzeroμ⟩ :=
    exists_sourcePsiCandidate_zero_on_realGap_of_equation_zero
      hp hp1 ψ hψ n m hmn a hroots x R hR hseg hdom hcircle hzero
  obtain ⟨k,hkn,hkμ⟩ :=
    (sourcePsiCandidate_eq_zero_iff_retained_root hp hp1 n a μ).mp hzeroμ
  have hμM : μ ∈ sourceIsolatingDisc hp hp1 φ N ε m := hsegIso hμ
  have hμK : μ ∈ sourceIsolatingDisc hp hp1 φ N ε k := by
    rw [← hkμ]
    exact hrootloc k hkn
  have hkm : k = m := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisjoint k hne) hμM hμK
  subst k
  rw [hkμ]
  exact hμ

/-- The same gap conclusion for a zero of the selected Banach-valued
psi equation on one common contour family. -/
theorem retainedRoots_mem_periodicSegments_of_selectedEquation_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (N : ℕ) (ε : ℝ) (n : ℤ) (a : DeletedCoeff p n)
    (hroots : ∀ j : ℤ,
      (displacedRoots (a : Coeff p) j).im = 0)
    (hrootloc : ∀ k : ℤ, k ≠ n →
      displacedRoots (a : Coeff p) k ∈
        sourceIsolatingDisc hp hp1 φ N ε k)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hcenter : ∀ m : ℤ, (c m).im = 0)
    (hgeom : ∀ m : ℤ,
      0 < R m ∧
      sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (R m) ∧
      closedBall (c m) (R m) ⊆
        sourceStandardRootOmittedDomain hp hp1 ψ m ∧
      sphere (c m) (R m) ⊆
        sourceCanonicalRootDomain hp hp1 ψ)
    (hfilled : ∀ m : ℤ,
      closedBall (c m) (R m) ⊆
        sourceIsolatingDisc hp hp1 φ N ε m)
    (hcoord : ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R a ψ : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (a : Coeff p) ψ (c m) (R m))
    (hzero : sourcePsiSelectedEquationSequence hp hp1 n c R a ψ = 0) :
    ∀ m : ℤ, m ≠ n →
      displacedRoots (a : Coeff p) m ∈
        sourcePeriodicSegment hp hp1 ψ m := by
  intro m hmn
  let x : ℝ := (c m).re
  have hx : (x : ℂ) = c m := by
    apply Complex.ext
    · rfl
    · simpa [x] using (hcenter m).symm
  have hsegIso : sourcePeriodicSegment hp hp1 ψ m ⊆
      sourceIsolatingDisc hp hp1 φ N ε m := by
    intro z hz
    exact hfilled m (ball_subset_closedBall ((hgeom m).2.1 hz))
  have hscalarZero : sourcePsiEquationCoordinate hp hp1 n m
      (a : Coeff p) ψ (c m) (R m) = 0 := by
    rw [← hcoord m, hzero]
    rfl
  exact displacedRoot_mem_periodicSegment_of_psiEquation_zero
    hp hp1 φ ψ hψ N ε n m hmn (a : Coeff p) hroots hsegIso
      hrootloc (fun k hkm => hdisjoint m k (Ne.symm hkm))
      x (R m) (hgeom m).1
      (by simpa only [hx] using (hgeom m).2.1)
      (by simpa only [hx] using (hgeom m).2.2.1)
      (by simpa only [hx] using (hgeom m).2.2.2)
      (by simpa only [hx] using hscalarZero)

end NLS.ZakharovShabat
