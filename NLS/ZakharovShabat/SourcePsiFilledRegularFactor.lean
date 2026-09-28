import NLS.ZakharovShabat.SourcePsiDeletedRootFill
import NLS.ZakharovShabat.SourcePsiRegularFactorIsolatingDisc

/-!
# Regular psi gap factor with a freely filled deleted root

The factorization of a psi contour integrand may use a root inserted
at the omitted index. The selected contour lies in a different
isolating disc, so that inserted root avoids the contour and the
regular factor is analytic throughout its closed disc.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem displacedRoots_sourcePsiFillDeletedRoot_im_eq_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (n : ℤ) (a : DeletedCoeff p n) (ξ : ℂ)
    (hroots : ∀ k : ℤ, k ≠ n →
      (displacedRoots (a : Coeff p) k).im = 0)
    (hξ : ξ.im = 0) :
    ∀ k : ℤ,
      (displacedRoots (sourcePsiFillDeletedRoot n a ξ) k).im = 0 := by
  intro k
  by_cases hkn : k = n
  · subst k
    simpa only [displacedRoots_sourcePsiFillDeletedRoot_same] using hξ
  · rw [displacedRoots_sourcePsiFillDeletedRoot_other n k hkn]
    exact hroots k hkn

/-- The inserted root avoids every other selected contour, because
that contour is contained in a disjoint isolating disc. -/
theorem sourcePsiFillDeletedRoot_avoids_otherCircle
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (n m : ℤ)
    (a : DeletedCoeff p n) (ξ : ℂ)
    (hξ : ξ ∈ sourceIsolatingDisc hp hp1 φ N ε n)
    (c : ℂ) (R : ℝ)
    (hclosed : closedBall c R ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hdisjoint : Disjoint
      (sourceIsolatingDisc hp hp1 φ N ε m)
      (sourceIsolatingDisc hp hp1 φ N ε n)) :
    ∀ z ∈ sphere c R,
      z ≠ displacedRoots (sourcePsiFillDeletedRoot n a ξ) n := by
  intro z hz heq
  have hzM := hclosed (sphere_subset_closedBall hz)
  have hzN : z ∈ sourceIsolatingDisc hp hp1 φ N ε n := by
    rw [heq]
    simpa only [displacedRoots_sourcePsiFillDeletedRoot_same] using hξ
  exact Set.disjoint_left.mp hdisjoint hzM hzN

/-- The regular gap factor built from the filled full sequence is
analytic on the selected closed contour disc. -/
theorem analyticOnNhd_sourcePsiFillDeletedRoot_gapRegularFactor
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (n m : ℤ) (a : DeletedCoeff p n) (ξ : ℂ)
    (ψ : CoeffPair p) (W : Set (CoeffPair p)) (hψW : ψ ∈ W)
    (hQ : AnalyticOnNhd ℂ
      (sourceSingleRootQuotientJointProduct hp hp1 m)
      (sourceSingleRootQuotientJointDomain hp hp1 W m))
    (c : ℂ) (R : ℝ)
    (hdom : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hclosed : closedBall c R ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hξ : ξ ∈ sourceIsolatingDisc hp hp1 φ N ε n)
    (hdisjoint : Disjoint
      (sourceIsolatingDisc hp hp1 φ N ε m)
      (sourceIsolatingDisc hp hp1 φ N ε n)) :
    AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m
          (sourcePsiFillDeletedRoot n a ξ) ψ z))
      (closedBall c R) := by
  apply analyticOnNhd_deletedPsi_gapRegularFactor_of_isolatingDisc
    hp hp1 φ N ε n m (sourcePsiFillDeletedRoot n a ξ)
      ψ W hψW hQ c R hdom hclosed
  · simpa only [displacedRoots_sourcePsiFillDeletedRoot_same] using hξ
  · exact hdisjoint

end NLS.ZakharovShabat
