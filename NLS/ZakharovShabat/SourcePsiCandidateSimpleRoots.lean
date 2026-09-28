import NLS.ZakharovShabat.SourcePsiCandidateRootVariation
import NLS.ZakharovShabat.SourcePsiDeletedProductNonzero
import NLS.ZakharovShabat.SourcePsiIsolatingRootSeparation

/-!
# Simple retained zeros of the entire psi numerator

The full single-root product has a linear factor at each displaced root.
After deleting that root, the remaining product is nonzero whenever the
root is distinct from the others. The same simplicity then transfers to
the psi numerator with a different index deleted.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The spectral derivative of the full single-root product at one of
its zeros is the remaining deleted product, with the exact normalization. -/
theorem deriv_jointSingleSpectralProduct_at_displacedRoot
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : Coeff p) (k : ℤ) :
    deriv (fun z : ℂ => jointSingleSpectralProduct (z,a))
      (displacedRoots a k) =
      -2 * jointDeletedSingleSpectralProduct k (displacedRoots a k,a) := by
  let σ := displacedRoots a k
  let G : ℂ → ℂ := fun z => jointDeletedSingleSpectralProduct k (z,a)
  have hG : DifferentiableAt ℂ G σ := by
    exact ((analyticOnNhd_jointDeletedSingleSpectralProduct hp hp1 k
      (σ,a) (Set.mem_univ _)).comp
        (f := fun z : ℂ => (z,a))
        (analyticAt_id.prod analyticAt_const)).differentiableAt
  have hlin : HasDerivAt (fun z : ℂ => 2 * (σ-z)) (-2) σ := by
    simpa using ((hasDerivAt_const σ σ).sub (hasDerivAt_id σ)).const_mul (2 : ℂ)
  have hprod := hlin.mul hG.hasDerivAt
  have hfun : ((fun z : ℂ => 2 * (σ-z)) * G) =
      (fun z : ℂ => 2 * (σ-z) * G z) := by
    funext z
    rfl
  rw [hfun] at hprod
  have heq : (fun z : ℂ => jointSingleSpectralProduct (z,a)) =
      (fun z : ℂ => 2 * (σ-z) * G z) := by
    funext z
    exact jointSingleSpectralProduct_eq_deleted hp hp1 k (z,a)
  rw [heq]
  simpa [σ, G] using hprod.deriv

/-- A displaced root has multiplicity one in the full product if it
does not coincide with any other displaced root. -/
theorem deriv_jointSingleSpectralProduct_ne_zero_of_distinct
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : Coeff p) (k : ℤ)
    (hdistinct : ∀ j : ℤ, j ≠ k →
      displacedRoots a k ≠ displacedRoots a j) :
    deriv (fun z : ℂ => jointSingleSpectralProduct (z,a))
      (displacedRoots a k) ≠ 0 := by
  rw [deriv_jointSingleSpectralProduct_at_displacedRoot hp hp1 a k]
  exact mul_ne_zero (by norm_num)
    (jointDeletedSingleSpectralProduct_ne_zero_of_off_other
      hp hp1 k (displacedRoots a k) a hdistinct)

/-- Every retained zero of the psi numerator is simple when the
displaced roots are pairwise distinct. -/
theorem deriv_sourcePsiCandidate_ne_zero_at_retained_root
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (hkn : k ≠ n) (a : Coeff p)
    (hdistinct : ∀ j : ℤ, j ≠ k →
      displacedRoots a k ≠ displacedRoots a j) :
    deriv (fun z : ℂ => sourcePsiCandidate n (z,a))
      (displacedRoots a k) ≠ 0 := by
  let σ := displacedRoots a k
  let ψ : ℂ → ℂ := fun z => sourcePsiCandidate n (z,a)
  have hψ : DifferentiableAt ℂ ψ σ :=
    (differentiable_sourcePsiCandidate hp hp1 n a) σ
  have hlin : HasDerivAt (fun z : ℂ => z-displacedRoots a n) 1 σ := by
    simpa using (hasDerivAt_id σ).sub_const (displacedRoots a n)
  have hprod := hlin.mul hψ.hasDerivAt
  have hfun : ((fun z : ℂ => z-displacedRoots a n) * ψ) =
      (fun z : ℂ => (z-displacedRoots a n) * ψ z) := by
    funext z
    rfl
  rw [hfun] at hprod
  have heq : (fun z : ℂ => jointSingleSpectralProduct (z,a)) =
      (fun z : ℂ => (z-displacedRoots a n) * ψ z) := by
    funext z
    rw [jointSingleSpectralProduct_eq_deleted hp hp1 n (z,a)]
    dsimp [ψ, sourcePsiCandidate]
    ring
  have hψzero : ψ σ = 0 :=
    sourcePsiCandidate_other_root hp hp1 n k hkn a
  have hderiv : deriv (fun z : ℂ => jointSingleSpectralProduct (z,a)) σ =
      (σ-displacedRoots a n) * deriv ψ σ := by
    rw [heq]
    simpa [hψzero] using hprod.deriv
  have hfull := deriv_jointSingleSpectralProduct_ne_zero_of_distinct
    hp hp1 a k hdistinct
  intro hzero
  apply hfull
  rw [hderiv, hzero, mul_zero]

/-- Once the entire numerator variation vanishes at every retained
root, separated roots force every coefficient of a deleted direction
to vanish. This isolates the interpolation part of Lemma 12.7. -/
theorem sourcePsiCandidate_direction_eq_zero_of_root_variation_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a h : Coeff p)
    (hsep : Function.Injective (displacedRoots a))
    (hdeleted : h n = 0)
    (hvariation : ∀ k : ℤ, k ≠ n →
      (fderiv ℂ (sourcePsiCandidate (p := p) n)
        (displacedRoots a k,a)) (0,h) = 0) :
    h = 0 := by
  ext k
  by_cases hkn : k = n
  · subst k
    simpa using hdeleted
  · have hsimple := deriv_sourcePsiCandidate_ne_zero_at_retained_root
      hp hp1 n k hkn a (fun j hj => hsep.ne hj.symm)
    have hk := sourcePsiCandidate_direction_coeff_eq_zero_of_simple_root
      hp hp1 n k hkn a h hsimple (hvariation k hkn)
    simpa using hk

/-- Root placement in the pairwise disjoint isolating discs makes the
displaced-root sequence injective. -/
theorem displacedRoots_injective_of_isolatingDiscs
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ) (a : Coeff p)
    (hroots : ∀ k : ℤ,
      displacedRoots a k ∈ sourceIsolatingDisc hp hp1 φ N ε k)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j)) :
    Function.Injective (displacedRoots a) := by
  intro i j hij
  by_contra hne
  have hjroot := hroots j
  rw [← hij] at hjroot
  exact Set.disjoint_left.mp (hdisjoint i j hne) (hroots i) hjroot

/-- In the isolating-disc geometry of Section 12, every retained zero
of the entire psi numerator is simple. -/
theorem deriv_sourcePsiCandidate_ne_zero_of_isolatingDiscs
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (N : ℕ) (ε : ℝ) (a : Coeff p)
    (hroots : ∀ k : ℤ,
      displacedRoots a k ∈ sourceIsolatingDisc hp hp1 φ N ε k)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (n k : ℤ) (hkn : k ≠ n) :
    deriv (fun z : ℂ => sourcePsiCandidate n (z,a))
      (displacedRoots a k) ≠ 0 := by
  have hsep := displacedRoots_injective_of_isolatingDiscs
    hp hp1 φ N ε a hroots hdisjoint
  exact deriv_sourcePsiCandidate_ne_zero_at_retained_root
    hp hp1 n k hkn a (fun j hj => hsep.ne hj.symm)

end NLS.ZakharovShabat
