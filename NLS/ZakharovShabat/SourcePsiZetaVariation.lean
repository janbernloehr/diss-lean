import NLS.ZakharovShabat.SourcePsiDoubleOmittedProduct
import NLS.ZakharovShabat.SourcePsiGeneralVariation

/-!
# Retained-root derivatives of the literal auxiliary product

The single quotient and double-omitted zeta depend affinely on each
retained root. The derivative has the original sigma_r-lambda denominator.
Filling the unused coordinate locally includes collisions with that root.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The single quotient is affine in every retained root coordinate. -/
theorem sourceSingleRootQuotient_variation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m k : ℤ) (hkm : k ≠ m)
    (a : Coeff p) (ψ : CoeffPair p) (z t : ℂ) (hzk : z ≠ displacedRoots a k) :
    sourceSingleRootQuotientJointProduct hp hp1 m (z,(a+lp.single p k t,ψ)) =
      sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ)) +
        t*(sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ))/(displacedRoots a k-z)) := by
  have he : jointDeletedSingleSpectralProduct m (z,a+lp.single p k t) =
      jointDeletedSingleSpectralProduct m (z,a) +
        t*(jointDeletedSingleSpectralProduct m (z,a)/(displacedRoots a k-z)) := by
    have h := sourcePsiCandidate_variation hp hp1 m k hkm a z t hzk
    unfold sourcePsiCandidate at h
    linear_combination (-1/2:ℂ)*h
  unfold sourceSingleRootQuotientJointProduct
  rw [he]
  ring

/-- The literal double-omitted zeta is affine in a retained root, even at the unused root. -/
theorem sourcePsiZeta_variation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m k : ℤ)
    (hmn : m ≠ n) (hkn : k ≠ n) (hkm : k ≠ m)
    (a : Coeff p) (ψ : CoeffPair p) (z t : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hzk : z ≠ displacedRoots a k) :
    sourcePsiZeta hp hp1 n m (a+lp.single p k t) ψ z =
      sourcePsiZeta hp hp1 n m a ψ z +
        t*(sourcePsiZeta hp hp1 n m a ψ z/(displacedRoots a k-z)) := by
  let b : Coeff p := a+lp.single p n (z+1-displacedRoots a n)
  have hbn : displacedRoots b n = z+1 := by
    simp only [b,displacedRoots,lp.coeFn_add,Pi.add_apply,lp.single_apply_self]
    ring
  have hbk : displacedRoots b k = displacedRoots a k := by
    simp only [b,displacedRoots,lp.coeFn_add,Pi.add_apply,lp.single_apply_ne _ _ _ hkn,add_zero]
  have hbnt (s : ℂ) : displacedRoots (b+lp.single p k s) n = z+1 := by
    simpa only [displacedRoots,lp.coeFn_add,Pi.add_apply,
      lp.single_apply_ne _ _ _ hkn.symm,add_zero] using hbn
  have hsame (s : ℂ) :
      sourcePsiZeta hp hp1 n m (b+lp.single p k s) ψ z =
        sourcePsiZeta hp hp1 n m (a+lp.single p k s) ψ z := by
    apply sourcePsiZeta_congr
    intro j hjn _
    simp only [b,lp.coeFn_add,Pi.add_apply,lp.single_apply_ne _ _ _ hjn,add_zero]
  have hsame₀ : sourcePsiZeta hp hp1 n m b ψ z = sourcePsiZeta hp hp1 n m a ψ z := by
    simpa using hsame 0
  rw [← hsame t,← hsame₀]
  have hne₁ : z ≠ displacedRoots (b+lp.single p k t) n := by rw [hbnt t]; simp
  have hne₀ : z ≠ displacedRoots b n := by rw [hbn]; simp
  have he₁ := sourcePsiGapRegularFactor_eq_zeta (p := p) hp hp1 n m hmn
    (b+lp.single p k t) ψ z hz hne₁
  have he₀ := sourcePsiGapRegularFactor_eq_zeta (p := p) hp hp1 n m hmn b ψ z hz hne₀
  rw [← he₁,← he₀]
  unfold sourcePsiGapRegularFactor
  rw [sourceSingleRootQuotient_variation hp hp1 m k hkm b ψ z t (by rwa [hbk]),hbnt,hbn,hbk]
  ring

/-- The source derivative of the literal zeta, with its original retained-root denominator. -/
theorem hasDerivAt_sourcePsiZeta_variation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m k : ℤ)
    (hmn : m ≠ n) (hkn : k ≠ n) (hkm : k ≠ m)
    (a : Coeff p) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hzk : z ≠ displacedRoots a k) :
    HasDerivAt (fun t : ℂ => sourcePsiZeta hp hp1 n m (a+lp.single p k t) ψ z)
      (sourcePsiZeta hp hp1 n m a ψ z/(displacedRoots a k-z)) 0 := by
  have he : (fun t : ℂ => sourcePsiZeta hp hp1 n m (a+lp.single p k t) ψ z) =
      (fun t : ℂ => sourcePsiZeta hp hp1 n m a ψ z +
        t*(sourcePsiZeta hp hp1 n m a ψ z/(displacedRoots a k-z))) := by
    funext t
    exact sourcePsiZeta_variation hp hp1 n m k hmn hkn hkm a ψ z t hz hzk
  rw [he]
  simpa using (((hasDerivAt_id (0:ℂ)).mul_const
    (sourcePsiZeta hp hp1 n m a ψ z/(displacedRoots a k-z))).const_add
      (sourcePsiZeta hp hp1 n m a ψ z))

end NLS.ZakharovShabat
