import NLS.ZakharovShabat.SourceAngularEndpointBound
import NLS.ZakharovShabat.SourcePsiLemma12_12
import NLS.ZakharovShabat.SourcePsiContourConjugation
import NLS.ZakharovShabat.SourcePsiOmegaDomain
import NLS.ZakharovShabat.SourceNormalizedActionCollapsedReal

/-! # Reality of the actual rotated angular numerator

The normalized psi extension agrees with its real deleted roots on the
real source locus. Its entire numerator and the omitted standard-root
product are real on the real axis. The literal angular factor `2i`
therefore makes the numerator real after rotation by `-i`.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourcePsiIsolatingComplexExtension.displacedRoots_im_eq_zero_of_realType
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n k : ℤ) :
    (displacedRoots (s n ψ : Coeff p) k).im = 0 := by
  have heq := hs.real_agreement n ⟨ψ,hreal⟩
  change s n ψ = sourcePsiGapRoot hp hp1 n ⟨ψ,hreal⟩ at heq
  rw [heq]
  have hr := sourcePsiGapRoot_mem_realDeletedCoeffSubmodule hp hp1 n ⟨ψ,hreal⟩ k
  simp only [displacedRoots,Complex.add_im,Complex.mul_im,Complex.ofReal_im,
    Complex.intCast_im,mul_zero,zero_mul,zero_add]
  exact hr

theorem sourceAngularGapNumerator_rotated_im_eq_zero_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    {W : Set (CoeffPair p)} {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) (z : ℂ)
    (hz : z.im = 0) (hO : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m) :
    (-I*sourceAngularGapNumerator hp hp1 n m s ψ z).im = 0 := by
  have hnum : (sourcePsiCandidate n (z,(s n ψ : Coeff p))).im = 0 := by
    have hc := sourcePsiCandidate_conj_of_real_roots hp hp1 n (s n ψ : Coeff p)
      (hs.displacedRoots_im_eq_zero_of_realType ψ hreal n) z
    rw [Complex.conj_eq_iff_im.mpr hz] at hc
    exact Complex.conj_eq_iff_im.mp hc.symm
  have hz' : (z.re:ℂ) = z := by simpa [hz] using Complex.re_add_im z
  have hP : (sourceStandardRootOmittedProduct hp hp1 m ψ z).im = 0 := by
    rw [← hz']
    exact sourceStandardRootOmittedProduct_im_eq_zero_on_realAxis hp hp1 ψ hreal m z.re
      (hz'.symm ▸ hO)
  simp [sourceAngularGapNumerator,Complex.mul_im,Complex.mul_re,Complex.div_re,hnum,hP]

end NLS.ZakharovShabat
