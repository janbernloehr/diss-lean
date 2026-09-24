import NLS.ZakharovShabat.SourceSingleRootQuotientAsymptoticDiscSup
import NLS.ZakharovShabat.FreeSineQuotient

/-!
# The free deleted numerator is the filled sine quotient

The entire single-root product is `-2 sin z` at the free roots.
Deleting the `n`th factor gives the filled sine quotient, including
at `z = π n` where cancellation alone cannot determine the value.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The normalized numerator with the `n`th free root removed equals
the filled free sine quotient at every spectral point. -/
theorem jointDeletedSingleSpectralProduct_zero_eq_freeSineQuotient
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    (fun z : ℂ => jointDeletedSingleSpectralProduct (p := p) n (z,(0 : Coeff p))) =
      freeSineQuotient n := by
  have hc : Continuous (fun z : ℂ =>
      jointDeletedSingleSpectralProduct (p := p) n (z,(0 : Coeff p))) := by
    have hprod : Continuous (jointDeletedSingleSpectralProduct (p := p) n) :=
      continuousOn_univ.mp
        (analyticOnNhd_jointDeletedSingleSpectralProduct hp hp1 n).continuousOn
    exact hprod.comp (continuous_id.prodMk continuous_const)
  apply Continuous.ext_on ((Set.to_countable {(Real.pi : ℂ)*n}).dense_compl ℂ)
    hc (continuous_freeSineQuotient n)
  intro z hz
  have hzn : z ≠ (Real.pi : ℂ)*n := by simpa using hz
  have hroots : displacedRoots (0 : Coeff p) = (fun n : ℤ => (Real.pi : ℂ)*n) := by
    funext m
    simp [displacedRoots]
  have hfree : jointSingleSpectralProduct (z,(0 : Coeff p)) = -2*sin z := by
    change entireSingleSpectralProduct (displacedRoots (0 : Coeff p)) z = -2*sin z
    rw [hroots]
    exact entireSingleSpectralProduct_free z
  have hroot : displacedRoots (0 : Coeff p) n = (Real.pi : ℂ)*n := by
    simp [displacedRoots]
  have he := jointSingleSpectralProduct_eq_deleted hp hp1 n (z,(0 : Coeff p))
  rw [hfree, hroot] at he
  have hs := freeSineQuotient_mul_sub n z
  have hfactor : 2*((Real.pi : ℂ)*n-z) ≠ 0 :=
    mul_ne_zero (by norm_num) (sub_ne_zero.mpr (Ne.symm hzn))
  apply mul_left_cancel₀ hfactor
  calc
    2*((Real.pi : ℂ)*n-z)*jointDeletedSingleSpectralProduct n (z,(0 : Coeff p)) =
        -2*sin z := he.symm
    _ = 2*((Real.pi : ℂ)*n-z)*freeSineQuotient n z := by rw [← hs]; ring

end NLS.ZakharovShabat
