import NLS.ZakharovShabat.SourcePsiCoordinateVariation
import NLS.ZakharovShabat.SourcePsiContourConjugation

/-!
# Reality of the nonfree psi Jacobian kernel

On a real-centered contour, the Cauchy kernel for variation of a real
retained root has the same anti-conjugation symmetry as the psi
integrand. Its contour integral, and hence the corresponding scalar
Jacobian entry, is real.
-/

noncomputable section
open Set Metric Complex ComplexConjugate
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Reflection of the retained-root variation kernel on the canonical
root domain. -/
theorem sourcePsiRootVariationKernel_conj_of_real_data
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n k : ℤ) (a : Coeff p)
    (hroots : ∀ j : ℤ, (displacedRoots a j).im = 0)
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourcePsiRootVariationKernel hp hp1 n k a ψ (conj z) =
      -conj (sourcePsiRootVariationKernel hp hp1 n k a ψ z) := by
  have hroot : conj (displacedRoots a k) = displacedRoots a k :=
    Complex.conj_eq_iff_im.mpr (hroots k)
  unfold sourcePsiRootVariationKernel
  rw [sourcePsiContourIntegrandJoint_conj_of_real_data
    hp hp1 ψ hreal n a hroots z hz]
  rw [map_div₀, map_sub, hroot]
  ring

/-- The integral of the retained-root variation kernel is real on a
real-centered canonical-root contour. -/
theorem sourcePsiRootVariationKernel_circleIntegral_im_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n k : ℤ) (a : Coeff p)
    (hroots : ∀ j : ℤ, (displacedRoots a j).im = 0)
    (x R : ℝ) (hR : 0 < R)
    (hcircle : sphere (x:ℂ) R ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    (∮ z in C((x:ℂ),R), sourcePsiRootVariationKernel hp hp1 n k a ψ z).im = 0 := by
  exact NLS.ComplexAnalysis.circleIntegral_im_eq_zero_of_anti_conj
    (sourcePsiRootVariationKernel hp hp1 n k a ψ) x R hR
      (by
        intro z hz
        exact sourcePsiRootVariationKernel_conj_of_real_data
          hp hp1 ψ hreal n k a hroots z (hcircle hz))

/-- The explicit nonfree Jacobian entry from the root-variation formula
is real whenever the source and all displaced roots are real. -/
theorem sourcePsiRootVariation_slope_im_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m k : ℤ) (a : Coeff p)
    (hroots : ∀ j : ℤ, (displacedRoots a j).im = 0)
    (x R : ℝ) (hR : 0 < R)
    (hcircle : sphere (x:ℂ) R ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    ((((n-m : ℤ) : ℂ) *
      (∮ z in C((x:ℂ),R), sourcePsiRootVariationKernel hp hp1 n k a ψ z))).im = 0 := by
  have hJ := sourcePsiRootVariationKernel_circleIntegral_im_eq_zero
    hp hp1 ψ hreal n k a hroots x R hR hcircle
  simp [Complex.mul_im, hJ]

/-- The deleted-coordinate scalar derivative is the real-valued
Jacobian entry given by the weighted kernel integral. -/
theorem hasDerivAt_sourcePsiDeletedEquationCoordinate_real_rootVariation
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m k : ℤ) (hkn : k ≠ n)
    (a : DeletedCoeff p n) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ))
    (hroots : ∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0)
    (x R : ℝ) (hR : 0 < R)
    (hcircle : sphere (x:ℂ) R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoid : ∀ z ∈ sphere (x:ℂ) R,
      z ≠ displacedRoots (a : Coeff p) k) :
    HasDerivAt
      (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
        (a+Coeff.deletedSingleCLM n k hkn t) ψ (x:ℂ) R)
      (((n-m : ℤ) : ℂ) *
        (∮ z in C((x:ℂ),R), sourcePsiRootVariationKernel hp hp1 n k
          (a : Coeff p) ψ z)) 0 ∧
    ((((n-m : ℤ) : ℂ) *
      (∮ z in C((x:ℂ),R), sourcePsiRootVariationKernel hp hp1 n k
        (a : Coeff p) ψ z))).im = 0 := by
  exact ⟨hasDerivAt_sourcePsiDeletedEquationCoordinate_rootVariation
      hp hp1 n m k hkn a ψ hreal (x:ℂ) R hR.le hcircle havoid,
    sourcePsiRootVariation_slope_im_eq_zero
      hp hp1 ψ hreal n m k (a : Coeff p) hroots x R hR hcircle⟩

end NLS.ZakharovShabat
