import NLS.ZakharovShabat.SourcePsiRealJacobianEntry

/-!
# Off-diagonal contour bound for the psi Jacobian kernel

The Cauchy denominator contributes inverse lattice separation to an
off-diagonal Jacobian entry. This theorem isolates the quantitative
circle-integral step from the spectral estimates that supply the
weighted numerator bound and the separation constant.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A weighted numerator bound and separation of the moved root from
the selected contour give the `1 / |m-k|` off-diagonal decay. -/
theorem norm_sourcePsiRootVariation_slope_le_of_circle_bounds
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m k : ℤ) (hmk : m ≠ k)
    (a : Coeff p) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hnum : ∀ z ∈ sphere c R,
      ‖((n-m : ℤ) : ℂ) *
        sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ))‖ ≤ B)
    (hsep : ∀ z ∈ sphere c R,
      δ * ‖((m-k : ℤ) : ℂ)‖ ≤ ‖displacedRoots a k-z‖) :
    ‖((n-m : ℤ) : ℂ) *
      (∮ z in C(c,R), sourcePsiRootVariationKernel hp hp1 n k a ψ z)‖ ≤
      2*Real.pi*R*(B/(δ*‖((m-k : ℤ) : ℂ)‖)) := by
  have hmk0 : (((m-k : ℤ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hmk
  have hq : 0 < δ*‖((m-k : ℤ) : ℂ)‖ :=
    mul_pos hδ (norm_pos_iff.mpr hmk0)
  rw [← circleIntegral.integral_const_mul]
  apply circleIntegral.norm_integral_le_of_norm_le_const hR
  intro z hz
  have hrewrite :
      ((n-m : ℤ) : ℂ) * sourcePsiRootVariationKernel hp hp1 n k a ψ z =
        (((n-m : ℤ) : ℂ) *
          sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ))) /
            (displacedRoots a k-z) := by
    unfold sourcePsiRootVariationKernel
    ring
  rw [hrewrite,norm_div]
  calc
    ‖((n-m : ℤ) : ℂ) *
        sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ))‖ /
        ‖displacedRoots a k-z‖ ≤ B / ‖displacedRoots a k-z‖ :=
      div_le_div_of_nonneg_right (hnum z hz) (norm_nonneg _)
    _ ≤ B / (δ*‖((m-k : ℤ) : ℂ)‖) :=
      div_le_div_of_nonneg_left hB hq (hsep z hz)

end NLS.ZakharovShabat
