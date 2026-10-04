import NLS.ZakharovShabat.SourceAbelianMomentCircle

/-! # Cancellation of the selected root in the moment integrand

One factor of the primitive cancels the selected standard root. The
remaining numerator is analytic across the gap. Even powers of the
primitive already have the canonical analytic square continuation.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The psi numerator after deleting the selected root from the canonical denominator. -/
def sourceMomentRegularNumerator (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  sourcePsiCandidate n (z,a)/(2*I*sourceStandardRootOmittedProduct hp hp1 k ψ z)

theorem sourceMomentRegularNumerator_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n k : ℤ) (a : Coeff p) (ψ : CoeffPair p)
    (hO : AnalyticOnNhd ℂ (sourceStandardRootOmittedProduct hp hp1 k ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ k)) :
    AnalyticOnNhd ℂ (sourceMomentRegularNumerator hp hp1 n k a ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ k) := by
  intro z hz
  have hnum := (analyticOnNhd_sourcePsiCandidate hp hp1 n (z,a) (mem_univ _)).comp
    (f := fun w : ℂ => (w,a)) (analyticAt_id.prod analyticAt_const)
  exact hnum.div (analyticAt_const.mul (hO z hz))
    (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z k hz))

/-- Exact factorization of the original quotient off the closed gaps. -/
theorem sourcePsiContourIntegrand_eq_regular_div_root
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n k : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) :
    sourcePsiContourIntegrandJoint hp hp1 n (z,(a,ψ)) =
      sourceMomentRegularNumerator hp hp1 n k a ψ z/sourceStandardRoot hp hp1 ψ k z := by
  unfold sourcePsiContourIntegrandJoint sourceMomentRegularNumerator
  rw [sourceCanonicalRoot_eq_omitted hp hp1 k ψ z]
  rw [div_div]
  congr 1
  ring

namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- The first moment integrand extends across the selected gap. -/
theorem momentIntegrand_one_eq_regular
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n k : ℤ)
    (a : Coeff p) (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (z : ℂ) (hz : z ∈ ball (C.discs.center k) (C.discs.outer k) \ sourcePeriodicSegment hp hp1 ψ k) :
    sourceAbelianMomentIntegrand hp hp1 W n k 1 (z,(a,ψ)) =
      sourceFullAbelianCauchyQuotient hp hp1 W k (C.discs.center k) (C.discs.outer k) (z,ψ)*
        sourceMomentRegularNumerator hp hp1 n k a ψ z := by
  have hw := sourceStandardRoot_ne_zero_off_segment hp hp1 ψ k z hz.2
  unfold sourceAbelianMomentIntegrand
  rw [pow_one,C.fullPrimitive_eq_cauchy k k ψ hψ z hz,
    sourcePsiContourIntegrand_eq_regular_div_root hp hp1 n k a ψ z]
  simp only [sub_self,mul_zero,add_zero,sourceFullAbelianCauchyPrimitive]
  field_simp

/-- Every odd moment integrand is an analytic square power times the
regular first-moment integrand. -/
theorem momentIntegrand_odd_eq_regular
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n k : ℤ) (l : ℕ)
    (a : Coeff p) (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (z : ℂ) (hz : z ∈ ball (C.discs.center k) (C.discs.outer k) \ sourcePeriodicSegment hp hp1 ψ k) :
    sourceAbelianMomentIntegrand hp hp1 W n k (2*l+1) (z,(a,ψ)) =
      (C.square k (z,ψ))^l*
        (sourceFullAbelianCauchyQuotient hp hp1 W k (C.discs.center k) (C.discs.outer k) (z,ψ)*
          sourceMomentRegularNumerator hp hp1 n k a ψ z) := by
  have he := C.momentIntegrand_one_eq_regular n k a ψ hψ z hz
  simp only [sourceAbelianMomentIntegrand,pow_one] at he
  unfold sourceAbelianMomentIntegrand
  rw [pow_succ,pow_mul,← C.square_eq_fullPrimitive_sq k ψ hψ z hz,mul_assoc,he]

/-- At a collapsed gap every positive-order integrand extends
analytically, using the linear standard root in place of the slit root. -/
theorem momentIntegrand_succ_eq_regular_of_collapsed
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n k : ℤ) (m : ℕ)
    (a : Coeff p) (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k = 0)
    (z : ℂ) (hz : z ∈ ball (C.discs.center k) (C.discs.outer k) \ sourcePeriodicSegment hp hp1 ψ k) :
    sourceAbelianMomentIntegrand hp hp1 W n k (m+1) (z,(a,ψ)) =
      ((sourceStandardRootMidpoint hp hp1 ψ k-z)*
        sourceFullAbelianCauchyQuotient hp hp1 W k (C.discs.center k) (C.discs.outer k) (z,ψ))^m*
        (sourceFullAbelianCauchyQuotient hp hp1 W k (C.discs.center k) (C.discs.outer k) (z,ψ)*
          sourceMomentRegularNumerator hp hp1 n k a ψ z) := by
  have he := C.momentIntegrand_one_eq_regular n k a ψ hψ z hz
  simp only [sourceAbelianMomentIntegrand,pow_one] at he
  simp only [sourceAbelianMomentIntegrand,pow_succ,mul_assoc]
  rw [he,C.fullPrimitive_eq_cauchy k k ψ hψ z hz]
  simp only [sub_self,mul_zero,add_zero,sourceFullAbelianCauchyPrimitive,
    sourceStandardRoot_of_zeroGap hp hp1 ψ k z hgap,sourceStandardRootMidpoint]

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
