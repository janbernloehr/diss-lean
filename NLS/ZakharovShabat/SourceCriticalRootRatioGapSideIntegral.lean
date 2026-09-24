import NLS.ZakharovShabat.SourceCriticalRootRatioGapSides
import NLS.ZakharovShabat.RealGapCanonicalRootAffineIntegral
import NLS.ZakharovShabat.SourceStandardRootGapSideImproper

/-!
# Vanishing straight gap-side integrals for the critical-root quotient

For real-type source potentials, the pulled-back upper and lower
boundary quotient integrals are the actual straight side-path integrals
of the selected critical factor and analytic deleted quotient.
-/

noncomputable section
open Set Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The complex half-gap is the real affine Jacobian for a real-type
source potential. -/
theorem sourceStandardRootHalfGap_eq_ofReal_affineJacobian
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    sourceStandardRootHalfGap hp hp1 ψ n =
      (((canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re -
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re)/2 : ℝ) := by
  let φ := periodOnePotential ψ
  let l := canonicalPeriodicLeft hp hp1 φ (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 φ (periodOnePotential_mem ψ) n
  have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType
    hp hp1 φ (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have hl : (l.re:ℂ) = l := by
    apply Complex.ext
    · simp
    · change 0 = l.im
      exact him.1.symm
  have hr : (r.re:ℂ) = r := by
    apply Complex.ext
    · simp
    · change 0 = r.im
      exact him.2.symm
  change (r-l)/2 = (((r.re-l.re)/2:ℝ):ℂ)
  rw [← hl, ← hr]
  simp only [Complex.ofReal_re]
  push_cast
  ring

/-- Inversion of the affine coordinate on an open real gap. -/
theorem realGapInverseCoordinate_affine
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (t : ℝ) :
    realGapInverseCoordinate hp hp1 ψ n
      (realGapAffinePoint hp hp1 ψ n t) = t := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  have hne : b-a ≠ 0 := by
    change a < b at hopen
    linarith
  change (2*((a+b)/2+(b-a)/2*t)-a-b)/(b-a) = t
  field_simp
  ring

/-- The selected regular numerator in the critical-root gap factorization. -/
def sourceCriticalRootGapNumerator (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (z : ℂ) : ℂ :=
  (canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n-z) *
    sourceCriticalRootRatioExtension hp hp1 n ψ z

/-- Both straight side-path integrals of the critical-root quotient
vanish on an open real-type canonical gap. -/
theorem sourceCriticalRoot_gapSidePathIntegral_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (upper : Bool) :
    gapSidePathIntegral
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n)
      (sourceCriticalRootGapNumerator hp hp1 ψ n)
      (-1) 1 upper = 0 := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let d : ℝ := (b-a)/2
  let F := sourceCriticalRootGapNumerator hp hp1 ψ n
  let D (z : ℂ) := deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z
  let U := realGapCanonicalRootUpperValue hp hp1 ψ n
  let L := realGapCanonicalRootLowerValue hp hp1 ψ n
  have hδ : δ = (d:ℂ) :=
    sourceStandardRootHalfGap_eq_ofReal_affineJacobian hp hp1 ψ hreal n
  have hd : d ≠ 0 := by
    change a < b at hopen
    dsimp [d]
    linarith
  have hδne : δ ≠ 0 := by
    rw [hδ]
    exact_mod_cast hd
  have hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ≠ 0 := by
    intro h
    have hzero : δ = 0 := by
      change canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n / 2 = 0
      rw [h]
      simp
    exact hδne hzero
  obtain ⟨W,_,_,hWreal,hWdom⟩ :=
    exists_global_source_gapPoint_mem_omittedDomain hp hp1
  have hψ : ψ ∈ W := hWreal hreal
  have hpoint (t : ℝ) (ht : t ∈ Ioo (-1) 1) :
      τ+δ*(t:ℂ) = (realGapAffinePoint hp hp1 ψ n t:ℂ) :=
    sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint
      hp hp1 ψ hreal n t
  have hinv (t : ℝ) :
      realGapInverseCoordinate hp hp1 ψ n
        (realGapAffinePoint hp hp1 ψ n t) = t :=
    realGapInverseCoordinate_affine hp hp1 ψ n hopen t
  have hkernel (t : ℝ) (ht : t ∈ Ioo (-1) 1) :
      F (τ+δ*(t:ℂ)) *
        (δ / ((if upper then -δ*I else δ*I) *
          (Real.sqrt (1-t^2):ℂ))) =
      d • (D (realGapAffinePoint hp hp1 ψ n t:ℂ) /
        (if upper then U (realGapAffinePoint hp hp1 ψ n t)
          else L (realGapAffinePoint hp hp1 ψ n t))) := by
    have hdom := hWdom ψ hψ n t ht.1.le ht.2.le
    have hz := hpoint t ht
    have hi := hinv t
    cases upper with
    | true =>
        simp only [ite_true]
        have hfactor :=
          discriminant_derivative_div_canonicalRootGapUpperValue_eq_selectedFactor
            hp hp1 ψ n t hgap ht hdom
        change D (τ+δ*(t:ℂ)) /
            sourceCanonicalRootGapUpperValue hp hp1 ψ n t =
          F (τ+δ*(t:ℂ)) /
            (-δ*I*(Real.sqrt (1-t^2):ℂ)) at hfactor
        change F (τ+δ*(t:ℂ)) *
            (δ / (-δ*I*(Real.sqrt (1-t^2):ℂ))) =
          d • (D (realGapAffinePoint hp hp1 ψ n t:ℂ) /
            U (realGapAffinePoint hp hp1 ψ n t))
        rw [← hz]
        change F (τ+δ*(t:ℂ)) *
            (δ / (-δ*I*(Real.sqrt (1-t^2):ℂ))) =
          d • (D (τ+δ*(t:ℂ)) /
            sourceCanonicalRootGapUpperValue hp hp1 ψ n
              (realGapInverseCoordinate hp hp1 ψ n
                (realGapAffinePoint hp hp1 ψ n t)))
        rw [hi, hfactor, hδ]
        change F (τ+((d:ℂ))*(t:ℂ)) *
            ((d:ℂ) / (-((d:ℂ))*I*(Real.sqrt (1-t^2):ℂ))) =
          (d:ℂ) * (F (τ+((d:ℂ))*(t:ℂ)) /
            (-((d:ℂ))*I*(Real.sqrt (1-t^2):ℂ)))
        ring
    | false =>
        simp only [Bool.false_eq_true, ite_false]
        have hfactor :=
          discriminant_derivative_div_canonicalRootGapLowerValue_eq_selectedFactor
            hp hp1 ψ n t hgap ht hdom
        change D (τ+δ*(t:ℂ)) /
            sourceCanonicalRootGapLowerValue hp hp1 ψ n t =
          F (τ+δ*(t:ℂ)) /
            (δ*I*(Real.sqrt (1-t^2):ℂ)) at hfactor
        change F (τ+δ*(t:ℂ)) *
            (δ / (δ*I*(Real.sqrt (1-t^2):ℂ))) =
          d • (D (realGapAffinePoint hp hp1 ψ n t:ℂ) /
            L (realGapAffinePoint hp hp1 ψ n t))
        rw [← hz]
        change F (τ+δ*(t:ℂ)) *
            (δ / (δ*I*(Real.sqrt (1-t^2):ℂ))) =
          d • (D (τ+δ*(t:ℂ)) /
            sourceCanonicalRootGapLowerValue hp hp1 ψ n
              (realGapInverseCoordinate hp hp1 ψ n
                (realGapAffinePoint hp hp1 ψ n t)))
        rw [hi, hfactor, hδ]
        change F (τ+((d:ℂ))*(t:ℂ)) *
            ((d:ℂ) / (((d:ℂ))*I*(Real.sqrt (1-t^2):ℂ))) =
          (d:ℂ) * (F (τ+((d:ℂ))*(t:ℂ)) /
            (((d:ℂ))*I*(Real.sqrt (1-t^2):ℂ)))
        ring
  change (∫ t in (-1:ℝ)..1,
    F (τ+δ*(t:ℂ)) *
      (δ / ((if upper then -δ*I else δ*I) *
        (Real.sqrt (1-t^2):ℂ)))) = 0
  calc
    _ = ∫ t in (-1:ℝ)..1,
        d • (D (realGapAffinePoint hp hp1 ψ n t:ℂ) /
          (if upper then U (realGapAffinePoint hp hp1 ψ n t)
            else L (realGapAffinePoint hp hp1 ψ n t))) := by
          apply intervalIntegral.integral_congr_uIoo
          intro t ht
          rw [uIoo_of_le (by norm_num : (-1:ℝ) ≤ 1)] at ht
          exact hkernel t ht
    _ = 0 := by
      cases upper with
      | true =>
          simpa only [ite_true, d, D, U] using
            integral_realGapCanonicalRootUpperValue_affine_eq_zero
              hp hp1 ψ hreal n hopen
      | false =>
          simpa only [Bool.false_eq_true, ite_false, d, D, L] using
            integral_realGapCanonicalRootLowerValue_affine_eq_zero
              hp hp1 ψ hreal n hopen

end NLS.ZakharovShabat
