import NLS.KdV.ClassicalRoughCriticalCompatibility
import NLS.ComplexAnalysis.ParametricDividedDifferenceCongruence
import NLS.KdV.HillHminusOneNormalizedMoments
import NLS.KdV.ClassicalNormalizedMoments

/-! # Exact continuous/rough agreement of normalized differentials and moments -/
noncomputable section
open Set Metric Complex NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

/- Filled centers agree as well as ordinary divided-difference values. -/
theorem hillHminusUniformNumerator_eq_classical (C : HillHminusMiuraChart) (N M : ℕ)
    (n : ℕ+) (q : Curve ℂ)
    (hcrit : hillHminusUniformCriticalPoint C N n (classicalHillHminusInclusion q) =
      classicalHillUniformCriticalPoint M n q) (lambda : ℂ) :
    hillHminusUniformNumerator C N n (lambda,classicalHillHminusInclusion q) =
      classicalHillUniformNumerator M n (lambda,q) := by
  unfold hillHminusUniformNumerator classicalHillUniformNumerator
  congr 1
  exact parametricMovingDividedDifference_congr_slice _ _ _ _ _ _ _ hcrit
    (fun w => hillHminusDiscriminantDerivative_eq_classical w q)

theorem hillHminusPeriodEntry_eq_classical (C : HillHminusMiuraChart) (N M : ℕ)
    (n k : ℕ+) (q : Curve ℂ)
    (hcrit : hillHminusUniformCriticalPoint C N n (classicalHillHminusInclusion q) =
      classicalHillUniformCriticalPoint M n q)
    (hcover : ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4), (z^2,q) ∈ classicalHillContinuationDomain) :
    hillHminusPeriodEntry C N n k (classicalHillHminusInclusion q) = classicalHillUniformHighPeriod M n k q := by
  unfold hillHminusPeriodEntry classicalHillUniformHighPeriod
  congr 1
  apply circleIntegral.integral_congr (by positivity)
  intro z hz
  dsimp only
  rw [hillHminusUniformNumerator_eq_classical C N M n q hcrit,
    hillHminusContinuedRoot_eq_classical _ q (hcover z hz)]

namespace HillHminusUniformPeriodData
variable {C : HillHminusMiuraChart} {N M : ℕ} {V : Set PeriodOneHminusOne}
variable {W : Set (Curve ℂ)} {A B : ℝ}
variable (Dr : HillHminusUniformPeriodData C N V A) (Dc : ClassicalAllContourPeriodData M W B)
include Dr Dc

/- Equality of every scalar entry of the actual extended integer matrix. -/
omit Dr in
theorem matrix_eq_classical (q : Curve ℂ) (hq : q ∈ W)
    (hcrit : ∀ n : ℕ+, hillHminusUniformCriticalPoint C N n (classicalHillHminusInclusion q) =
      classicalHillUniformCriticalPoint M n q) (m n : ℤ) :
    hillHminusPeriodMatrix C N (classicalHillHminusInclusion q) m n = classicalHillPeriodMatrix M q m n := by
  unfold hillHminusPeriodMatrix classicalHillPeriodMatrix
  split_ifs with hm hn
  · exact hillHminusPeriodEntry_eq_classical C N M _ _ q (hcrit _) (Dc.cover _ q hq)
  all_goals rfl

/- Actual Hilbert realizations agree, not only their formal coordinate sequences. -/
theorem numeratorHilbert_eq_classical (q : Curve ℂ) (hqr : classicalHillHminusInclusion q ∈ V) (hqc : q ∈ W)
    (hcrit : ∀ n : ℕ+, hillHminusUniformCriticalPoint C N n (classicalHillHminusInclusion q) =
      classicalHillUniformCriticalPoint M n q) (lambda : ℂ) :
    hillHminusNumeratorHilbert C N (lambda,classicalHillHminusInclusion q) = classicalHillNumeratorHilbert M (lambda,q) := by
  ext k
  rw [Dr.numeratorHilbert_spec.1 _ ⟨mem_univ _,hqr⟩,Dc.numeratorHilbert_spec.1 _ ⟨mem_univ _,hqc⟩]
  unfold hillHminusNumeratorCoordinates classicalHillNumeratorCoordinates
  split_ifs with hk
  · exact hillHminusUniformNumerator_eq_classical C N M _ q (hcrit _) lambda
  · rfl

/- The bounded operators are forced equal by their actual matrix entries. -/
omit Dr in
theorem operator_eq_classical (q : Curve ℂ) (hq : q ∈ W)
    (hcrit : ∀ n : ℕ+, hillHminusUniformCriticalPoint C N n (classicalHillHminusInclusion q) =
      classicalHillUniformCriticalPoint M n q)
    (Tr Tc : NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)
    (hr : ∀ m n : ℤ, (Tr (lp.single 2 n 1)) m = hillHminusPeriodMatrix C N (classicalHillHminusInclusion q) m n)
    (hc : ∀ m n : ℤ, (Tc (lp.single 2 n 1)) m = classicalHillPeriodMatrix M q m n) : Tr = Tc := by
  apply NLS.Coeff.continuousLinearMap_eq_of_single (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro n
  ext m
  rw [hr,hc,matrix_eq_classical Dc q hq hcrit]

/- Any actual left/right inverse constructions agree once their periods agree. -/
omit Dr in
theorem inverse_eq_classical (q : Curve ℂ) (hq : q ∈ W)
    (hcrit : ∀ n : ℕ+, hillHminusUniformCriticalPoint C N n (classicalHillHminusInclusion q) =
      classicalHillUniformCriticalPoint M n q)
    (Tr Rr Tc Rc : NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)
    (hr : ∀ m n : ℤ, (Tr (lp.single 2 n 1)) m = hillHminusPeriodMatrix C N (classicalHillHminusInclusion q) m n)
    (hc : ∀ m n : ℤ, (Tc (lp.single 2 n 1)) m = classicalHillPeriodMatrix M q m n)
    (hrInv : Rr.comp Tr = ContinuousLinearMap.id ℂ (NLS.Coeff 2))
    (hcInv : Tc.comp Rc = ContinuousLinearMap.id ℂ (NLS.Coeff 2)) : Rr = Rc := by
  have he := operator_eq_classical Dc q hq hcrit Tr Tc hr hc
  rw [he] at hrInv
  exact left_inv_eq_right_inv hrInv hcInv

/- Exact entire normalized numerator equality for any agreeing inverse columns. -/
theorem normalizedNumerator_eq_classical
    (Rr : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (Rc : Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : Curve ℂ) (hqr : classicalHillHminusInclusion q ∈ V) (hqc : q ∈ W)
    (hcrit : ∀ n : ℕ+, hillHminusUniformCriticalPoint C N n (classicalHillHminusInclusion q) =
      classicalHillUniformCriticalPoint M n q)
    (hR : Rr (classicalHillHminusInclusion q) = Rc q) (n : ℕ+) (lambda : ℂ) :
    hillHminusNormalizedNumerator C N Rr n (lambda,classicalHillHminusInclusion q) =
      classicalHillNormalizedNumerator M Rc n (lambda,q) := by
  unfold hillHminusNormalizedNumerator classicalHillNormalizedNumerator
  rw [hR,Dr.numeratorHilbert_eq_classical Dc q hqr hqc hcrit]

theorem normalizedMoment_eq_classical
    (Rr : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (Rc : Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : Curve ℂ) (hqr : classicalHillHminusInclusion q ∈ V) (hqc : q ∈ W)
    (hcrit : ∀ n : ℕ+, hillHminusUniformCriticalPoint C N n (classicalHillHminusInclusion q) =
      classicalHillUniformCriticalPoint M n q)
    (hR : Rr (classicalHillHminusInclusion q) = Rc q) (n k : ℕ+) (m : ℕ) :
    hillHminusNormalizedMoment C N Rr n k m (classicalHillHminusInclusion q) =
      classicalHillNormalizedMoment M Rc n k m q := by
  unfold hillHminusNormalizedMoment classicalHillNormalizedMoment
  apply circleIntegral.integral_congr (by positivity)
  intro z hz
  unfold hillHminusNormalizedMomentIntegrand classicalHillNormalizedMomentIntegrand
    hillHminusFrequencyPrimitive classicalHillFrequencyPrimitive
  dsimp only
  rw [hillHminusContinuedPrimitive_eq_classical _ q (Dc.cover k q hqc z hz),
    hillHminusContinuedRoot_eq_classical _ q (Dc.cover k q hqc z hz),
    Dr.normalizedNumerator_eq_classical Dc Rr Rc q hqr hqc hcrit hR]

end HillHminusUniformPeriodData
namespace ClassicalAllContourPeriodData
/-- Any actual continuous period inverse has a constructed rough counterpart,
with exact entire numerator and all-order moment agreement on one common
continuous neighborhood before every positive index and moment order. -/
theorem exists_rough_normalization_compatibility {M : ℕ} {W : Set (Curve ℂ)} {B : ℝ}
    (Dc : ClassicalAllContourPeriodData M W B)
    (Tc Rc : Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hentryc : ∀ q ∈ W, ∀ m n : ℤ, (Tc q (lp.single 2 n 1)) m = classicalHillPeriodMatrix M q m n)
    (hinvc : ∀ q ∈ W, (Tc q).comp (Rc q) = ContinuousLinearMap.id ℂ (NLS.Coeff 2)) :
    ∃ C : HillHminusMiuraChart, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, ∃ U : Set (Curve ℂ),
      ∃ Rr : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
        0 < N ∧ IsOpen V ∧ 0 ∈ V ∧ U ⊆ W ∧ U ⊆ classicalHillHminusInclusion ⁻¹' V ∧
        IsOpen U ∧ 0 ∈ U ∧ AnalyticOnNhd ℂ Rr V ∧
        Rr 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧ (∀ q ∈ V, ‖Rr q‖ ≤ 2) ∧
        (∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusNormalizedNumerator C N Rr n) (univ ×ˢ V)) ∧
        (∀ n : ℕ+, ∀ lambda : ℂ, hillHminusNormalizedNumerator C N Rr n (lambda,0) = classicalHillFreePsi n lambda) ∧
        (∀ n k : ℕ+, ∀ q ∈ V,
          (2*(Real.pi : ℂ))⁻¹*hillHminusNormalizedMoment C N Rr n k 0 q = if n = k then 1 else 0) ∧
        (∀ n k : ℕ+, ∀ m : ℕ, AnalyticOnNhd ℂ (hillHminusNormalizedMoment C N Rr n k m) V) ∧
        (∀ q ∈ U, Rr (classicalHillHminusInclusion q) = Rc q) ∧
        (∀ n : ℕ+, ∀ q ∈ U, ∀ lambda : ℂ,
          hillHminusNormalizedNumerator C N Rr n (lambda,classicalHillHminusInclusion q) =
            classicalHillNormalizedNumerator M Rc n (lambda,q)) ∧
        (∀ n k : ℕ+, ∀ m : ℕ, ∀ q ∈ U,
          hillHminusNormalizedMoment C N Rr n k m (classicalHillHminusInclusion q) =
            classicalHillNormalizedMoment M Rc n k m q) ∧
        ∃ A : ℝ, HillHminusUniformPeriodData C N V A := by
  obtain ⟨C,N,V,Tr,Rr,hN,hV,h0V,_,hRa,_,hR0,hinvr,hentryr,A,Dr⟩ :=
    exists_hillHminus_analytic_period_inverse
  obtain ⟨U,hUW,hULV,hU,h0U,hcrit⟩ := Dr.exists_critical_compatibility Dc
  have hR (q : Curve ℂ) (hq : q ∈ U) : Rr (classicalHillHminusInclusion q) = Rc q :=
    HillHminusUniformPeriodData.inverse_eq_classical Dc q (hUW hq) (fun n => hcrit n q hq)
      (Tr (classicalHillHminusInclusion q)) (Rr (classicalHillHminusInclusion q)) (Tc q) (Rc q)
      (hentryr _ (hULV hq)) (hentryc q (hUW hq)) (hinvr _ (hULV hq)).2.1 (hinvc q (hUW hq))
  exact ⟨C,N,V,U,Rr,hN,hV,h0V,hUW,hULV,hU,h0U,hRa,hR0,fun q hq => (hinvr q hq).2.2,
    Dr.normalizedNumerator_analytic Rr hRa,Dr.normalizedNumerator_free Rr hR0,
    fun n k q hq => Dr.normalizedMoment_zero_order Rr Tr n k q hq (hentryr q hq) (hinvr q hq).1,
    Dr.normalizedMoment_analytic Rr hRa,hR,
    fun n q hq lambda => Dr.normalizedNumerator_eq_classical Dc Rr Rc q (hULV hq) (hUW hq)
      (fun j => hcrit j q hq) (hR q hq) n lambda,
    fun n k m q hq => Dr.normalizedMoment_eq_classical Dc Rr Rc q (hULV hq) (hUW hq)
      (fun j => hcrit j q hq) (hR q hq) n k m,A,Dr⟩
end ClassicalAllContourPeriodData

end NLS.KdV
