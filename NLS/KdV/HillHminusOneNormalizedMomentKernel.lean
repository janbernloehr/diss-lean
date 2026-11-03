import NLS.KdV.HillHminusOneMomentKernel
import NLS.KdV.HillHminusOneTwoWeightedNormalizedMoments

/-! # Actual normalized rough moments as Hilbert kernel pairings

Coordinate functionals commute with genuine Bochner integrals. Equality of
the resulting l2 vectors and continuous bilinear duality give an absolutely
convergent coefficient expansion, without a formal sum/integral exchange.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

def hillHminusNumeratorMomentVector (C : HillHminusMiuraChart) (N : ℕ) (k : ℕ+) (m : ℕ)
    (q : PeriodOneHminusOne) : NLS.Coeff 2 :=
  ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
    ((hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^m*
      ((2*z)/hillHminusContinuedRoot (z^2,q))) • hillHminusNumeratorHilbert C N (z^2,q)

namespace HillHminusUniformPeriodData
variable {C : HillHminusMiuraChart} {N : ℕ} {V : Set PeriodOneHminusOne} {A : ℝ}
variable (D : HillHminusUniformPeriodData C N V A)
include D

theorem numeratorMoment_contour_integrable (k : ℕ+) (m : ℕ)
    (q : PeriodOneHminusOne) (hq : q ∈ V) :
    CircleIntegrable (fun z : ℂ =>
      ((hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^m*
        ((2*z)/hillHminusContinuedRoot (z^2,q))) • hillHminusNumeratorHilbert C N (z^2,q))
      ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) := by
  have hB : AnalyticOnNhd ℂ (fun z : ℂ => hillHminusNumeratorHilbert C N (z^2,q))
      (sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) := by
    intro z _
    exact (D.numeratorHilbert_spec.2 (z^2,q) ⟨mem_univ _,hq⟩).comp
      (f := fun w : ℂ => (w^2,q)) ((analyticAt_id.pow 2).prod analyticAt_const)
  have hF : AnalyticOnNhd ℂ (fun z => hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)
      (sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) := by
    intro z hz
    exact ((analyticOnNhd_hillHminusContinuedPrimitive (z^2,q) (D.cover k q hq z hz)).comp
      (f := fun w : ℂ => (w^2,q)) ((analyticAt_id.pow 2).prod analyticAt_const)).add analyticAt_const
  have hRoot : AnalyticOnNhd ℂ (fun z => hillHminusContinuedRoot (z^2,q))
      (sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) := by
    intro z hz
    exact (analyticOnNhd_hillHminusContinuedRoot (z^2,q) (D.cover k q hq z hz)).comp
      (f := fun w : ℂ => (w^2,q)) ((analyticAt_id.pow 2).prod analyticAt_const)
  exact (((hF.pow m).mul ((analyticOnNhd_const.mul analyticOnNhd_id).div hRoot
    (fun z hz => hillHminusSourceFamily.root_ne_zero (z^2,q) (D.cover k q hq z hz)))).smul hB).continuousOn.circleIntegrable (by positivity)

theorem numeratorMomentVector_eq_kernel (k : ℕ+) (m : ℕ)
    (q : PeriodOneHminusOne) (hq : q ∈ V) :
    hillHminusNumeratorMomentVector C N k m q =
      ((2*(Real.pi : ℂ))/(m+1)) • hillHminusMomentKernelVector C N k m q := by
  apply lp.ext
  funext j
  change (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j) (hillHminusNumeratorMomentVector C N k m q) = _
  unfold hillHminusNumeratorMomentVector
  rw [map_circleIntegral _ (D.numeratorMoment_contour_integrable k m q hq)]
  change (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4), _) =
    ((2*(Real.pi : ℂ))/(m+1))*hillHminusMomentKernelVector C N k m q j
  by_cases hj : 0 < j
  · let i := positiveIntegerIndex j hj
    have hi : (i : ℤ) = j := positiveIntegerIndex_int j hj
    have he : (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
        (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j)
          (((hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^m*
            ((2*z)/hillHminusContinuedRoot (z^2,q))) • hillHminusNumeratorHilbert C N (z^2,q))) =
        ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
          (hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^m*
            (hillHminusUniformNumerator C N i (z^2,q)/hillHminusContinuedRoot (z^2,q))*(2*z) := by
      apply circleIntegral.integral_congr (by positivity)
      intro z _
      simp only [map_smul,smul_eq_mul]
      change _*hillHminusNumeratorHilbert C N (z^2,q) j = _
      rw [D.numeratorHilbert_spec.1 (z^2,q) ⟨mem_univ _,hq⟩ j,
        hillHminusNumeratorCoordinates,dif_pos hj]
      change _*hillHminusUniformNumerator C N i (z^2,q) = _
      ring
    rw [he,D.numerator_power_period_eq_kernel i k m q hq,hi]
  · rw [D.momentKernelVector_nonpositive k m q hq j (not_lt.mp hj),mul_zero]
    have he : (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
        (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j)
          (((hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^m*
            ((2*z)/hillHminusContinuedRoot (z^2,q))) • hillHminusNumeratorHilbert C N (z^2,q))) =
        (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4), (0 : ℂ)) := by
      apply circleIntegral.integral_congr (by positivity)
      intro z _
      simp only [map_smul,smul_eq_mul]
      change _*hillHminusNumeratorHilbert C N (z^2,q) j = 0
      rw [D.numeratorHilbert_spec.1 (z^2,q) ⟨mem_univ _,hq⟩ j,
        hillHminusNumeratorCoordinates,dif_neg hj,mul_zero]
    rw [he]
    simp only [circleIntegral,smul_zero,intervalIntegral.integral_zero]

theorem normalizedMoment_eq_kernel_vector
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n k : ℕ+) (m : ℕ) (q : PeriodOneHminusOne) (hq : q ∈ V) :
    hillHminusNormalizedMoment C N R n k m q = (2*(Real.pi : ℂ))/(m+1)*
      NLS.Coeff.dualPairing (R q (lp.single 2 (n : ℤ) 1)) (hillHminusMomentKernelVector C N k m q) := by
  let L : NLS.Coeff 2 →L[ℂ] ℂ := NLS.Coeff.dualPairing (R q (lp.single 2 (n : ℤ) 1))
  have he : hillHminusNormalizedMoment C N R n k m q =
      L (hillHminusNumeratorMomentVector C N k m q) := by
    unfold hillHminusNumeratorMomentVector
    rw [map_circleIntegral L (D.numeratorMoment_contour_integrable k m q hq)]
    apply circleIntegral.integral_congr (by positivity)
    intro z _
    simp only [map_smul,smul_eq_mul]
    change _*(L (hillHminusNumeratorHilbert C N (z^2,q))/hillHminusContinuedRoot (z^2,q))*(2*z) = _
    dsimp only [hillHminusFrequencyPrimitive]
    ring
  rw [he,D.numeratorMomentVector_eq_kernel k m q hq,map_smul,smul_eq_mul]

theorem momentKernelVector_positive_series (k : ℕ+) (m : ℕ)
    (q : PeriodOneHminusOne) (hq : q ∈ V) (c : NLS.Coeff 2) :
    Summable (fun j : ℕ+ => ‖(j : ℂ)*c (j : ℤ)*
      ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
        (hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)/
          (z^2-hillHminusUniformCriticalPoint C N j q)^2‖) ∧
    NLS.Coeff.dualPairing c (hillHminusMomentKernelVector C N k m q) =
      ∑' j : ℕ+, (j : ℂ)*c (j : ℤ)*
        ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
          (hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)/
            (z^2-hillHminusUniformCriticalPoint C N j q)^2 := by
  have hi : Function.Injective (fun j : ℕ+ => (j : ℤ)) := by
    intro i j hij
    apply Subtype.ext
    exact Int.ofNat_inj.mp hij
  have he (j : ℕ+) : c (j : ℤ)*hillHminusMomentKernelVector C N k m q (j : ℤ) =
      (j : ℂ)*c (j : ℤ)*(∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
        (hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)/
          (z^2-hillHminusUniformCriticalPoint C N j q)^2) := by
    rw [D.momentKernelVector_positive k j m q hq]
    ring
  constructor
  · simpa only [Function.comp_def,he] using!
      (NLS.Coeff.summable_norm_dualPairing c (hillHminusMomentKernelVector C N k m q)).comp_injective hi
  rw [NLS.Coeff.dualPairing_apply,tsum_eq_positive_of_nonpositive_zero _
    (fun j hj => by rw [D.momentKernelVector_nonpositive k m q hq j hj,mul_zero])]
  exact tsum_congr he

theorem normalizedMoment_kernel_series
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n k : ℕ+) (m : ℕ) (q : PeriodOneHminusOne) (hq : q ∈ V) :
    Summable (fun j : ℕ+ => ‖(j : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (j : ℤ)*
      ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
        (hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)/
          (z^2-hillHminusUniformCriticalPoint C N j q)^2‖) ∧
    hillHminusNormalizedMoment C N R n k m q = (2*(Real.pi : ℂ))/(m+1)*
      ∑' j : ℕ+, (j : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (j : ℤ)*
        ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
          (hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)/
            (z^2-hillHminusUniformCriticalPoint C N j q)^2 := by
  obtain ⟨hs,he⟩ := D.momentKernelVector_positive_series k m q hq (R q (lp.single 2 (n : ℤ) 1))
  exact ⟨hs,(D.normalizedMoment_eq_kernel_vector R n k m q hq).trans (congrArg _ he)⟩

end HillHminusUniformPeriodData

/-- The kernel identity and every positive coefficient series hold for the
same constructed weighted family, with all its earlier analytic, inverse,
free, exact-period and odd-cancellation data retained. -/
theorem exists_hillHminus_weighted_moment_kernel_family :
    ∃ C : HillHminusMiuraChart, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      ∃ T R S Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
        0 < N ∧ IsOpen V ∧ 0 ∈ V ∧
        HillHminusTwoWeightedNormalizedMomentData C N V T R S Q ∧
        (∀ q ∈ V, ∀ n k : ℕ+, ∀ m : ℕ,
          hillHminusNormalizedMoment C N R n k m q = (2*(Real.pi : ℂ))/(m+1)*
            NLS.Coeff.dualPairing (R q (lp.single 2 (n : ℤ) 1))
              (hillHminusMomentKernelVector C N k m q)) ∧
        ∀ q ∈ V, ∀ n k : ℕ+, ∀ m : ℕ,
          Summable (fun j : ℕ+ => ‖(j : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (j : ℤ)*
            ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
              (hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)/
                (z^2-hillHminusUniformCriticalPoint C N j q)^2‖) ∧
          hillHminusNormalizedMoment C N R n k m q = (2*(Real.pi : ℂ))/(m+1)*
            ∑' j : ℕ+, (j : ℂ)*(R q (lp.single 2 (n : ℤ) 1)) (j : ℤ)*
              ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
                (hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)/
                  (z^2-hillHminusUniformCriticalPoint C N j q)^2 := by
  obtain ⟨C,N,V,T,R,S,Q,hN,hV,h0V,D⟩ := exists_hillHminus_twoWeighted_normalized_moments
  obtain ⟨A,Dr⟩ := D.source_data
  exact ⟨C,N,V,T,R,S,Q,hN,hV,h0V,D,
    fun q hq n k m => Dr.normalizedMoment_eq_kernel_vector R n k m q hq,
    fun q hq n k m => Dr.normalizedMoment_kernel_series R n k m q hq⟩

end NLS.KdV
