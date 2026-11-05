import NLS.KdV.HillHminusIntrinsicGapSymmetricData
import NLS.KdV.HillLocalGapUnit
import NLS.ComplexAnalysis.TwoZeroCauchyDeflation
import NLS.ComplexAnalysis.ParametricCircleTransforms

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillHminusIntrinsicGapPolynomial (k : ℕ) (p : PeriodOneHminusOne) (z : ℂ) : ℂ :=
  (z-hillHminusIntrinsicGapMidpoint q hq hr k p)^2-hillHminusIntrinsicGapSquare q hq hr k p/4

def hillHminusIntrinsicGapUnit (k : ℕ) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  parametricCircleCauchyTransform
    (fun s : ℂ × PeriodOneHminusOne => hillHminusRadicand s.2 s.1/hillHminusIntrinsicGapPolynomial q hq hr k s.2 s.1)
    (hillRealGapCenter q hq hr k : ℂ)
    (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) t

theorem hillHminusIntrinsicGapPolynomial_eq_of_pair (k : ℕ) (hk : 1 ≤ k) (p : PeriodOneHminusOne)
    (hb : ∀ z ∈ sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k), hillHminusRadicand p z ≠ 0)
    {a b : ℂ}
    (ha : a ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k))
    (hb' : b ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k))
    (hm : ∀ z ∈ closedBall (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      analyticOrderNatAt (hillHminusRadicand p) z = ({a,b} : Multiset ℂ).count z) (z : ℂ) :
    hillHminusIntrinsicGapPolynomial q hq hr k p z = (z-a)*(z-b) := by
  obtain ⟨hmid,hsq⟩ := hillHminusIntrinsicGapSymmetricData_eq_of_pair q hq hr k hk p hb ha hb' hm
  rw [hillHminusIntrinsicGapPolynomial,hmid,hsq]
  ring

theorem hillHminusIntrinsicGapUnit_eq_twoZeroQuotient (k : ℕ) (hk : 1 ≤ k) (p : PeriodOneHminusOne)
    (hb : ∀ z ∈ sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k), hillHminusRadicand p z ≠ 0)
    {a b : ℂ}
    (ha : a ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k))
    (hb' : b ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k))
    (haz : hillHminusRadicand p a = 0) (hbz : hillHminusRadicand p b = 0)
    (hm : ∀ z ∈ closedBall (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      analyticOrderNatAt (hillHminusRadicand p) z = ({a,b} : Multiset ℂ).count z)
    {z : ℂ} (hz : z ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :
    hillHminusIntrinsicGapUnit q hq hr k (z,p) = twoZeroQuotient (hillHminusRadicand p) a b z := by
  have hab (he : a = b) : deriv (hillHminusRadicand p) a = 0 := by
    apply deriv_eq_zero_of_two_zero_order (analyticOnNhd_hillHminusRadicand p a (mem_univ _)) haz
    simpa [he] using hm a (ball_subset_closedBall ha)
  have hR := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1
  have he : (fun w => hillHminusRadicand p w/hillHminusIntrinsicGapPolynomial q hq hr k p w) =
      (fun w => hillHminusRadicand p w/((w-a)*(w-b))) := by
    funext w
    rw [hillHminusIntrinsicGapPolynomial_eq_of_pair q hq hr k hk p hb ha hb' hm]
  change circleCauchyTransform (fun w => hillHminusRadicand p w/hillHminusIntrinsicGapPolynomial q hq hr k p w) _ _ z = _
  rw [he]
  exact circleCauchyTransform_div_two_zero_factor _ hR
    ((analyticOnNhd_hillHminusRadicand p).mono (subset_univ _)) ha hb' haz hbz hab hz

theorem exists_hillHminusIntrinsicGapUnit_analytic_neighborhood (k : ℕ) (hk : 1 ≤ k) :
    ∃ V : Set (PeriodOneHminusOne), IsOpen V ∧ hillOriginalHminusSource q ∈ V ∧
      AnalyticOnNhd ℂ (hillHminusIntrinsicGapUnit q hq hr k)
        (ball (hillRealGapCenter q hq hr k : ℂ)
          (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) ×ˢ V) := by
  obtain ⟨V,hV,hqV,hM,hS,_⟩ := exists_hillHminusIntrinsicGapSymmetricData_analytic_neighborhood q hq hr k hk
  obtain ⟨W,hW,hqW,hpair⟩ := exists_hillHminusIntrinsicGapPair_neighborhood q hq hr k hk
  let U := V ∩ W
  have hU : IsOpen U := hV.inter hW
  let c : ℂ := hillRealGapCenter q hq hr k
  let R := hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k
  have hR : 0 ≤ R := (add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1).le
  have hP : AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne => hillHminusIntrinsicGapPolynomial q hq hr k t.2 t.1)
      (sphere c R ×ˢ U) := by
    intro t ht
    exact ((analyticAt_fst.sub ((hM t.2 ht.2.1).comp analyticAt_snd)).pow 2).sub
      (((hS t.2 ht.2.1).comp analyticAt_snd).div_const)
  have hPn (t : ℂ × PeriodOneHminusOne) (ht : t ∈ sphere c R ×ˢ U) :
      hillHminusIntrinsicGapPolynomial q hq hr k t.2 t.1 ≠ 0 := by
    obtain ⟨hb,a,ha,b,hb',_,_,hm⟩ := hpair t.2 ht.2.2
    rw [hillHminusIntrinsicGapPolynomial_eq_of_pair q hq hr k hk t.2 hb ha hb' hm]
    exact mul_ne_zero (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem ht.1 ha))
      (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem ht.1 hb'))
  have hF : AnalyticOnNhd ℂ
      (fun t : ℂ × PeriodOneHminusOne => hillHminusRadicand t.2 t.1/hillHminusIntrinsicGapPolynomial q hq hr k t.2 t.1)
      (sphere c R ×ˢ U) := by
    intro t ht
    exact (analyticOnNhd_hillHminusRadicand_joint t (mem_univ _)).div (hP t ht) (hPn t ht)
  have ha := analyticOnNhd_parametricCircleCauchyTransform _ c R hR U hU hF
  refine ⟨U,hU,⟨hqV,hqW⟩,ha.mono ?_⟩
  intro t ht
  exact ⟨fun he => (ne_of_lt ht.1) he,ht.2⟩

theorem exists_hillHminusIntrinsicGapUnit_factorization_neighborhood (k : ℕ) (hk : 1 ≤ k) :
    ∃ V : Set (PeriodOneHminusOne), IsOpen V ∧ hillOriginalHminusSource q ∈ V ∧
      ∀ p ∈ V, ∀ z ∈ ball (hillRealGapCenter q hq hr k : ℂ)
        (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
        hillHminusRadicand p z = hillHminusIntrinsicGapPolynomial q hq hr k p z*hillHminusIntrinsicGapUnit q hq hr k (z,p) ∧
        hillHminusIntrinsicGapUnit q hq hr k (z,p) ≠ 0 := by
  obtain ⟨V,hV,hqV,hpair⟩ := exists_hillHminusIntrinsicGapPair_neighborhood q hq hr k hk
  refine ⟨V,hV,hqV,?_⟩
  intro p hp z hz
  obtain ⟨hb,a,ha,b,hb',haz,hbz,hm⟩ := hpair p hp
  have hR := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1
  have hP := hillHminusIntrinsicGapPolynomial_eq_of_pair q hq hr k hk p hb ha hb' hm
  have hunit : hillHminusIntrinsicGapUnit q hq hr k (z,p) =
      circleCauchyTransform (fun w => hillHminusRadicand p w/((w-a)*(w-b)))
        (hillRealGapCenter q hq hr k : ℂ)
        (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) z := by
    change circleCauchyTransform (fun w => hillHminusRadicand p w/hillHminusIntrinsicGapPolynomial q hq hr k p w) _ _ z = _
    congr 1
    funext w
    rw [hP]
  rw [hunit,hP]
  exact circleCauchyTransform_two_zero_unit _ hR
    ((analyticOnNhd_hillHminusRadicand p).mono (subset_univ _)) hb ha hb' haz hbz hm hz

theorem hillHminusIntrinsicGapPolynomial_original_source (k : ℕ)
    (p : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hp : SpectralWeight.one.toCoeff p ∈ Coeff.paritySubspace 0) (z : ℂ) :
    hillHminusIntrinsicGapPolynomial q hq hr k (hillOriginalHminusSource p) z =
      hillLocalGapPolynomial q hq hr k (SpectralWeight.one.toCoeff p) z := by
  rw [hillHminusIntrinsicGapPolynomial,hillLocalGapPolynomial,
    hillHminusIntrinsicGapMidpoint_original_source q hq hr k p hp,
    hillHminusIntrinsicGapSquare_original_source q hq hr k p hp]

/-- The actual jointly analytic deflated unit has the ORIGINAL unit
restriction at EVERY original even source and energy, including both roots. -/
theorem hillHminusIntrinsicGapUnit_original_source (k : ℕ)
    (p : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hp : SpectralWeight.one.toCoeff p ∈ Coeff.paritySubspace 0) (z : ℂ) :
    hillHminusIntrinsicGapUnit q hq hr k (z,hillOriginalHminusSource p) =
      hillLocalGapUnit q hq hr k (z,SpectralWeight.one.toCoeff p) := by
  simp only [hillHminusIntrinsicGapUnit,hillLocalGapUnit,parametricCircleCauchyTransform]
  simp_rw [hillHminusIntrinsicGapPolynomial_original_source q hq hr k p hp,
    hillHminusRadicand_original_source_agreement p hp]

end NLS.KdV
