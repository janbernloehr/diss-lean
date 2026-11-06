import NLS.KdV.HillAllGapSymmetricData
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

def hillLocalGapPolynomial (k : ℕ) (p : Coeff 2) (z : ℂ) : ℂ :=
  (z-hillLocalGapMidpoint q hq hr k p)^2-hillLocalGapSquare q hq hr k p/4

def hillLocalGapUnit (k : ℕ) (t : ℂ × Coeff 2) : ℂ :=
  parametricCircleCauchyTransform
    (fun s : ℂ × Coeff 2 => hillL2Radicand s.2 s.1/hillLocalGapPolynomial q hq hr k s.2 s.1)
    (hillRealGapCenter q hq hr k : ℂ)
    (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) t

theorem hillLocalGapPolynomial_eq_of_pair (k : ℕ) (hk : 1 ≤ k) (p : Coeff 2)
    (hb : ∀ z ∈ sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k), hillL2Radicand p z ≠ 0)
    {a b : ℂ}
    (ha : a ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k))
    (hb' : b ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k))
    (hm : ∀ z ∈ closedBall (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      analyticOrderNatAt (hillL2Radicand p) z = ({a,b} : Multiset ℂ).count z) (z : ℂ) :
    hillLocalGapPolynomial q hq hr k p z = (z-a)*(z-b) := by
  obtain ⟨hmid,hsq⟩ := hillLocalGapSymmetricData_eq_of_pair q hq hr k hk p hb ha hb' hm
  rw [hillLocalGapPolynomial,hmid,hsq]
  ring

theorem hillLocalGapUnit_eq_twoZeroQuotient (k : ℕ) (hk : 1 ≤ k) (p : Coeff 2)
    (hb : ∀ z ∈ sphere (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k), hillL2Radicand p z ≠ 0)
    {a b : ℂ}
    (ha : a ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k))
    (hb' : b ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k))
    (haz : hillL2Radicand p a = 0) (hbz : hillL2Radicand p b = 0)
    (hm : ∀ z ∈ closedBall (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      analyticOrderNatAt (hillL2Radicand p) z = ({a,b} : Multiset ℂ).count z)
    {z : ℂ} (hz : z ∈ ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :
    hillLocalGapUnit q hq hr k (z,p) = twoZeroQuotient (hillL2Radicand p) a b z := by
  have hab (he : a = b) : deriv (hillL2Radicand p) a = 0 := by
    apply deriv_eq_zero_of_two_zero_order (analyticOnNhd_hillL2Radicand p a (mem_univ _)) haz
    simpa [he] using hm a (ball_subset_closedBall ha)
  have hR := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1
  have he : (fun w => hillL2Radicand p w/hillLocalGapPolynomial q hq hr k p w) =
      (fun w => hillL2Radicand p w/((w-a)*(w-b))) := by
    funext w
    rw [hillLocalGapPolynomial_eq_of_pair q hq hr k hk p hb ha hb' hm]
  change circleCauchyTransform (fun w => hillL2Radicand p w/hillLocalGapPolynomial q hq hr k p w) _ _ z = _
  rw [he]
  exact circleCauchyTransform_div_two_zero_factor _ hR
    ((analyticOnNhd_hillL2Radicand p).mono (subset_univ _)) ha hb' haz hbz hab hz

theorem exists_hillLocalGapUnit_analytic_neighborhood (k : ℕ) (hk : 1 ≤ k) :
    ∃ V : Set (Coeff 2), IsOpen V ∧ SpectralWeight.one.toCoeff q ∈ V ∧
      AnalyticOnNhd ℂ (hillLocalGapUnit q hq hr k)
        (ball (hillRealGapCenter q hq hr k : ℂ)
          (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) ×ˢ V) := by
  obtain ⟨V,hV,hqV,hM,hS,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr k hk
  obtain ⟨W,hW,hqW,hpair⟩ := exists_hillComplexGapPair_neighborhood q hq hr k hk
  let U := V ∩ W
  have hU : IsOpen U := hV.inter hW
  let c : ℂ := hillRealGapCenter q hq hr k
  let R := hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k
  have hR : 0 ≤ R := (add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1).le
  have hP : AnalyticOnNhd ℂ (fun t : ℂ × Coeff 2 => hillLocalGapPolynomial q hq hr k t.2 t.1)
      (sphere c R ×ˢ U) := by
    intro t ht
    exact ((analyticAt_fst.sub ((hM t.2 ht.2.1).comp analyticAt_snd)).pow 2).sub
      (((hS t.2 ht.2.1).comp analyticAt_snd).div_const)
  have hPn (t : ℂ × Coeff 2) (ht : t ∈ sphere c R ×ˢ U) :
      hillLocalGapPolynomial q hq hr k t.2 t.1 ≠ 0 := by
    obtain ⟨hb,a,ha,b,hb',_,_,hm⟩ := hpair t.2 ht.2.2
    rw [hillLocalGapPolynomial_eq_of_pair q hq hr k hk t.2 hb ha hb' hm]
    exact mul_ne_zero (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem ht.1 ha))
      (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem ht.1 hb'))
  have hF : AnalyticOnNhd ℂ
      (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1/hillLocalGapPolynomial q hq hr k t.2 t.1)
      (sphere c R ×ˢ U) := by
    intro t ht
    exact (analyticOnNhd_hillL2Radicand_joint t (mem_univ _)).div (hP t ht) (hPn t ht)
  have ha := analyticOnNhd_parametricCircleCauchyTransform _ c R hR U hU hF
  refine ⟨U,hU,⟨hqV,hqW⟩,ha.mono ?_⟩
  intro t ht
  exact ⟨fun he => (ne_of_lt ht.1) he,ht.2⟩

theorem exists_hillLocalGapUnit_factorization_neighborhood (k : ℕ) (hk : 1 ≤ k) :
    ∃ V : Set (Coeff 2), IsOpen V ∧ SpectralWeight.one.toCoeff q ∈ V ∧
      ∀ p ∈ V, ∀ z ∈ ball (hillRealGapCenter q hq hr k : ℂ)
        (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
        hillL2Radicand p z = hillLocalGapPolynomial q hq hr k p z*hillLocalGapUnit q hq hr k (z,p) ∧
        hillLocalGapUnit q hq hr k (z,p) ≠ 0 := by
  obtain ⟨V,hV,hqV,hpair⟩ := exists_hillComplexGapPair_neighborhood q hq hr k hk
  refine ⟨V,hV,hqV,?_⟩
  intro p hp z hz
  obtain ⟨hb,a,ha,b,hb',haz,hbz,hm⟩ := hpair p hp
  have hR := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q hq hr k hk).1
    (hillRealGapContour_geometry q hq hr k hk).2.1
  have hP := hillLocalGapPolynomial_eq_of_pair q hq hr k hk p hb ha hb' hm
  have hunit : hillLocalGapUnit q hq hr k (z,p) =
      circleCauchyTransform (fun w => hillL2Radicand p w/((w-a)*(w-b)))
        (hillRealGapCenter q hq hr k : ℂ)
        (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k) z := by
    change circleCauchyTransform (fun w => hillL2Radicand p w/hillLocalGapPolynomial q hq hr k p w) _ _ z = _
    congr 1
    funext w
    rw [hP]
  rw [hunit,hP]
  exact circleCauchyTransform_two_zero_unit _ hR
    ((analyticOnNhd_hillL2Radicand p).mono (subset_univ _)) hb ha hb' haz hbz hm hz

end NLS.KdV
