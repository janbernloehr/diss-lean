import NLS.KdV.ClassicalHillOddDifferentialMoments
import NLS.KdV.ClassicalHillGapQuotients
import NLS.ComplexAnalysis.AnalyticDiscSquareRoot
import NLS.ComplexAnalysis.ContinuousSquareRootPath

/-! # Actual positive differential moments at collapsed high Hill gaps

The actual endpoint-deflated square has a nonzero analytic quotient.
Its disc square root extends the primitive, up to one fixed sign on the
connected contour. Filled primitive/root quotients then cancel every
positive moment of any entire numerator, including the diagonal case.
-/
noncomputable section
open Set Metric Complex NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_classicalHill_high_collapsed_differential_moments (q : Curve ℂ) :
    ∃ M : ℕ, ∃ U : Set (Curve ℂ), 0 < M ∧ IsOpen U ∧ q ∈ U ∧
      ∀ a ∈ U, ∀ k : ℕ+, M ≤ (k : ℕ) → classicalHillHighSquaredGap a k = 0 →
        ∀ P : ℂ → ℂ, AnalyticOnNhd ℂ P univ → ∀ m : ℕ,
          (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
            (classicalHillContinuedPrimitive (z^2,a)+I*(k : ℂ)*Real.pi)^(m+1)*
              (P (z^2)/classicalHillContinuedRoot (z^2,a))*(2*z)) = 0 := by
  obtain ⟨r1,N1,V1,hr1,hr1pi,hN1,hV1,hq1,hfamily1⟩ := exists_classicalHill_whole_gap_quotients q
  obtain ⟨r2,N2,V2,hr2,_,_,hV2,hq2,hfamily2⟩ := exists_classicalHill_gap_quotient_bounds q
  let r := min r1 r2
  have hr : 0 < r := lt_min hr1 hr2
  have hrpi : r ≤ Real.pi/4 := (min_le_left _ _).trans hr1pi
  have hrho : 0 < r/8 := by positivity
  have hrhopi : r/8 ≤ Real.pi/4 := by linarith
  obtain ⟨N3,V3,_,hV3,hq3,hannulus⟩ := exists_classicalHill_high_annulus_neighborhood q (r/8) hrho hrhopi
  refine ⟨max N1 (max N2 N3),V1 ∩ (V2 ∩ V3),hN1.trans_le (le_max_left _ _),
    hV1.inter (hV2.inter hV3),⟨hq1,hq2,hq3⟩,?_⟩
  intro a ha k hk hgap P hP m
  have hk1 : N1 ≤ (k : ℕ) := (le_max_left _ _).trans hk
  have hk2 : N2 ≤ (k : ℕ) := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hk3 : N3 ≤ (k : ℕ) := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  obtain ⟨K1,H1,_,hH1,_,hmatch1,_,_⟩ := hfamily1 k hk1
  obtain ⟨K2,_,_,hzero,hmatch2,hpairs⟩ := hfamily2 k hk2
  obtain ⟨l,u,hpair,_,_,hQ,hfactor,hunit,_⟩ := hpairs a ha.2.1
  have hlu : l = u := by
    rw [hpair.squaredGap_eq] at hgap
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hgap)
  subst u
  let c : ℂ := (Real.pi : ℂ)*(k : ℕ)
  let R2 : ℝ := Real.pi*(k : ℕ)*r2
  have hR2 : 0 < R2 := by dsimp only [R2];positivity
  let Q : ℂ → ℂ := twoZeroQuotient (fun z => K2 (z,a)) l l
  obtain ⟨g,hg,hgsq⟩ := exists_analytic_squareRoot_on_ball Q (c^2) R2 hR2
    (hQ.mono ball_subset_closedBall) hunit
  let J (z : ℂ) : ℂ := (z-l)*g z
  have hJ : AnalyticOnNhd ℂ J (ball (c^2) R2) := (analyticOnNhd_id.sub analyticOnNhd_const).mul hg
  have hJsq (z : ℂ) (hz : z ∈ ball (c^2) R2) : J z^2 = K2 (z,a) := by
    dsimp only [J]
    rw [mul_pow,(hgsq z hz).2,hfactor z]
    ring
  have hcover := hannulus a ha.2.2 k hk3
  rw [classicalHill_frequency_differential_radius_independence P hP k (m+1) a (r/8) hrho hrhopi hcover]
  have henergy (z : ℂ) (hz : z ∈ closedBall c (r/8)) :
      (z^2,a) ∈ classicalHillGapSquareDisc k r1 ×ˢ V1 ∧
      z^2 ∈ ball (c^2) R2 ∧ (z^2,a) ∈ classicalHillGapSquareDisc k r2 ×ˢ V2 := by
    have hkc : 0 < Real.pi*(k : ℕ) := by positivity
    have hrc : r ≤ Real.pi*(k : ℕ) := by
      have hk1 : (1 : ℝ) ≤ (k : ℕ) := by exact_mod_cast k.property
      nlinarith [Real.pi_pos]
    have hfreq : z ∈ ball (((Real.pi*(k : ℕ) : ℝ)) : ℂ) (r/4) := by
      have hh : ‖z-c‖ ≤ r/8 := by simpa only [mem_closedBall,dist_eq_norm] using hz
      have hc : ((Real.pi*(k : ℕ) : ℝ) : ℂ) = c := by simp only [c,ofReal_mul,ofReal_natCast]
      rw [hc,mem_ball,dist_eq_norm]
      linarith
    have he := square_mem_energy_ball_of_small_frequency (Real.pi*(k : ℕ)) r hkc hr hrc z hfreq
    have he1 : z^2 ∈ ball (c^2) (Real.pi*(k : ℕ)*r1) := by
      apply ball_subset_ball (mul_le_mul_of_nonneg_left (min_le_left r1 r2) hkc.le)
      simpa only [c,ofReal_mul,ofReal_natCast] using he
    have he2 : z^2 ∈ ball (c^2) R2 := by
      apply ball_subset_ball (mul_le_mul_of_nonneg_left (min_le_right r1 r2) hkc.le)
      simpa only [c,ofReal_mul,ofReal_natCast] using he
    exact ⟨⟨ball_subset_closedBall he1,ha.1⟩,he2,ball_subset_closedBall he2,ha.2.1⟩
  let F (z : ℂ) : ℂ := classicalHillContinuedPrimitive (z^2,a)+I*(k : ℂ)*Real.pi
  have hsource (z : ℂ) (hz : z ∈ sphere c (r/8)) : (z^2,a) ∈ classicalHillContinuationDomain :=
    hcover z (closedBall_subset_closedBall hrhopi (sphere_subset_closedBall hz)) (by simpa only [c] using (mem_sphere_iff_norm.mp hz).ge)
  have hF : AnalyticOnNhd ℂ F (sphere c (r/8)) := by
    intro z hz
    exact ((analyticOnNhd_classicalHillContinuedPrimitive (z^2,a) (hsource z hz)).comp
      (f := fun z : ℂ => (z^2,a)) ((analyticAt_id.pow 2).prod analyticAt_const)).add analyticAt_const
  have hJfreq : AnalyticOnNhd ℂ (fun z => J (z^2)) (closedBall c (r/8)) := by
    intro z hz
    exact (hJ (z^2) (henergy z hz).2.1).comp (f := fun z : ℂ => z^2) (analyticAt_id.pow 2)
  have hsq (z : ℂ) (hz : z ∈ sphere c (r/8)) : F z^2 = J (z^2)^2 := by
    rw [hJsq (z^2) (henergy z (sphere_subset_closedBall hz)).2.1]
    exact (hmatch2 (z^2,a) ⟨(henergy z (sphere_subset_closedBall hz)).2.2,hsource z hz⟩).symm
  have hne (z : ℂ) (hz : z ∈ sphere c (r/8)) : J (z^2) ≠ 0 := by
    intro he
    have hd := (classicalHillContinuationDomain_subset (hsource z hz)).2
    apply hd
    apply (hzero (z^2,a) (henergy z (sphere_subset_closedBall hz)).2.2).mp
    rw [← hJsq (z^2) (henergy z (sphere_subset_closedBall hz)).2.1,he]
    norm_num
  obtain ⟨s,_,hfixed⟩ := exists_fixed_sign_of_sq_eq_on_preconnected F (fun z => J (z^2))
    (sphere c (r/8)) (isPreconnected_sphere (by simp) _ _) hF.continuousOn
    (hJfreq.continuousOn.mono sphere_subset_closedBall) hsq hne
  let G (z : ℂ) : ℂ := (P (z^2)/classicalHillContinuedRoot (z^2,a))*(2*z)
  have hExt : AnalyticOnNhd ℂ (fun z => s*J (z^2)) (closedBall c (r/8)) := analyticOnNhd_const.mul hJfreq
  have hHfreq : AnalyticOnNhd ℂ (fun z => H1 (z^2,a)*P (z^2)*(2*z)) (closedBall c (r/8)) := by
    intro z hz
    have hh := (hH1 (z^2,a) (henergy z hz).1).comp (f := fun z : ℂ => (z^2,a)) ((analyticAt_id.pow 2).prod analyticAt_const)
    exact (hh.mul ((hP (z^2) (mem_univ _)).comp (f := fun z : ℂ => z^2) (analyticAt_id.pow 2))).mul (analyticAt_const.mul analyticAt_id)
  have hcircle (z : ℂ) (hz : z ∈ sphere c (r/8)) : s*J (z^2) = F z ∧ H1 (z^2,a)*P (z^2)*(2*z) = F z*G z := by
    refine ⟨(hfixed z hz).symm,?_⟩
    have hh := (hmatch1 (z^2,a) ⟨(henergy z (sphere_subset_closedBall hz)).1,hsource z hz⟩).2
    rw [hh]
    dsimp only [F,G]
    ring
  have hz := frequencyMoment_pos_eq_zero_of_continuations F G (fun z => s*J (z^2))
    (fun z => H1 (z^2,a)*P (z^2)*(2*z)) c (r/8) hrho.le hExt hHfreq hcircle m
  simpa only [frequencyMoment,F,G,mul_assoc] using! hz

end NLS.KdV
