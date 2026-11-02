import NLS.KdV.ClassicalL2PrimitiveAgreement
import NLS.KdV.ClassicalHillArnoldActionComparison
import NLS.KdV.HillL2CubicContourMoments
import NLS.ComplexAnalysis.SquaredCircleHomotopy

/-! # Agreement of the original high contours with the L2 energy circles

The frequency radius 1/(4*pi) squares to a contour homotopic to the
energy circle of radius n/2. The whole deformation lies in the checked
L2 source annulus. This identifies both literal Arnold actions and cubic
moments, retaining the exact Jacobian and shifted-primitive normalization.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem classicalL2_small_frequency_power_period_eq_energy_period
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hQ : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (n : ℕ+) (hcut : 16*‖hillContinuousCoefficients Q‖ < (n : ℕ)) (m : ℕ) :
    ((Real.pi : ℂ)⁻¹ * ∮ z in C((Real.pi : ℂ)*(n : ℕ),1/(4*Real.pi)),
      (classicalHillFrequencyPrimitive (z,hillUnitPotentialCurve Q)+I*(n : ℂ)*Real.pi)^m*(2*z)) =
      (Real.pi : ℂ)⁻¹ * ∮ z in C((freeHillValue (n : ℕ) : ℂ),(n : ℝ)/2),
        (hillL2ContinuedPrimitive (z,SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))+
          I*(n : ℂ)*Real.pi)^m := by
  let c : ℝ := Real.pi*(n : ℕ)
  let rho : ℝ := 1/(4*Real.pi)
  let q := hillContinuousCoefficients Q
  have hn : (0 : ℝ) < (n : ℕ) := by positivity
  have hc : 0 < c := by dsimp only [c]; positivity
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  have hrhoc : rho ≤ c/8 := by
    dsimp only [rho,c]
    have hn1 : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.property
    have hpi := Real.pi_gt_three
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4*Real.pi)).mpr
    nlinarith
  have hcenter : (c : ℂ)^2 = (freeHillValue (n : ℕ) : ℂ) := by
    dsimp only [c,freeHillValue]
    push_cast
    ring
  have hrad : c*rho = (n : ℝ)/4 := by
    dsimp only [c,rho]
    field_simp
  have hrad2 : 2*c*rho = (n : ℝ)/2 := by nlinarith [hrad]
  have hrad3 : 3*c*rho = 3*(n : ℝ)/4 := by nlinarith [hrad]
  have hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0 :=
    hillContinuousCoefficients_mem_even Q hQ
  have hcut' : 8*‖q‖ ≤ (n : ℕ) := by dsimp only [q]; linarith [norm_nonneg (hillContinuousCoefficients Q)]
  have hdom (z : ℂ)
      (hz : z ∈ closedBall ((c : ℂ)^2) (3*c*rho) \ closedBall ((c : ℂ)^2) (c*rho)) :
      (z,SpectralWeight.one.toCoeff q) ∈ hillL2ContinuationDomain := by
    rw [hcenter,hrad,hrad3] at hz
    apply hillL2Continuation_high_annulus q hq (n : ℕ) n.property hcut'
      ((n : ℝ)/4) (3*(n : ℝ)/4) (by dsimp only [q]; linarith) (by linarith) z
    exact ⟨hz.1,fun ht => hz.2 (ball_subset_closedBall ht)⟩
  let f : ℂ → ℂ := fun z => (hillL2ContinuedPrimitive (z,SpectralWeight.one.toCoeff q)+I*(n : ℂ)*Real.pi)^m
  have hf : AnalyticOnNhd ℂ f
      (closedBall ((c : ℂ)^2) (3*c*rho) \ closedBall ((c : ℂ)^2) (c*rho)) := by
    intro z hz
    exact (((analyticOnNhd_hillL2ContinuedPrimitive _ (hdom z hz)).comp
      (f := fun z : ℂ => (z,SpectralWeight.one.toCoeff q))
      (analyticAt_id.prod analyticAt_const)).add analyticAt_const).pow m
  have heq := circleIntegral_square_pullback_eq_energy_circle f c rho hc hrho hrhoc hf
  have hfreq : (∮ z in C((c : ℂ),rho),
      (classicalHillFrequencyPrimitive (z,hillUnitPotentialCurve Q)+I*(n : ℂ)*Real.pi)^m*(2*z)) =
      ∮ z in C((c : ℂ),rho), f (z^2)*(2*z) := by
    apply circleIntegral.integral_congr hrho.le
    intro z hz
    have hgeo := norm_sq_sub_sq_of_small_sphere c rho hc hrho hrhoc z hz
    have hd := hdom (z^2) ⟨by simpa only [mem_closedBall,dist_eq_norm] using hgeo.2,
      by simpa only [mem_closedBall,dist_eq_norm,not_le] using hgeo.1⟩
    have hclass := (hillL2ContinuationDomain_iff_classical Q (z^2)).mp hd
    have hp := hillL2ContinuedPrimitive_eq_classical Q (z^2) hclass
    dsimp only [f,classicalHillFrequencyPrimitive,q]
    rw [hp]
  have hcC : (Real.pi : ℂ)*(n : ℕ) = (c : ℂ) := by simp only [c,ofReal_mul,ofReal_natCast]
  rw [hcC]
  change (Real.pi : ℂ)⁻¹*(∮ z in C((c : ℂ),rho),
    (classicalHillFrequencyPrimitive (z,hillUnitPotentialCurve Q)+I*(n : ℂ)*Real.pi)^m*(2*z)) = _
  rw [hfreq,heq,hcenter,hrad2]

theorem hillL2HighContourMoment_zero_eq_shifted_half_radius
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ+) (hcut : 16*‖q‖ < (n : ℕ)) :
    hillL2HighContourMoment (n : ℕ) 0 (SpectralWeight.one.toCoeff q) =
      -(Real.pi : ℂ)⁻¹ * ∮ z in C((freeHillValue (n : ℕ) : ℂ),(n : ℝ)/2),
        hillL2ContinuedPrimitive (z,SpectralWeight.one.toCoeff q)+I*(n : ℂ)*Real.pi := by
  have hn : (0 : ℝ) < (n : ℕ) := by positivity
  have hcut' : 8*‖q‖ ≤ (n : ℕ) := by linarith [norm_nonneg q]
  have hhalf : 4*‖q‖ < (n : ℝ)/2 := by linarith
  rw [hillL2HighContourMoment_eq_radius q hq (n : ℕ) n.property hcut'
    ((n : ℝ)/2) hhalf (by linarith) 0]
  simp only [pow_zero,one_mul]
  let D : Set ℂ := {z | (z,SpectralWeight.one.toCoeff q) ∈ hillL2ContinuationDomain}
  have hF : AnalyticOnNhd ℂ (fun z => hillL2ContinuedPrimitive (z,SpectralWeight.one.toCoeff q)) D := by
    intro z hz
    exact (analyticOnNhd_hillL2ContinuedPrimitive _ hz).comp
      (f := fun z : ℂ => (z,SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)
  have hcircle : sphere (freeHillValue (n : ℕ) : ℂ) ((n : ℝ)/2) ⊆ D := by
    intro z hz
    exact hillL2Continuation_high_annulus q hq (n : ℕ) n.property hcut'
      ((n : ℝ)/2) ((n : ℝ)/2) hhalf (by linarith) z
      ⟨sphere_subset_closedBall hz,fun ht => sphere_disjoint_ball.le_bot ⟨hz,ht⟩⟩
  exact (primitiveAction_add_const_of_analyticOnNhd _ D hF _ _ _
    (by positivity) hcircle).symm

/-- One complex open neighborhood of a continuous potential supports
the exact high-contour identities at every period-one potential in it.
The neighborhood and cutoff precede all those potentials and indices. -/
theorem exists_classicalL2_high_contour_agreement (Q : C(AddCircle (2 : ℝ), ℂ)) :
    ∃ N : ℕ, ∃ U : Set C(AddCircle (2 : ℝ), ℂ), 0 < N ∧ IsOpen U ∧ Q ∈ U ∧
      ∀ A ∈ U, Function.Periodic (fun x : ℝ => A (x : AddCircle (2 : ℝ))) 1 →
        ∀ n : ℕ+, N ≤ (n : ℕ) →
          16*‖hillContinuousCoefficients A‖ < (n : ℕ) ∧
          classicalHillHighContourAction n (hillUnitPotentialCurve A) =
            hillL2HighContourMoment (n : ℕ) 0 (SpectralWeight.one.toCoeff (hillContinuousCoefficients A)) ∧
          classicalHillHighContourMoment n (hillUnitPotentialCurve A) =
            hillL2HighCubicContourMoment (n : ℕ) (SpectralWeight.one.toCoeff (hillContinuousCoefficients A)) := by
  let rho : ℝ := 1/(4*Real.pi)
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  have hrhopi : rho ≤ Real.pi/4 := by
    dsimp only [rho]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4*Real.pi)).mpr
    nlinarith [Real.pi_gt_three]
  obtain ⟨Nc,V,hNc,hV,hQV,_,hperiod⟩ :=
    exists_classicalHill_high_power_period_radius_independence (hillUnitPotentialCurve Q) rho hrho hrhopi
  let B : ℝ := ‖hillContinuousCoefficients Q‖+1
  obtain ⟨Nb,hNb⟩ := exists_nat_gt (16*B)
  have hcont : Continuous hillContinuousCoefficients :=
    (WeightedCoeff.weightIsometry SpectralWeight.one.toWeight 2).symm.continuous.comp
      Fourier.continuousFourierCLM.continuous
  let U := hillUnitPotentialCLM ⁻¹' V ∩ {A | ‖hillContinuousCoefficients A‖ < B}
  refine ⟨max Nc Nb,U,hNc.trans_le (le_max_left _ _),
    (hV.preimage hillUnitPotentialCLM.continuous).inter (isOpen_lt hcont.norm continuous_const),
    ⟨hQV,by change ‖hillContinuousCoefficients Q‖ < ‖hillContinuousCoefficients Q‖+1; linarith⟩,?_⟩
  intro A hAU hA n hn
  have hnc : Nc ≤ (n : ℕ) := (le_max_left Nc Nb).trans hn
  have hnb : (Nb : ℝ) ≤ (n : ℕ) := by exact_mod_cast (le_max_right Nc Nb).trans hn
  have hcut : 16*‖hillContinuousCoefficients A‖ < (n : ℕ) := by
    have hAB : ‖hillContinuousCoefficients A‖ < B := hAU.2
    linarith
  have hp (m : ℕ) := (hperiod (hillUnitPotentialCurve A) hAU.1 n hnc rho ⟨le_rfl,hrhopi⟩ m).trans
    (classicalL2_small_frequency_power_period_eq_energy_period A hA n hcut m)
  refine ⟨hcut,?_,?_⟩
  · rw [hillL2HighContourMoment_zero_eq_shifted_half_radius
      (hillContinuousCoefficients A) (hillContinuousCoefficients_mem_even A hA) n hcut]
    simpa only [classicalHillHighContourAction,pow_one,neg_mul] using congrArg Neg.neg (hp 1)
  · rw [hillL2HighCubicContourMoment_eq_radius (hillContinuousCoefficients A)
      (hillContinuousCoefficients_mem_even A hA) (n : ℕ) n.property
      (by linarith [norm_nonneg (hillContinuousCoefficients A)]) ((n : ℝ)/2)
      (by linarith) (by
        have hnpos : (0 : ℝ) < (n : ℕ) := by positivity
        linarith)]
    exact hp 3

/-- The quadratic estimate is now for the actual L2 energy-circle
periods. Its uniform neighborhood is still in the continuous-potential
norm; this statement does not promote the estimates to the L2 topology. -/
theorem exists_classicalL2_high_moment_action_bounds (Q : C(AddCircle (2 : ℝ), ℂ)) :
    ∃ C : ℝ, ∃ N : ℕ, ∃ U : Set C(AddCircle (2 : ℝ), ℂ),
      0 < C ∧ 0 < N ∧ IsOpen U ∧ Q ∈ U ∧
      ∀ A ∈ U, Function.Periodic (fun x : ℝ => A (x : AddCircle (2 : ℝ))) 1 →
        ∀ n : ℕ+, N ≤ (n : ℕ) →
          AnalyticAt ℂ (hillL2HighContourMoment (n : ℕ) 0)
            (SpectralWeight.one.toCoeff (hillContinuousCoefficients A)) ∧
          AnalyticAt ℂ (hillL2HighCubicContourMoment (n : ℕ))
            (SpectralWeight.one.toCoeff (hillContinuousCoefficients A)) ∧
          (∃ l u : ℂ, ClassicalHillHighGapPair (hillUnitPotentialCurve A) n l u ∧
            ‖l-u‖^2/(n : ℕ) ≤
              16*Real.pi*‖hillL2HighContourMoment (n : ℕ) 0
                (SpectralWeight.one.toCoeff (hillContinuousCoefficients A))‖ ∧
            (hillL2HighContourMoment (n : ℕ) 0
              (SpectralWeight.one.toCoeff (hillContinuousCoefficients A)) = 0 ↔ l = u)) ∧
          ‖((8*(n : ℕ)*Real.pi : ℝ) : ℂ)*hillL2HighCubicContourMoment (n : ℕ)
              (SpectralWeight.one.toCoeff (hillContinuousCoefficients A))‖ ≤
            C*‖hillL2HighContourMoment (n : ℕ) 0
              (SpectralWeight.one.toCoeff (hillContinuousCoefficients A))‖^2 := by
  obtain ⟨Ne,Ue,hNe,hUe,hQe,heq⟩ := exists_classicalL2_high_contour_agreement Q
  obtain ⟨C,Nm,Vm,hC,_,hVm,hQm,hm⟩ :=
    exists_analytic_classicalHill_moments_with_action_bounds (hillUnitPotentialCurve Q)
  obtain ⟨Ng,Vg,_,hVg,hQg,hg⟩ :=
    exists_classicalHill_high_action_gap_comparison_and_zero_locus (hillUnitPotentialCurve Q)
  let N := max Ne (max Nm Ng)
  let U := Ue ∩ hillUnitPotentialCLM ⁻¹' (Vm ∩ Vg)
  refine ⟨C,N,U,hC,hNe.trans_le (le_max_left _ _),
    hUe.inter ((hVm.inter hVg).preimage hillUnitPotentialCLM.continuous),⟨hQe,hQm,hQg⟩,?_⟩
  intro A hAU hA n hn
  have hne : Ne ≤ (n : ℕ) := (le_max_left Ne _).trans hn
  have hnm : Nm ≤ (n : ℕ) := (le_max_left Nm Ng).trans ((le_max_right Ne _).trans hn)
  have hng : Ng ≤ (n : ℕ) := (le_max_right Nm Ng).trans ((le_max_right Ne _).trans hn)
  obtain ⟨hcut,hI,hR⟩ := heq A hAU.1 hA n hne
  have hcut' : 8*‖hillContinuousCoefficients A‖ ≤ (n : ℕ) := by
    linarith [norm_nonneg (hillContinuousCoefficients A)]
  refine ⟨analyticAt_hillL2HighContourMoment (hillContinuousCoefficients A)
      (hillContinuousCoefficients_mem_even A hA) (n : ℕ) n.property hcut' 0,
    analyticAt_hillL2HighCubicContourMoment (hillContinuousCoefficients A)
      (hillContinuousCoefficients_mem_even A hA) (n : ℕ) n.property hcut',?_,?_⟩
  · obtain ⟨l,u,hpair,hbound,hzero⟩ := hg n hng (hillUnitPotentialCurve A) hAU.2.2
    rw [hI] at hbound hzero
    exact ⟨l,u,hpair,hbound,hzero⟩
  · have hb := (hm n hnm).2.2 (hillUnitPotentialCurve A) hAU.2.1
    rwa [hI,hR] at hb

end NLS.KdV
