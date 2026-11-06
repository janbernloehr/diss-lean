import NLS.KdV.HillScaledComplexGapRoot
import NLS.ComplexAnalysis.CenteredTwoRootPeriod
import NLS.KdV.HillRadiusEnergyCirclePhysicalRoot
/-! # Actual quadratic data on the radius-k energy annuli

One cutoff before all bounded complex sources gives the literal normalized
quadratic root, its norm bounds and exact negative unit reciprocal period.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillFreeGap_energy_radius_geometry (k : ℕ+) :
    (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ) = freeHillEnergy k ∧
      (k : ℝ) ≤ hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ) ∧
      hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ) < 8*(k : ℝ) := by
  have hfr : (freeHillValue (k : ℕ) : ℂ) = freeHillEnergy k := by
    dsimp only [freeHillValue,freeHillEnergy];push_cast;ring
  refine ⟨by rw [hillFreeGapCenter h0q h0r (k : ℕ) k.property,hfr],?_,?_⟩
  all_goals rw [hillFreeGapHalfLength h0q h0r (k : ℕ) k.property,zero_add,hillFreeGapCollar h0q h0r (k : ℕ) k.property]
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast k.property
    have hh := mul_nonneg (show 0 ≤ Real.pi^2-4 by nlinarith [Real.pi_gt_three])
      (show 0 ≤ 2*(k : ℝ)-1 by linarith)
    nlinarith
  · have hk : (0 : ℝ) < k := by positivity
    have hpi : Real.pi^2 < 16 := by nlinarith [Real.pi_pos,Real.pi_lt_four]
    have hh := mul_pos (sub_pos.mpr hpi) hk
    nlinarith [sq_nonneg Real.pi]

theorem exists_hillRadiusEnergyCircle_quadratic_data (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ k : ℕ+, N ≤ (k : ℕ) →
      AnalyticOnNhd ℂ (hillFreeGapQuadraticRoot h0q h0r (k : ℕ))
        ({E : ℂ | (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖} ×ˢ ball (0 : Coeff 2) B) ∧
      (∀ p ∈ ball (0 : Coeff 2) B, ∀ E : ℂ, (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖ →
        hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p)^2=hillLocalGapPolynomial 0 h0q h0r (k : ℕ) p E ∧
        hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p) ≠ 0 ∧
        ‖E-freeHillEnergy k‖/2 ≤ ‖hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p)‖ ∧
        ‖hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p)‖ ≤ 2*‖E-freeHillEnergy k‖) ∧
      ∀ p ∈ ball (0 : Coeff 2) B,
        CircleIntegrable (fun E : ℂ => (hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p))⁻¹) (freeHillEnergy k) (k : ℝ) ∧
        (∮ E in C(freeHillEnergy k,(k : ℝ)), (hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p))⁻¹) = -(2*(Real.pi : ℂ)*I) := by
  obtain ⟨Nq,hNq,hQ⟩ := exists_hillFreeGap_scaled_complex_quadratic_root_chart h0q h0r (1/16) (by norm_num) (by norm_num) B
  obtain ⟨Np,_,hpairs⟩ := exists_hillFreeGap_bounded_complex_localized_pairs h0q h0r (1/128) (by norm_num) (by norm_num) B
  refine ⟨max Nq Np,hNq.trans (le_max_left _ _),?_⟩
  intro k hk
  have hkq := (le_max_left Nq Np).trans hk
  have hkp := (le_max_right Nq Np).trans hk
  obtain ⟨hc,hRlo,hRhi⟩ := hillFreeGap_energy_radius_geometry h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ)
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r (k : ℕ) k.property).1
    (hillRealGapContour_geometry 0 h0q h0r (k : ℕ) k.property).2.1
  have hsmall (E : ℂ) (hE : (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖) :
      (1/16)*R ≤ ‖E-(hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ)‖ := by rw [hc];dsimp only [R];linarith
  have hQa : AnalyticOnNhd ℂ (hillFreeGapQuadraticRoot h0q h0r (k : ℕ))
      ({E : ℂ | (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖} ×ˢ ball (0 : Coeff 2) B) :=
    ((hQ (k : ℕ) hkq).1).mono (fun t ht => ⟨hsmall t.1 ht.1,ht.2⟩)
  have hdata (p : Coeff 2) (hp : p ∈ ball 0 B) (E : ℂ) (hE : (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖) :=
    (hQ (k : ℕ) hkq).2 p hp E (hsmall E hE)
  refine ⟨hQa,?_,?_⟩
  · intro p hp E hE
    simpa only [hc] using hdata p hp E hE
  · intro p hp
    have hA : AnalyticOnNhd ℂ (fun E : ℂ => (hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p))⁻¹)
        (sphere (freeHillEnergy k) (k : ℝ)) := by
      intro E hE
      have hd : (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖ := by rw [mem_sphere_iff_norm.mp hE];nlinarith [show (0 : ℝ) ≤ k by positivity]
      exact ((hQa (E,p) ⟨hd,hp⟩).comp (f := fun E : ℂ => (E,p))
        (analyticAt_id.prod analyticAt_const)).inv (hdata p hp E hd).2.1
    refine ⟨hA.continuousOn.circleIntegrable (by positivity),?_⟩
    have hpB : ‖p‖ ≤ B := (mem_ball_zero_iff.mp hp).le
    obtain ⟨hboundary,a,ha,b,hb,_,_,hm⟩ := hpairs p hpB (k : ℕ) hkp
    have haB : a ∈ ball (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ) R :=
      ball_subset_ball (by linarith : (1/128)*R ≤ R) ha
    have hbB : b ∈ ball (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ) R :=
      ball_subset_ball (by linarith : (1/128)*R ≤ R) hb
    have ha' : ‖a-freeHillEnergy k‖ ≤ (k : ℝ)/16 := by
      have hh := mem_ball_iff_norm.mp ha
      rw [hc] at hh
      linarith
    have hb' : ‖b-freeHillEnergy k‖ ≤ (k : ℝ)/16 := by
      have hh := mem_ball_iff_norm.mp hb
      rw [hc] at hh
      linarith
    have hpoly (E : ℂ) := hillLocalGapPolynomial_eq_of_pair 0 h0q h0r (k : ℕ) k.property p hboundary haB hbB hm E
    have heq : (fun E : ℂ => (hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p))⁻¹) =
        (fun E : ℂ => ((freeHillEnergy k-E)*sqrt (((E-a)*(E-b))/(E-freeHillEnergy k)^2))⁻¹) := by
      funext E
      rw [hillFreeGapQuadraticRoot,hpoly E,hc]
    rw [heq]
    exact circleIntegral_inv_centered_twoRoot a b (freeHillEnergy k) (k : ℝ) (by positivity) ha' hb'
end NLS.KdV
