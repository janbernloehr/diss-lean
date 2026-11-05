import NLS.KdV.HillLocalQuadraticRoot
import NLS.ComplexAnalysis.FiniteHeadUniformTail
import NLS.KdV.HillRadiusQuadraticData
import NLS.ComplexAnalysis.CenteredTwoRootPeriod
import NLS.KdV.HillRadiusEnergyCirclePhysicalRoot
/-! # Actual quadratic data on the radius-k energy annuli

Every fixed positive gap has a complex source ball with the literal root
chart, its norm bounds and exact negative unit reciprocal period. A finite
head and the existing uniform tail give one ball for all positive gaps.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillRadiusEnergyCircle_local_quadratic_data (k : ℕ+) :
    ∃ η : ℝ, 0 < η ∧
      AnalyticOnNhd ℂ (hillFreeGapQuadraticRoot h0q h0r (k : ℕ))
        ({E : ℂ | (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖} ×ˢ ball (0 : Coeff 2) η) ∧
      (∀ p ∈ ball (0 : Coeff 2) η, ∀ E : ℂ, (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖ →
        hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p)^2=hillLocalGapPolynomial 0 h0q h0r (k : ℕ) p E ∧
        hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p) ≠ 0 ∧
        ‖E-freeHillEnergy k‖/2 ≤ ‖hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p)‖ ∧
        ‖hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p)‖ ≤ 2*‖E-freeHillEnergy k‖) ∧
      ∀ p ∈ ball (0 : Coeff 2) η,
        CircleIntegrable (fun E : ℂ => (hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p))⁻¹) (freeHillEnergy k) (k : ℝ) ∧
        (∮ E in C(freeHillEnergy k,(k : ℝ)), (hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p))⁻¹) = -(2*(Real.pi : ℂ)*I) := by
  obtain ⟨V,hV,h0V,hQ⟩ := exists_hillFreeGap_local_quadratic_root_chart h0q h0r (k : ℕ) k.property (1/16) (by norm_num) (by norm_num)
  obtain ⟨W,hW,h0W,hpairs⟩ := exists_hillFreeGap_localized_pairs_neighborhood h0q h0r (k : ℕ) k.property (1/128) (by norm_num)
  obtain ⟨η,hη,hsub⟩ := Metric.isOpen_iff.mp (hV.inter hW) 0 ⟨h0V,h0W⟩
  refine ⟨η,hη,?_⟩
  obtain ⟨hc,hRlo,hRhi⟩ := hillFreeGap_energy_radius_geometry h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ)
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r (k : ℕ) k.property).1
    (hillRealGapContour_geometry 0 h0q h0r (k : ℕ) k.property).2.1
  have hsmall (E : ℂ) (hE : (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖) :
      (1/16)*R ≤ ‖E-(hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ)‖ := by rw [hc];dsimp only [R];linarith
  have hQa : AnalyticOnNhd ℂ (hillFreeGapQuadraticRoot h0q h0r (k : ℕ))
      ({E : ℂ | (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖} ×ˢ ball (0 : Coeff 2) η) :=
    hQ.1.mono (fun t ht => ⟨hsmall t.1 ht.1,(hsub ht.2).1⟩)
  have hdata (p : Coeff 2) (hp : p ∈ ball 0 η) (E : ℂ) (hE : (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖) :=
    hQ.2 p (hsub hp).1 E (hsmall E hE)
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
    obtain ⟨hboundary,a,ha,b,hb,_,_,hm⟩ := hpairs p (hsub hp).2
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
/-- The finite head and uniform tail share one positive complex source ball. -/
theorem exists_hillRadiusEnergyCircle_all_quadratic_data :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ k : ℕ+,
      AnalyticOnNhd ℂ (hillFreeGapQuadraticRoot h0q h0r (k : ℕ))
        ({E : ℂ | (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖} ×ˢ ball (0 : Coeff 2) η) ∧
      (∀ p ∈ ball (0 : Coeff 2) η, ∀ E : ℂ, (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖ →
        hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p)^2=hillLocalGapPolynomial 0 h0q h0r (k : ℕ) p E ∧
        hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p) ≠ 0 ∧
        ‖E-freeHillEnergy k‖/2 ≤ ‖hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p)‖ ∧
        ‖hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p)‖ ≤ 2*‖E-freeHillEnergy k‖) ∧
      ∀ p ∈ ball (0 : Coeff 2) η,
        CircleIntegrable (fun E : ℂ => (hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p))⁻¹) (freeHillEnergy k) (k : ℝ) ∧
        (∮ E in C(freeHillEnergy k,(k : ℝ)), (hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p))⁻¹) = -(2*(Real.pi : ℂ)*I) := by
  let P := fun (k : ℕ+) (p : Coeff 2) =>
    (∀ E : ℂ, (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖ →
      AnalyticAt ℂ (hillFreeGapQuadraticRoot h0q h0r (k : ℕ)) (E,p) ∧
      hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p)^2=hillLocalGapPolynomial 0 h0q h0r (k : ℕ) p E ∧
      hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p) ≠ 0 ∧
      ‖E-freeHillEnergy k‖/2 ≤ ‖hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p)‖ ∧
      ‖hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p)‖ ≤ 2*‖E-freeHillEnergy k‖) ∧
    CircleIntegrable (fun E : ℂ => (hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p))⁻¹) (freeHillEnergy k) (k : ℝ) ∧
    (∮ E in C(freeHillEnergy k,(k : ℝ)), (hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,p))⁻¹) = -(2*(Real.pi : ℂ)*I)
  have hlocal (k : ℕ+) : ∀ᶠ p in 𝓝 (0 : Coeff 2), P k p := by
    obtain ⟨η,hη,hQa,hdata,hperiod⟩ := exists_hillRadiusEnergyCircle_local_quadratic_data h0q h0r k
    filter_upwards [ball_mem_nhds (0 : Coeff 2) hη] with p hp
    exact ⟨fun E hE => ⟨hQa (E,p) ⟨hE,hp⟩,hdata p hp E hE⟩,hperiod p hp⟩
  obtain ⟨N,_,hQ⟩ := exists_hillRadiusEnergyCircle_quadratic_data h0q h0r 1
  have htail (k : ℕ+) (hk : N ≤ (k : ℕ)) (p : Coeff 2) (hp : p ∈ ball 0 1) : P k p :=
    ⟨fun E hE => ⟨(hQ k hk).1 (E,p) ⟨hE,hp⟩,(hQ k hk).2.1 p hp E hE⟩,(hQ k hk).2.2 p hp⟩
  obtain ⟨η,hη,hη1,hdata⟩ := exists_ball_forall_pos_index_of_local_and_uniform_tail
    P (0 : Coeff 2) hlocal N 1 (by norm_num) htail
  refine ⟨η,hη,hη1,?_⟩
  intro k
  exact ⟨fun t ht => ((hdata k t.2 ht.2).1 t.1 ht.1).1,
    fun p hp E hE => ((hdata k p hp).1 E hE).2,fun p hp => (hdata k p hp).2⟩

end NLS.KdV
