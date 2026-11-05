import NLS.KdV.HillRadiusQuadraticData
import NLS.KdV.HillComplexRootProductMatching
/-! # Actual quadratic/filled-root products on radius-k energy circles

Joint continuity and source connectedness select the actual continued
sheet from its exact free value, uniformly before all positive high modes.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillRadiusEnergyCircle_root_product_matching
    (η B : ℝ) (hη : 0 < η)
    (hsource : ∀ u ∈ ball (0 : Coeff 2) η, Coeff.periodDouble u ∈ ball (0 : Coeff 2) B)
    (hcover : ∀ u ∈ ball (0 : Coeff 2) η, ∀ k : ℕ+, ∀ E ∈ sphere (freeHillEnergy k) (k : ℝ),
      (E,periodOneL2Inclusion u) ∈ hillHminusContinuationDomain) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ k : ℕ+, N ≤ (k : ℕ) → ∀ u ∈ ball (0 : Coeff 2) η,
      ∀ E ∈ sphere (freeHillEnergy k) (k : ℝ),
        hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,Coeff.periodDouble u)*
          hillFilledFreeGapRoot h0q h0r (k : ℕ) (E,Coeff.periodDouble u) =
        hillHminusContinuedRoot (E,periodOneL2Inclusion u) := by
  obtain ⟨Nq,hNq,hQ⟩ := exists_hillRadiusEnergyCircle_quadratic_data h0q h0r B
  obtain ⟨Nr,_,hU⟩ := exists_hillFilledFreeGapRoot_bounded_complex_analytic h0q h0r B
  obtain ⟨Nf,_,hfactor⟩ := exists_hillFilledFreeGapUnit_bounded_complex_factorization h0q h0r B
  refine ⟨max Nq (max Nr Nf),hNq.trans (le_max_left _ _),?_⟩
  intro k hk u hu E hE
  have hkq := (le_max_left Nq (max Nr Nf)).trans hk
  have hkr := (le_max_left Nr Nf).trans ((le_max_right Nq (max Nr Nf)).trans hk)
  have hkf := (le_max_right Nr Nf).trans ((le_max_right Nq (max Nr Nf)).trans hk)
  obtain ⟨hc,hRlo,_⟩ := hillFreeGap_energy_radius_geometry h0q h0r k
  have hEold : E ∈ closedBall (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ)
      (hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ)) := by
    rw [hc]
    exact closedBall_subset_closedBall hRlo (sphere_subset_closedBall hE)
  have hd : (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖ := by
    rw [mem_sphere_iff_norm.mp hE]
    nlinarith [show (0 : ℝ) ≤ k by positivity]
  let L := fun v : Coeff 2 => hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,Coeff.periodDouble v)*
    hillFilledFreeGapRoot h0q h0r (k : ℕ) (E,Coeff.periodDouble v)
  let S := fun v : Coeff 2 => hillHminusContinuedRoot (E,periodOneL2Inclusion v)
  have hleft : ContinuousOn L (ball (0 : Coeff 2) η) :=
    (((hQ k hkq).1).continuousOn.comp (f := fun v : Coeff 2 => (E,Coeff.periodDouble v)) (by fun_prop) (fun v hv => ⟨hd,hsource v hv⟩)).mul
      (((hU (k : ℕ) hkr).1).continuousOn.comp (f := fun v : Coeff 2 => (E,Coeff.periodDouble v)) (by fun_prop) (fun v hv => ⟨hEold,hsource v hv⟩))
  have hright : ContinuousOn S (ball (0 : Coeff 2) η) :=
    analyticOnNhd_hillHminusContinuedRoot.continuousOn.comp (f := fun v : Coeff 2 => (E,periodOneL2Inclusion v)) (by fun_prop)
      (fun v hv => hcover v hv k E hE)
  have hsq (v : Coeff 2) (hv : v ∈ ball (0 : Coeff 2) η) : L v^2 = S v^2 := by
    have hp := hsource v hv
    have hpB := (mem_ball_zero_iff.mp hp).le
    change (_*_)^2 = hillHminusContinuedRoot (E,periodOneL2Inclusion v)^2
    calc
      _ = hillLocalGapPolynomial 0 h0q h0r (k : ℕ) (Coeff.periodDouble v) E *
          hillFilledFreeGapUnit h0q h0r (k : ℕ) (E,Coeff.periodDouble v) := by
        rw [mul_pow,((hQ k hkq).2.1 _ hp E hd).1,((hU (k : ℕ) hkr).2 _ hp E hEold).1]
      _ = hillL2Radicand (Coeff.periodDouble v) E := (hfactor _ hpB (k : ℕ) hkf E).symm
      _ = hillHminusRadicand (periodOneL2Inclusion v) E := (hillHminusRadicand_eq_hillL2 v E).symm
      _ = hillHminusContinuedRoot (E,periodOneL2Inclusion v)^2 :=
        (hillHminusContinuedRoot_sq _ (hcover v hv k E hE)).symm
  have h0η : (0 : Coeff 2) ∈ ball 0 η := mem_ball_self hη
  have hEc : E ≠ (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ) := by
    intro he
    have hh := mem_sphere_iff_norm.mp hE
    rw [hc] at he
    rw [he,sub_self,norm_zero] at hh
    have hkpos : (0 : ℝ) < k := by positivity
    linarith
  have hbaseprod : hillFreeGapQuadraticRoot h0q h0r (k : ℕ) (E,0)*
      hillFilledFreeGapRoot h0q h0r (k : ℕ) (E,0) = hillEnergyCanonicalRootProduct 0 h0q h0r E := by
    rw [hillFreeGapQuadraticRoot_base h0q h0r (k : ℕ) k.property E hEc,
      hillFilledFreeGapRoot_base h0q h0r (k : ℕ) k.property E hEold,
      hillEnergyCanonicalRootProduct_eq_endpoint_mul_deflated 0 h0q h0r (k : ℕ) k.property E]
    obtain ⟨hl,hr⟩ := hillFreeGapEndpoints h0q h0r (k : ℕ) k.property
    rw [hl,hr,← hillFreeGapCenter h0q h0r (k : ℕ) k.property]
    congr 1
    simp only [endpointRoot,normalizedStandardRoot,sub_self,zero_pow (by norm_num : 2 ≠ 0),
      zero_div,sub_zero,sqrt_one,mul_one]
    ring
  have hcoeff0 : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) =
      Coeff.periodDouble (0 : Coeff 2) := by rw [map_zero,map_zero]
  have hbase : L 0 = S 0 := by
    have hr := (hillRadiusEnergyCircle_actual_physical_root h0q h0r 0 h0q h0r 0 hcoeff0 k E hE (hcover 0 h0η k E hE)).2
    simpa only [L,S,map_zero] using hbaseprod.trans hr.symm
  have heq := (convex_ball (0 : Coeff 2) η).isPreconnected.eq_of_sq_eq hleft hright hsq
    (fun {v} hv => hillHminusSourceFamily.root_ne_zero _ (hcover v hv k E hE)) h0η hbase
  exact heq hu
end NLS.KdV
