import NLS.KdV.HillFilledFreeGapRoot
import NLS.KdV.HillFreeContourRadicandBound
import NLS.KdV.HillDeflatedRadicandFactorization

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFreeDeflatedRoot_uniform_inverse_bound :
    ∃ C : ℝ, 0<C ∧ ∀ k : ℕ, 1≤k → ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
      ‖(hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E)⁻¹‖ ≤
        C*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) := by
  obtain ⟨d,hd,hbound⟩ := exists_hillFreeGapContour_free_radicand_bound h0q h0r
  refine ⟨1/Real.sqrt d,by positivity,?_⟩
  intro k hk
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk).1
    (hillRealGapContour_geometry 0 h0q h0r k hk).2.1
  let f : ℂ → ℂ := fun E => (hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E)⁻¹
  have hfill : closedBall c R ⊆ hillGapFilledDomain 0 h0q h0r k :=
    hillRealGapContour_closedBall_subset_filledDomain 0 h0q h0r k hk
  have hf : AnalyticOnNhd ℂ f (closedBall c R) := by
    intro E hE
    exact (analyticOnNhd_hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E (hfill hE)).inv
      (hillDeflatedEnergyCanonicalRoot_ne_zero 0 h0q h0r k hk E (hfill hE))
  have hout (E : ℂ) (hE : E∈sphere c R) : ‖f E‖≤(1/Real.sqrt d)*R := by
    have hEq := hillL2Radicand_eq_gap_polynomial_mul_deflated_sq 0 h0q h0r k hk E (hfill (sphere_subset_closedBall hE))
    rw [map_zero] at hEq
    obtain ⟨hl,hu⟩ := hillFreeGapEndpoints h0q h0r k hk
    rw [hl,hu,← hillFreeGapCenter h0q h0r k hk] at hEq
    have hn : ‖hillL2Radicand 0 E‖=R^2*‖hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E‖^2 := by
      have he : ‖E-c‖=R := by simpa only [mem_sphere,dist_eq_norm] using hE
      rw [hEq,norm_mul,norm_mul,norm_pow]
      change ‖E-c‖*‖E-c‖*_=R^2*_
      rw [he]
      ring
    have hsqrt : 0<Real.sqrt d := Real.sqrt_pos.mpr hd
    have hlow : Real.sqrt d≤R*‖hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E‖ := by
      have hh := hbound k hk E hE
      rw [hn] at hh
      apply (sq_le_sq₀ hsqrt.le (mul_nonneg hR.le (norm_nonneg _))).mp
      rw [Real.sq_sqrt hd.le,mul_pow]
      exact hh
    have hnroot : 0<‖hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E‖ := by
      by_contra h
      have he : ‖hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E‖=0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
      rw [he,mul_zero] at hlow
      linarith
    change ‖(hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E)⁻¹‖≤_
    rw [norm_inv]
    have hh : 1/‖hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E‖≤R/Real.sqrt d :=
      (div_le_div_iff₀ hnroot hsqrt).mpr (by simpa only [one_mul] using hlow)
    simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using hh
  intro E hE
  have hdc : DiffContOnCl ℂ f (ball c R) :=
    DiffContOnCl.mk_ball (hf.differentiableOn.mono ball_subset_closedBall) hf.continuousOn
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc
  · intro w hw
    rw [frontier_ball c hR.ne'] at hw
    exact hout w hw
  · rw [closure_ball c hR.ne']
    exact hE

theorem exists_hillFilledFreeGapRoot_uniform_inverse_bound :
    ∃ C : ℝ, 0<C ∧ ∀ B : ℝ, ∃ N : ℕ, 1≤N ∧ ∀ p : Coeff 2, ‖p‖≤B →
      ∀ k : ℕ, N≤k → ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
        (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
        ‖(hillFilledFreeGapRoot h0q h0r k (E,p))⁻¹‖ ≤
          C*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) := by
  obtain ⟨C,hC,hfree⟩ := exists_hillFreeDeflatedRoot_uniform_inverse_bound h0q h0r
  refine ⟨(3/2)*C,by positivity,?_⟩
  intro B
  obtain ⟨N,hN,hroot⟩ := exists_hillFilledFreeGapRoot_bounded_complex_analytic h0q h0r (B+1)
  refine ⟨N,hN,?_⟩
  intro p hp k hk E hE
  have hpB : p∈ball (0 : Coeff 2) (B+1) := by rw [mem_ball,dist_zero_right];linarith
  have hk1 := hN.trans hk
  have hne := hillDeflatedEnergyCanonicalRoot_ne_zero 0 h0q h0r k hk1 E
    (hillRealGapContour_closedBall_subset_filledDomain 0 h0q h0r k hk1 hE)
  have hpn := ((hroot k hk).2 p hpB E hE).2.1
  have hr := ((hroot k hk).2 p hpB E hE).2.2.2
  have hrat : ‖hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E/hillFilledFreeGapRoot h0q h0r k (E,p)‖≤3/2 := by
    have hh := norm_add_le
      (hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E/hillFilledFreeGapRoot h0q h0r k (E,p)-1) (1:ℂ)
    rw [sub_add_cancel,norm_one] at hh
    linarith
  have he : (hillFilledFreeGapRoot h0q h0r k (E,p))⁻¹=
      (hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E/hillFilledFreeGapRoot h0q h0r k (E,p))*
        (hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E)⁻¹ := by field_simp
  rw [he,norm_mul]
  exact (mul_le_mul hrat (hfree k hk1 E hE) (norm_nonneg _) (by norm_num : (0:ℝ)≤3/2)).trans_eq (by ring)

end NLS.KdV
