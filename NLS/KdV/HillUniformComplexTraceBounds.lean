import NLS.KdV.HillL2SmallPotentialTrace
import NLS.KdV.HillFreeGapContourGeometry
import NLS.ComplexAnalysis.DiscBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillL2Discriminant_uniform_complex_free_disc_bound :
    ∃ C : ℝ, 0<C ∧ ∀ B : ℝ, ∃ N : ℕ, 1≤N ∧ ∀ p : Coeff 2, ‖p‖≤B →
      ∀ k : ℕ, N≤k → ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
        (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
        ‖hillL2Discriminant p E‖ ≤ C := by
  let H := Real.pi/2
  refine ⟨4*Real.exp H,by positivity,?_⟩
  intro B
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (8*Real.exp H*B/Real.pi))
  have hN1 : 1≤N := by
    have hh : (1:ℝ)<N := (le_max_left _ _).trans_lt hN
    exact_mod_cast hh.le
  refine ⟨N,hN1,?_⟩
  intro p hp k hk
  have hk1 := hN1.trans hk
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hs : 4*Real.exp H*‖p‖≤(k:ℝ)*Real.pi/2 := by
    have hh : 8*Real.exp H*B/Real.pi≤(k:ℝ) :=
      ((le_max_right _ _).trans hN.le).trans (by exact_mod_cast hk)
    have hd := (div_le_iff₀ Real.pi_pos).mp hh
    have hp' := mul_le_mul_of_nonneg_left hp (by positivity : 0≤4*Real.exp H)
    linarith
  have hout (E : ℂ) (hE : E∈sphere c R) : ‖hillL2Discriminant p E‖≤4*Real.exp H := by
    have hg := hillFreeGapContour_frequency_bounds h0q h0r k hk1 E hE
    have hz : 0<‖sqrt E‖ := lt_of_lt_of_le (by positivity : 0<(k:ℝ)*Real.pi/2) hg.2.2.2
    have hs' := hs.trans hg.2.2.2
    have herr := hillL2Discriminant_free_error_small p (sqrt E) (norm_pos_iff.mp hz) H hg.2.2.1 hs'
    rw [complex_sqrt_sq] at herr
    have herr' : 8*(Real.exp H)^2*‖p‖/‖sqrt E‖≤2*Real.exp H := by
      apply (div_le_iff₀ hz).mpr
      nlinarith [mul_le_mul_of_nonneg_left hs' (by positivity : 0≤2*Real.exp H)]
    have hcos : ‖2*cos (sqrt E)‖≤2*Real.exp H := by
      rw [norm_mul,norm_ofNat]
      exact mul_le_mul_of_nonneg_left
        ((norm_complex_cos_le_exp_im _).trans (Real.exp_le_exp.mpr hg.2.2.1)) (by norm_num)
    have htri := norm_add_le (hillL2Discriminant p E-2*cos (sqrt E)) (2*cos (sqrt E))
    rw [sub_add_cancel] at htri
    linarith
  intro E hE
  exact norm_le_of_sphere_bound (fun z => (analyticOnNhd_hillL2Discriminant p z (mem_univ _)).differentiableAt) c hR
    (4*Real.exp H) hout (by simpa only [mem_closedBall,dist_eq_norm] using hE)

end NLS.KdV
