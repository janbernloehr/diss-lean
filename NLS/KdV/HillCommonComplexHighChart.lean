import NLS.KdV.HillBoundedComplexPeriodChart
import NLS.KdV.HillComplexHighPeriodZero
import NLS.KdV.HillContourHilbertPsiBounds
import NLS.KdV.HillHighRegularCorrectionDecay
import NLS.KdV.HillBoundedComplexTailPeriodControl

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillSelectedPsi_common_complex_high_contour_chart (n : ℕ) (hn : 1 ≤ n) :
    ∃ G : ℂ × Coeff 2 → ℂ, ∃ U : Set (Coeff 2), IsOpen U ∧ SpectralWeight.one.toCoeff q ∈ U ∧
      ∃ N : ℕ, 1 ≤ N ∧ ∃ C : ℝ, 0 < C ∧
        AnalyticOnNhd ℂ G (univ ×ˢ U) ∧
        (∀ p ∈ U, ∀ k : ℕ, N ≤ k →
          (∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
            (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
            (E,p) ∈ hillAbelianComplexRootDomain 0 h0q h0r ∧
              ‖G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p)‖ ≤ C/(k : ℝ)^3) ∧
          (∮ E in C((hillRealGapCenter 0 h0q h0r k : ℂ),
            hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
            G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p)) = 0) ∧
        ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
          SpectralWeight.one.toCoeff r.val ∈ U ∧ ∀ E : ℂ,
            G (E,SpectralWeight.one.toCoeff r.val) = hillAbelianSelectedGlobalPsi r.val r.property.1 r.property.2 n hn E := by
  obtain ⟨N,hN,a,P,U,hU,hqU,B,A,L,hB,hA,hL,ha,hP,hdata,hmatch⟩ :=
    exists_hillSelectedPsi_bounded_complex_period_chart q hq hr h0q h0r n hn
  obtain ⟨M,hM,D,hD,hinverse⟩ := exists_hillFreeGapContour_bounded_complex_tail_inverse_bound h0q h0r B
  let K := max N (max M (2*n))
  let S := 4*Real.exp ((8/Real.pi^2)*A)*(1+D*B)/L
  let G := hillComplexBranchPsi n a P
  have hS : 0 < S := by dsimp [S];positivity
  have hGa : AnalyticOnNhd ℂ G (univ ×ˢ U) := analyticOnNhd_hillComplexBranchPsi n a P U ha hP
    (fun p hp => norm_pos_iff.mp (hL.trans_le (hdata p hp).2.2.1))
  refine ⟨G,U,hU,hqU,K,hN.trans (le_max_left _ _),2*(n : ℝ)*S/Real.pi^2,by positivity,hGa,?_,?_⟩
  · intro p hp k hk
    have hkN : N ≤ k := (le_max_left N _).trans hk
    have hkM : M ≤ k := (le_max_left M _).trans ((le_max_right N _).trans hk)
    have hk2n : 2*n ≤ k := (le_max_right M _).trans ((le_max_right N _).trans hk)
    have hk1 : 1 ≤ k := hN.trans hkN
    have hnk : n ≠ k := by omega
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hpB := (hdata p hp).1
    have haA := (hdata p hp).2.1
    have hPL := (hdata p hp).2.2.1
    refine ⟨?_,?_⟩
    · intro E hE
      obtain ⟨hdom,hinv⟩ := hinverse p hpB k hkM E hE
      refine ⟨hdom,?_⟩
      apply norm_le_cubic_decay_of_scaled_freeHillValue_bound n k hn hk2n S
      have hratio : ‖hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p)‖ ≤ 1+D*B := by
        have h := norm_le_norm_sub_add (hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p)) 1
        rw [norm_one] at h
        have hd : D*‖p‖/(k : ℝ) ≤ D*‖p‖ := div_le_self (by positivity) hkR
        have hmul : D*‖p‖ ≤ D*B := mul_le_mul_of_nonneg_left hpB hD.le
        exact h.trans (by linarith)
      have hfree := norm_scaled_hillAbelianHilbertPsi_free_root_le h0q h0r n k hn hk1 hnk E hE (a p)
      have hfree' : ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
          (hillAbelianHilbertPsi n (E,a p)/hillEnergyCanonicalRootProduct 0 h0q h0r E)‖ ≤
          (4/(k : ℝ))*Real.exp ((8/Real.pi^2)*A) := by
        apply hfree.trans
        gcongr
      have hroot : hillEnergyCanonicalRootProduct 0 h0q h0r E ≠ 0 :=
        hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain 0 h0q h0r E
          (hillRealGapContour_sphere_subset 0 h0q h0r k hk1 hE)
      have he : (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*(G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p)) =
          ((((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
            (hillAbelianHilbertPsi n (E,a p)/hillEnergyCanonicalRootProduct 0 h0q h0r E))*
              (hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p))/P p := by
        dsimp only [G,hillComplexBranchPsi]
        field_simp
      rw [he,norm_div,norm_mul]
      apply (div_le_div₀ (by positivity : 0 ≤ (4/(k : ℝ))*Real.exp ((8/Real.pi^2)*A)*(1+D*B))
        (mul_le_mul hfree' hratio (norm_nonneg _) (by positivity)) hL hPL).trans_eq
      dsimp only [S]
      ring
    · exact circleIntegral_hillComplexBranch_high_eq_zero_of_mixed q hq hr h0q h0r N n k hn hk1 hkN hnk.symm
        (a p) p (P p) (hdata p hp).2.2.2
  · let Q : RealPeriodOneHillPotential → Coeff 2 := fun r => SpectralWeight.one.toCoeff r.val
    have hQ : Continuous Q := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
    filter_upwards [hmatch,hQ.continuousAt.tendsto.eventually (hU.mem_nhds hqU)] with r hrmatch hrU
    exact ⟨hrU,hrmatch⟩

end NLS.KdV
