import NLS.Articles.KdVPseudomeasures.ComplexMidpointEstimate
import NLS.Articles.KdVPseudomeasures.SpectralWeightedGaps

/-! The ACTUAL complex midpoint has full arbitrary-source-weight endpoint
decay, uniformly before the weight and the potential on each original norm ball. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- ONE cutoff before BOTH the arbitrary original spectral weight and the
complex potential gives the full weighted high midpoint estimate. -/
theorem exists_uniform_sourceWeightedComplexMidpoint_high_bound
    (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) (Nmin : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ Nmin ≤ N ∧ ∀ w : SpectralWeight,
      ∀ q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤, ‖q‖ ≤ R →
      ∀ hp : IsPeriodicDistribution 1 q.val.toTempered, ∀ n : ℕ+, N ≤ (n:ℕ) →
        w.negativeSobolev r (n:ℤ)*‖sourceComplexDirichletMidpoint r hr (sourceForgetWeight w r q)
          (by rw [sourceForgetWeight_val];exact hp) n‖ ≤ 128*(6*Real.sqrt 6+12)*R := by
  obtain ⟨NM,hNM,hmin,hM⟩ := exists_uniform_sourceComplexMidpoint_coupling_bound r hr R Nmin
  obtain ⟨NL,_,hcut,hlabels⟩ := source_uniform_canonical_complex_labels_with_contraction r hr R
  refine ⟨max NM NL,hNM.trans (le_max_left _ _),hmin.trans (le_max_left _ _),?_⟩
  intro w q hq hp n hn
  have hnM : NM ≤ (n:ℕ) := (le_max_left _ _).trans hn
  have hnL : NL ≤ (n:ℕ) := (le_max_right _ _).trans hn
  let u := sourceForgetWeight w r q
  have hu : ‖u‖ ≤ R := (norm_sourceForgetWeight_le w r q).trans hq
  have hup : IsPeriodicDistribution 1 u.val.toTempered := by rw [sourceForgetWeight_val];exact hp
  let z := sourceHillComplexLabels r hr u (2*(n:ℕ))
  let gamma := z-sourceHillComplexLabels r hr u (2*(n:ℕ)-1)
  have hraw := hM u hu hup n hnM
  have hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2 := by
    have hmul := mul_le_mul_of_nonneg_left hq
      (show 0 ≤ endpointHillConstant r*(n:ℝ)^(r-1/2) by positivity [endpointHillConstant_pos r hr.2])
    have hc := hcut (n:ℕ) hnL
    have hnon : 0 ≤ endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ := by
      positivity [endpointHillConstant_pos r hr.2]
    nlinarith
  have hsW : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceWeightedEndpointCoefficients w r q‖ ≤ 1/2 := by
    rwa [norm_sourceWeightedEndpointCoefficients]
  obtain ⟨p,hl,hrr⟩ := (hlabels u hu).high_pair (n:ℕ) hnL
  have hz : z ∈ reducedHillStrip (n:ℕ) := by dsimp only [z];rw [hrr];exact p.right_mem
  have hg0 := EndpointHillComplexPair.general_weighted_gap_le w r hr.1 hr.2 (n:ℕ) n.property
    (sourceWeightedEndpointCoefficients w r q) hsW
  rw [← sourceEndpointCoefficients_forgetWeight w r q] at hg0
  have hg : w.negativeSobolev r (n:ℤ)*‖gamma‖ ≤ 6*Real.sqrt 6*‖q‖ := by
    have ht := hg0 p
    rw [← hl,← hrr,norm_sourceWeightedEndpointCoefficients] at ht
    exact ht
  have hc := endpointCouplings_weighted_le w r hr.1 hr.2 (n:ℕ) n.property z hz
    (sourceWeightedEndpointCoefficients w r q) hsW
  rw [← sourceEndpointCoefficients_forgetWeight w r q,norm_sourceWeightedEndpointCoefficients] at hc
  have hw := negativeSobolev_mode_le_three_double w r hr.1 hr.2 (n:ℕ) n.property
  have hb : w.negativeSobolev r (n:ℤ)*
      ‖endpointUpperCoupling r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r u,z)‖ ≤ 6*‖q‖ := by
    have ht := mul_le_mul_of_nonneg_right hw
      (norm_nonneg (endpointUpperCoupling r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r u,z)))
    nlinarith [hc.1]
  have hd : w.negativeSobolev r (n:ℤ)*
      ‖endpointLowerCoupling r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r u,z)‖ ≤ 6*‖q‖ := by
    have ht := mul_le_mul_of_nonneg_right hw
      (norm_nonneg (endpointLowerCoupling r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r u,z)))
    nlinarith [hc.2]
  calc
    _ ≤ w.negativeSobolev r (n:ℤ)*(128*(‖gamma‖+
        ‖endpointUpperCoupling r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r u,z)‖+
        ‖endpointLowerCoupling r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r u,z)‖)) :=
      mul_le_mul_of_nonneg_left hraw ((w.negativeSobolev r).positive _).le
    _ = 128*(w.negativeSobolev r (n:ℤ)*‖gamma‖+
        w.negativeSobolev r (n:ℤ)*‖endpointUpperCoupling r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r u,z)‖+
        w.negativeSobolev r (n:ℤ)*‖endpointLowerCoupling r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r u,z)‖) := by ring
    _ ≤ 128*(6*Real.sqrt 6*‖q‖+6*‖q‖+6*‖q‖) := by gcongr
    _ = 128*(6*Real.sqrt 6+12)*‖q‖ := by ring
    _ ≤ 128*(6*Real.sqrt 6+12)*R := by gcongr

end NLS.Articles.KdVPseudomeasures
