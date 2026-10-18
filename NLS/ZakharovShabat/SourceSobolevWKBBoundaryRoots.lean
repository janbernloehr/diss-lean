import NLS.ZakharovShabat.SourceSobolevWKBCharacteristicModels
import NLS.ZakharovShabat.SourceTailIsolation
import NLS.ZakharovShabat.ClassicalSobolevRemainderSequenceBounds

/-! # WKB characteristic models at actual canonical boundary roots

A common complex Sobolev neighborhood and signed tail cutoff give order-(N+1) pointwise bounds at both boundary root sequences. This is not a weighted L2 remainder estimate.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The explicit characteristic model is uniformly small at both actual
canonical boundary-root sequences on a complex Sobolev neighborhood.
The cutoff includes both signed tails and the bound gains order N+1. -/
theorem exists_local_nlsWKB_boundary_root_model_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (a₀ : SobolevSource s) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀ ∈ U ∧
      ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab ∈ U, ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ θ : BoundaryCondition, ∀ n : ℤ, K ≤ n.natAbs →
        ‖nlsWKBSeparatedCharacteristicModel θ a b N
          (canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ
            (higherSobolevSourceInclusion s ab) n)‖ ≤ C/(1+(n.natAbs:ℝ))^(N+1) := by
  obtain ⟨K₀,V,hV,ha₀,hiso⟩ := exists_uniform_source_tail_isolation
    (by norm_num) (by norm_num) (higherSobolevSourceInclusion s a₀)
  let U := (higherSobolevSourceInclusion s ⁻¹' V) ∩ Metric.ball a₀ 1
  have hU : IsOpen U := (hV.preimage (higherSobolevSourceInclusion s).continuous).inter Metric.isOpen_ball
  have hUa₀ : a₀ ∈ U := ⟨ha₀,by simp⟩
  have hR : 0 ≤ ‖a₀‖+1 := by positivity
  obtain ⟨T,hT,C,hC,hmodel⟩ :=
    exists_uniform_source_nlsWKB_characteristic_models_error_bound s N hs hNs (‖a₀‖+1) hR 1
  obtain ⟨K₁,hK₁,hfreq⟩ := exists_near_free_frequency_cutoff 1 (by norm_num)
  obtain ⟨L,hL⟩ := exists_nat_gt T
  refine ⟨U,hU,hUa₀,max (K₀+1) (max K₁ L),
    hK₁.trans_le ((le_max_left _ _).trans (le_max_right _ _)),C,hC,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb θ n hn
  have habR : ‖ab‖ ≤ ‖a₀‖+1 := by
    have hd : ‖ab-a₀‖ < 1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hab.2
    have ht := norm_le_norm_sub_add ab a₀
    linarith
  have hn₀ : K₀ < n.natAbs := by have := (le_max_left (K₀+1) (max K₁ L)).trans hn; omega
  have hn₁ : K₁ ≤ n.natAbs := (le_max_left K₁ L).trans ((le_max_right _ _).trans hn)
  have hnL : L ≤ n.natAbs := (le_max_right K₁ L).trans ((le_max_right _ _).trans hn)
  let z := canonicalPeriodOneBoundaryRoots (by norm_num) (by norm_num) θ (higherSobolevSourceInclusion s ab) n
  have hzdisc : z ∈ refinedResonantDisk n := by
    have hh := hiso _ hab.1 n hn₀
    cases θ with
    | dirichlet => exact hh.2.2.1
    | neumann => exact hh.2.2.2.1
  have hδ : ‖z-(Real.pi:ℂ)*n‖ ≤ 1 := by
    have hd : ‖z-(Real.pi:ℂ)*n‖ < Real.pi/4 := by
      simpa only [refinedResonantDisk,Metric.mem_ball,dist_eq_norm] using hzdisc
    linarith [Real.pi_lt_four]
  obtain ⟨him,_,hzn⟩ := hfreq n hn₁ z hδ
  have hnn : 1 ≤ (n.natAbs:ℝ) := by exact_mod_cast hK₁.trans_le hn₁
  have hnz : (n.natAbs:ℝ) ≤ ‖z‖ := by nlinarith [Real.two_le_pi]
  have hzT : T ≤ ‖z‖ := by
    have hh : (L:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast hnL
    linarith
  have hm := (hmodel ab habR a b ha hb hpa hpb hca hcb z hzT him).2.2 θ
  rw [periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero (by norm_num) (by norm_num) θ _ n,
    zero_sub,norm_neg] at hm
  apply hm.trans
  have hi : ‖(2*I*z)⁻¹‖ ≤ (1+(n.natAbs:ℝ))⁻¹ := by
    simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
    exact inv_anti₀ (by positivity) (by linarith)
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hi (N+1)) hC
  simpa only [inv_pow,div_eq_mul_inv] using hp

end NLS.ZakharovShabat
