import NLS.KdV.HillBalancedRegularFactor
import NLS.ZakharovShabat.SourceIsolatingUniformPoleBounds

/-! Uniform balanced-factor bounds before ALL positive Hill indices.
Both poles stay in their original signed discs. The original regular
quotient is recovered EXACTLY at the moving selected midpoint. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillIndependent_uniform_paired_pole_distance
    {V : Set (CoeffPair 2)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2)
    (hplace : ∀ k : ℤ, hillIndependentFrequency (c,d) k ∈ D k)
    (n m : ℕ+) (hmn : m ≠ n) (z : ℂ) (hz : z ∈ closure (D ((m:ℕ):ℤ))) :
    C⁻¹ ≤ ‖hillIndependentFrequency (c,d) ((n:ℕ):ℤ)-z‖ ∧
    C⁻¹ ≤ ‖hillIndependentFrequency (c,d) ((n:ℕ):ℤ)+z‖ := by
  have hmn' : ((m:ℕ):ℤ) ≠ ((n:ℕ):ℤ) := fun h => hmn (Subtype.ext (Int.ofNat.inj h))
  have hmneg : ((m:ℕ):ℤ) ≠ -((n:ℕ):ℤ) := by have := m.pos; have := n.pos; omega
  refine ⟨hD.uniform_pole_distance _ _ hmn' z hz _ (hplace _),?_⟩
  have hneg : -hillIndependentFrequency (c,d) ((n:ℕ):ℤ) ∈ D (-((n:ℕ):ℤ)) := by
    rw [← hillIndependentFrequency_neg]
    exact hplace _
  have h := hD.uniform_pole_distance _ _ hmneg z hz _ hneg
  simpa only [show -hillIndependentFrequency (c,d) ((n:ℕ):ℤ)-z = -(hillIndependentFrequency (c,d) ((n:ℕ):ℤ)+z) by ring,norm_neg] using h

theorem analyticOnNhd_hillBalancedMidpointRegularFactor
    {W V : Set (CoeffPair 2)} (H : SourceCorollary10_6Data (by norm_num) (by norm_num) W)
    {D : ℤ → Set ℂ} {C : ℝ} (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (ψ : CoeffPair 2) (hψW : ψ ∈ W) (hψV : ψ ∈ V) (c : ℂ)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (hplace : ∀ k : ℤ, hillIndependentFrequency (c,d) k ∈ D k)
    (n m : ℕ+) (hmn : m ≠ n) :
    AnalyticOnNhd ℂ (hillBalancedMidpointRegularFactor n m c d ψ) (closure (D ((m:ℕ):ℤ))) := by
  have hC : 0 < C⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hD.one_le)
  apply analyticOnNhd_pairedPoleNormalizedFactor
  · exact fun z hz => H.spectral ψ hψW _ _ z (hD.closedDisc_subset_omittedDomain ψ hψV _ hz)
  · exact fun z hz => norm_pos_iff.mp (hC.trans_le (hillIndependent_uniform_paired_pole_distance hD c d hplace n m hmn z hz).1)
  · exact fun z hz => norm_pos_iff.mp (hC.trans_le (hillIndependent_uniform_paired_pole_distance hD c d hplace n m hmn z hz).2)

theorem norm_hillBalancedMidpointRegularFactor_le
    {V : Set (CoeffPair 2)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (ψ : CoeffPair 2) (hψV : ψ ∈ V) (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2)
    (hplace : ∀ k : ℤ, hillIndependentFrequency (c,d) k ∈ D k)
    (n m : ℕ+) (hmn : m ≠ n) (z : ℂ) (hz : z ∈ D ((m:ℕ):ℤ))
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hquot : ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) ((m:ℕ):ℤ)
      (z,(hillIndependentFrequencyDisplacement (c,d),ψ))‖ ≤ Q) :
    ‖hillBalancedMidpointRegularFactor n m c d ψ z‖ ≤ (1+2*C/C⁻¹)^2*Q := by
  have hC : 0 < C := zero_lt_one.trans_le hD.one_le
  have hmid := hD.gap ψ hψV ((m:ℕ):ℤ) (sourcePeriodicMidpoint_mem_segment (by norm_num) (by norm_num) ψ _)
  have hdist := hD.uniform_disc_diameter ((m:ℕ):ℤ) z _ hz hmid
  have hpoles := hillIndependent_uniform_paired_pole_distance hD c d hplace n m hmn z (subset_closure hz)
  have h := norm_pairedPoleNormalizedFactor_le _ _
    (fun w => sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) ((m:ℕ):ℤ)
      (w,(hillIndependentFrequencyDisplacement (c,d),ψ))) z (2*C) C⁻¹ C⁻¹ Q (by positivity)
    (inv_pos.mpr hC) (inv_pos.mpr hC) hQ hpoles.1 hpoles.2 hdist hquot
  simpa only [pow_two,hillBalancedMidpointRegularFactor,sourceStandardRootMidpoint] using h

theorem hillBalancedMidpointRegularFactor_midpoint_eq_quotient
    {V : Set (CoeffPair 2)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (ψ : CoeffPair 2) (hψV : ψ ∈ V) (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2)
    (hplace : ∀ k : ℤ, hillIndependentFrequency (c,d) k ∈ D k)
    (n m : ℕ+) (hmn : m ≠ n) :
    hillBalancedMidpointRegularFactor n m c d ψ (sourceStandardRootMidpoint (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ)) =
      sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) ((m:ℕ):ℤ)
        (sourceStandardRootMidpoint (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ),(hillIndependentFrequencyDisplacement (c,d),ψ)) := by
  have hC : 0 < C⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hD.one_le)
  have hmid := hD.gap ψ hψV ((m:ℕ):ℤ) (sourcePeriodicMidpoint_mem_segment (by norm_num) (by norm_num) ψ _)
  have hpoles := hillIndependent_uniform_paired_pole_distance hD c d hplace n m hmn _ (subset_closure hmid)
  exact hillBalancedMidpointRegularFactor_midpoint n m c d ψ (norm_pos_iff.mp (hC.trans_le hpoles.1))
    (norm_pos_iff.mp (hC.trans_le hpoles.2))

end NLS.KdV
