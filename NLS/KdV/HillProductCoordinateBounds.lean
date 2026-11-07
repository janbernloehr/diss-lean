import NLS.KdV.HillIndependentMultiplierBound

/-! Actual nonlinear weighted Hill period coordinates obey a single
lp majorant on the ORIGINAL isolating discs. The extra balanced
quadratic multiplier is analytic on the filled selected disc, so the
verified complex/collapsed-gap contour estimate applies without poles. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillWeightedProductPeriod_coordinate_bound
    {W V : Set (CoeffPair 2)} (H : SourceCorollary10_6Data (by norm_num) (by norm_num) W)
    {D : ℤ → Set ℂ} {C : ℝ} (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (ψ : CoeffPair 2) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2)
    (hplace : ∀ k : ℤ, hillIndependentFrequency (c,d) k ∈ D k)
    (n m : ℕ+) (hmn : m ≠ n) (a r : ℝ) (hr : 0 < r)
    (he : D ((m:ℕ):ℤ) = ball (a:ℂ) r) (Q : ℝ)
    (hquot : ∀ z ∈ D ((m:ℕ):ℤ),
      ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) ((m:ℕ):ℤ)
        (z,(hillIndependentFrequencyDisplacement (c,d),ψ))‖ ≤ Q) :
    ‖(2*Real.pi:ℂ)⁻¹*(hillPeriodEquationWeight n m*
      hillEnergyProductFixedPeriod n c ψ (hD.periodCircle ψ hψV ((m:ℕ):ℤ) a r hr he) d)‖ ≤
      (‖hillIndependentFrequencyDisplacement (c,d) ((m:ℕ):ℤ)‖+
        ‖sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ)‖+
        ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ)‖)*(Real.pi^2*C*(C*Q)) := by
  let b := hillIndependentFrequencyDisplacement (c,d)
  let P := hD.periodCircle ψ hψV ((m:ℕ):ℤ) a r hr he
  let M : ℂ → ℂ := fun z => (Real.pi:ℂ)^2*(((n:ℕ):ℂ)+((m:ℕ):ℂ))/
    (hillIndependentFrequency (c,d) ((n:ℕ):ℤ)+z)
  let R : ℂ → ℂ := fun z => ((((n:ℕ):ℤ)-((m:ℕ):ℤ):ℤ):ℂ)*
    sourcePsiGapRegularFactor (by norm_num) (by norm_num) ((n:ℕ):ℤ) ((m:ℕ):ℤ) b ψ z
  let f : ℂ → ℂ := fun z => (hillIndependentFrequency (c,d) ((m:ℕ):ℤ)-z)*(M z*R z)
  have hc : 0 ≤ C := zero_le_one.trans hD.one_le
  have hmn' : ((m:ℕ):ℤ) ≠ ((n:ℕ):ℤ) := by
    intro h
    exact hmn (Subtype.ext (Int.ofNat.inj h))
  have hcl : closedBall (a:ℂ) r = closure (D ((m:ℕ):ℤ)) := by rw [he,closure_ball _ hr.ne']
  have hsep (z : ℂ) (hz : z ∈ closedBall (a:ℂ) r) := hD.weighted_separation_closure
    ((n:ℕ):ℤ) ((m:ℕ):ℤ) hmn' (hillIndependentFrequency (c,d) ((n:ℕ):ℤ)) (hplace _) z (hcl ▸ hz)
  have hM (z : ℂ) (hz : z ∈ closedBall (a:ℂ) r) := hillIndependent_multiplier_bound hD (c,d) hplace n m z (hcl ▸ hz)
  have hRa : AnalyticOnNhd ℂ R (closedBall (a:ℂ) r) := by
    intro z hz
    have hq := H.spectral ψ hψW b ((m:ℕ):ℤ) z (P.closedBall_subset_omittedDomain hz)
    exact analyticAt_const.mul ((analyticAt_const.mul hq).div
      (analyticAt_const.sub analyticAt_id) (sub_ne_zero.mpr (hsep z hz).1.symm))
  have hMa : AnalyticOnNhd ℂ M (closedBall (a:ℂ) r) := by
    intro z hz
    exact analyticAt_const.div (analyticAt_const.add analyticAt_id) (hM z hz).1
  have hf : AnalyticOnNhd ℂ f (closedBall (a:ℂ) r) := by
    intro z hz
    exact (analyticAt_const.sub analyticAt_id).mul ((hMa z hz).mul (hRa z hz))
  have hRb (z : ℂ) (hz : z ∈ D ((m:ℕ):ℤ)) : ‖R z‖ ≤ C*Q := by
    have hs := hsep z (hcl.symm ▸ subset_closure hz)
    simp only [R,sourcePsiGapRegularFactor,norm_mul,norm_div,norm_I,one_mul]
    rw [← mul_div_assoc,mul_div_right_comm]
    exact mul_le_mul hs.2 (hquot z hz) (norm_nonneg _) hc
  have heq : hillPeriodEquationWeight n m*hillEnergyProductFixedPeriod n c ψ P d =
      ∮ z in C((a:ℂ),r), f z/sourceStandardRoot (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ) z := by
    unfold hillEnergyProductFixedPeriod
    change hillPeriodEquationWeight n m*((2*Real.pi:ℂ)⁻¹*
      (∮ z in C((a:ℂ),r), hillEnergyProductPeriodIntegrand n c ψ (z,d))) = _
    calc
      _ = ∮ z in C((a:ℂ),r), (2*Real.pi:ℂ)⁻¹*hillPeriodEquationWeight n m*
          hillEnergyProductPeriodIntegrand n c ψ (z,d) := by rw [circleIntegral.integral_const_mul]; ring
      _ = _ := by
        apply circleIntegral.integral_congr hr.le
        intro z hz
        have hzD : z ∈ closedBall (a:ℂ) r := sphere_subset_closedBall hz
        have hp := hillWeightedProductIntegrand_independent_candidate n m c d ψ z
          (P.sphere_subset_rootDomain hz) (hM z hzD).1
        have hg := sourcePsiContourIntegrandJoint_eq_gap_factor (by norm_num) (by norm_num)
          ((n:ℕ):ℤ) ((m:ℕ):ℤ) b ψ z (P.sphere_subset_rootDomain hz) (hsep z hzD).1
        change sourcePsiCandidate ((n:ℕ):ℤ) (z,b)/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z =
          ((hillIndependentFrequency (c,d) ((m:ℕ):ℤ)-z)/sourceStandardRoot (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ) z)*
            sourcePsiGapRegularFactor (by norm_num) (by norm_num) ((n:ℕ):ℤ) ((m:ℕ):ℤ) b ψ z at hg
        change (2*Real.pi:ℂ)⁻¹*hillPeriodEquationWeight n m*hillEnergyProductPeriodIntegrand n c ψ (z,d) =
          f z/sourceStandardRoot (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ) z
        calc
          _ = M z*((((n:ℕ):ℂ)-((m:ℕ):ℂ))*(sourcePsiCandidate ((n:ℕ):ℤ) (z,b)/
              sourceCanonicalRoot (by norm_num) (by norm_num) ψ z)) := by
            rw [hp]
            dsimp only [M,b]
            ring
          _ = _ := by
            rw [hg]
            dsimp only [f,R]
            push_cast
            ring
  obtain ⟨z,hz,_,hb,_⟩ := P.lemma12_3_circle f hf
  rw [PiecewiseC1Loop.integral_circle] at hb
  rw [heq]
  apply hb.trans
  rw [show ‖f z‖ = ‖hillIndependentFrequency (c,d) ((m:ℕ):ℤ)-z‖*(‖M z‖*‖R z‖) by simp only [f,norm_mul]]
  exact mul_le_mul (norm_displacedRoot_sub_gap_le (by norm_num) (by norm_num) b ψ ((m:ℕ):ℤ) z hz)
    (mul_le_mul (hM z (hcl.symm ▸ subset_closure (hD.gap ψ hψV _ hz))).2
      (hRb z (hD.gap ψ hψV _ hz)) (norm_nonneg _) (mul_nonneg (sq_nonneg _) hc))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)

end NLS.KdV
