import NLS.KdV.HillRadiusMidpointMoments
import NLS.KdV.HillL2AnnularSeparation

/-! # One native complex source ball for all literal midpoint coordinates -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillLocalGapMidpoint_all_periodOne_analytic :
    ∃ η : ℝ, 0 < η ∧ ∀ k : ℕ+,
      AnalyticOnNhd ℂ (fun u : Coeff 2 => hillLocalGapMidpoint 0 h0q h0r (k : ℕ) (Coeff.periodDouble u))
        (ball (0 : Coeff 2) η) := by
  obtain ⟨ηm,hηm,hmom⟩ := exists_hillFreeGap_all_radius_moment_identification h0q h0r
  obtain ⟨ηb,b,hηb,hb,hlower⟩ := exists_hillL2_all_annular_radicand_lower_bound
  let η := min ηm ηb
  have hη : 0 < η := lt_min hηm hηb
  let F := fun t : ℂ × Coeff 2 => hillL2Radicand (Coeff.periodDouble t.2) t.1
  have hF : AnalyticOnNhd ℂ F univ := by
    intro t _
    exact (analyticOnNhd_hillL2Radicand_joint (t.1,Coeff.periodDouble t.2) (mem_univ _)).comp
      (f := fun s : ℂ × Coeff 2 => (s.1,Coeff.periodDouble s.2))
      (analyticAt_fst.prod ((Coeff.periodDouble.toContinuousLinearMap.analyticAt t.2).comp analyticAt_snd))
  have hboundary (k : ℕ+) (u : Coeff 2) (hu : u ∈ ball 0 η)
      (E : ℂ) (hE : E ∈ sphere (freeHillEnergy k) (k : ℝ)) : F (E,u) ≠ 0 := by
    apply norm_pos_iff.mp
    apply hb.trans_le
    have hd := mem_sphere_iff_norm.mp hE
    exact hlower u (ball_subset_ball (min_le_right _ _) hu) k E
      (by rw [hd]; linarith [show (0 : ℝ) < k by positivity])
      (by rw [hd]; linarith [show (0 : ℝ) < k by positivity])
  have hmatch (k : ℕ+) (u : Coeff 2) (hu : u ∈ ball 0 η) :
      logarithmicCircleMoment F (freeHillEnergy k) (k : ℝ) 1 u =
        2*hillLocalGapMidpoint 0 h0q h0r (k : ℕ) (Coeff.periodDouble u) := by
    exact (hmom k (Coeff.periodDouble u)
      (by rw [mem_ball_zero_iff,Coeff.norm_periodDouble]; exact (mem_ball_zero_iff.mp hu).trans_le (min_le_left _ _))
      (hboundary k u hu)).2
  refine ⟨η,hη,?_⟩
  intro k u hu
  have ha := analyticOnNhd_logarithmicCircleMoment F hF (freeHillEnergy k) (k : ℝ)
    (by positivity) 1 isOpen_ball (hboundary k)
  apply ((ha u hu).div_const (c := 2)).congr
  filter_upwards [isOpen_ball.mem_nhds hu] with v hv
  rw [hmatch k v hv]
  ring

end NLS.KdV
