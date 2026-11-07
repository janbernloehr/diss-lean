import NLS.KdV.HminusOneFractionalDirichletEigenfunctions
import NLS.KdV.HminusOneDirichletProjectionConvergence

/-! # Fractional power bounds for actual high Dirichlet contour projections -/
noncomputable section
open Set Metric Complex Filter Topology NLS.WeightedCoeff
namespace NLS.KdV

theorem exists_local_fractional_hillHminusDirichletProjection_bound
    (q : PeriodOneHminusOne) (r : ℝ) (hr : 1/2 < r) (hr1 : r < 1)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, ∃ B : ℝ,
      0 < N ∧ IsOpen V ∧ q ∈ V ∧ 0 ≤ B ∧
      ∀ b : WeightedCoeff (Weight.sobolev (-r)) 2, ‖b‖ ≤ M →
        sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) b ∈ V →
        ∀ n : ℕ+, N < (n:ℕ) →
          ‖singularDirichletContinuousRieszProjection
                (periodOneOriginal (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) b))
                (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-
            singularDirichletContinuousRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ ≤
            B*(n:ℝ)^(-(1-r)) := by
  obtain ⟨N₀,V₀,A,hN₀,hV₀,hq₀,hA,hcompare⟩ :=
    (hillHminusMiuraChartAt q).exists_uniform_fractional_dirichletEigenfunction_bound
      q (mem_hillHminusMiuraChartAt q) r hr hr1 M hM
  obtain ⟨N₁,V₁,_,hV₁,hq₁,_,hcircles⟩ := exists_uniform_hillHminusDirichlet_sourceCircles q
  obtain ⟨N₂,_,_,_,hzero,_,hfree⟩ := exists_uniform_hillHminusDirichlet_sourceCircles 0
  have hpow := (tendsto_rpow_neg_atTop (show (0:ℝ)<1-r by linarith)).comp
    tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun j : ℕ => A*(j:ℝ)^(-(1-r))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero] using hpow.const_mul A
  obtain ⟨N₃,hN₃⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds (show (0:ℝ)<1/16 by norm_num)))
  let N := max N₀ (max N₁ (max N₂ N₃))
  refine ⟨N,V₀ ∩ V₁,40*A,hN₀.trans_le (le_max_left _ _),hV₀.inter hV₁,⟨hq₀,hq₁⟩,
    mul_nonneg (by norm_num) hA,?_⟩
  intro b hb ha n hn
  let a : PeriodOneHminusOne := sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) b
  have hn₀ : N₀ < (n:ℕ) := (le_max_left _ _).trans_lt hn
  have hn₁ : N₁ < (n:ℕ) := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hn
  have hn₂ : N₂ < (n:ℕ) :=
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)).trans_lt hn
  have hn₃ : N₃ ≤ (n:ℕ) := by
    exact (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)).trans hn.le
  obtain ⟨g,hg0,hg,he⟩ := hcompare b hb ha.1 n hn₀
  obtain ⟨hcq,hl,hiso,hmq⟩ := hcircles a ha.2 n hn₁
  obtain ⟨hc0,_,hiso0,hm0⟩ := hfree 0 hzero n hn₂
  simp only [map_zero,hillHminusDirichletComplexLabels_zero] at hc0 hiso0 hm0
  have hd : 0 ≤ A*(n:ℝ)^(-(1-r)) := mul_nonneg hA (Real.rpow_nonneg (by positivity) _)
  have hdsmall : A*(n:ℝ)^(-(1-r)) ≤ 1/16 := (hN₃ (n:ℕ) hn₃).le
  have hp := norm_singularDirichletProjection_sub_free_le_of_sine_error
    (periodOneOriginal a) n (hillHminusDirichletComplexLabels a n) hcq hc0 hl
    (fun z hz hs => (hiso z (ball_subset_closedBall hz)).mp hs)
    (fun z hz hs => (hiso0 z (ball_subset_closedBall hz)).mp hs)
    hmq hm0 g hg0 hg hd hdsmall he
  exact hp.trans_eq (by ring)

end NLS.KdV
