import NLS.ZakharovShabat.SourceNormalizedEnergyAction
import NLS.ZakharovShabat.SourceNormalizedActionUniformTailCircles

/-! One complex source neighborhood makes the SAME original Cauchy
energy action ratios analytic before ALL sufficiently high positive
labels. The actual periodic midpoint stays away from zero there. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {W : Set (CoeffPair 2)}

theorem exists_local_normalizedEnergyActionRatio_common_analytic
    (C : SourceFullAbelianUniformCauchyFamily (by norm_num) (by norm_num) W)
    (φ : realTypeSourceSubmodule 2)
    (hφ : φ.val∈ball C.discs.source.val C.discs.sourceRadius) :
    ∃ N : ℕ, ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val∈U ∧
      U⊆ball C.discs.source.val C.discs.sourceRadius ∧
      ∀ n : ℕ+, N≤(n:ℕ) → AnalyticOnNhd ℂ (C.normalizedEnergyActionRatio (n:ℕ)) U := by
  obtain ⟨r,hr,hsub,hC⟩ := C.exists_ball_normalizedWeightedActions (sourceHigherActionAtlas (by norm_num) (by norm_num)) φ hφ
  obtain ⟨M,hM,_,hrealM,hm⟩ := exists_global_source_analytic_midpoint_squaredGap (by norm_num : (2:ℝ≥0∞)≠⊤) (by norm_num)
  obtain ⟨N,V,hV,hφV,hgeom⟩ := exists_local_sourceNormalizedAction_uniform_tail_circle_data
    (by norm_num : (2:ℝ≥0∞)≠⊤) (by norm_num) φ.val φ.property
  let U := (ball φ.val r∩M)∩V
  refine ⟨N,U,(isOpen_ball.inter hM).inter hV,⟨⟨mem_ball_self hr,hrealM φ.property⟩,hφV⟩,
    (fun ψ hψ => (hsub hψ.1.1).2),?_⟩
  intro n hn ψ hψ
  have hτa := (hm ψ hψ.1.2 (n:ℕ)).1
  have hτ : sourceStandardRootMidpoint (by norm_num) (by norm_num) ψ (n:ℕ)≠0 := by
    have hn' : N≤(((n:ℕ):ℤ)).natAbs := by simpa only [Int.natAbs_natCast] using hn
    have hb := (hgeom ψ hψ.2 (n:ℕ) hn').1
      (sourcePeriodicMidpoint_mem_segment (by norm_num) (by norm_num) ψ (n:ℕ))
    have hb' : ‖sourceStandardRootMidpoint (by norm_num) (by norm_num) ψ (n:ℕ)-
        (Real.pi:ℂ)*(n:ℕ)‖<Real.pi/8 := by
      simpa only [mem_ball,dist_eq_norm,sourceStandardRootMidpoint,Int.cast_natCast] using hb
    intro he
    rw [he,zero_sub,norm_neg,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_natCast] at hb'
    have hnr : (1:ℝ)≤n := by exact_mod_cast n.property
    nlinarith [Real.pi_pos]
  exact (analyticAt_const.mul ((hC (n:ℕ) 1).1 ψ hψ.1.1)).div (hτa.pow 2) (pow_ne_zero 2 hτ)

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
