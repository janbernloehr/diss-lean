import NLS.KdV.HillActionAngleNativeAnalytic

/-! The ACTUAL native Cartesian map has the source's exact positive
minus-half Hilbert norm, not only an equivalent bracket norm. -/
noncomputable section
open Set Complex NLS.LpSequence
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillHminusNativeCartesianMap_norm_sq (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) :
    ‖hillHminusNativeCartesianMap q‖^2 = ∑' n : ℕ+,
      (‖hillHminusActionAngleX n q‖^2+‖hillHminusActionAngleY n q‖^2)/(n:ℝ) := by
  let w := Weight.positiveSobolev (-1/2)
  let f : ℤ → ℝ := fun k => (w k)^2*
    (‖(hillHminusNativeCartesianMap q).fst.val k‖^2+‖(hillHminusNativeCartesianMap q).snd.val k‖^2)
  have he := WeightedCoeffPair.norm_rpow_eq_tsum (p := 2) (by norm_num) w (hillHminusNativeCartesianMap q)
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_two] at he
  change ‖hillHminusNativeCartesianMap q‖^2 = ∑' k : ℤ, f k at he
  have hs : (∑' n : ℕ+, f ((n:ℕ):ℤ)) = ∑' k : ℤ, f k := by
    apply positiveEmbedding.injective.tsum_eq
    intro k hk
    by_contra hnot
    have hc := hillHminusActionAngle_sequences_coordinates q hq k
    have hx : (hillHminusNativeCartesianMap q).fst.val k = 0 := by
      change (hillHminusActionAngleXSequence q).val k = 0
      rw [hc.1,positiveScalarExtension_zero_of_not_mem_range _ k hnot]
    have hy : (hillHminusNativeCartesianMap q).snd.val k = 0 := by
      change (hillHminusActionAngleYSequence q).val k = 0
      rw [hc.2,positiveScalarExtension_zero_of_not_mem_range _ k hnot]
    exact hk (by simp only [f,hx,hy,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_add,mul_zero])
  rw [← hs] at he
  apply he.trans
  apply tsum_congr
  intro n
  have hp := hillHminusNativeCartesianMap_positive q hq n
  have hn : (0:ℝ) ≤ (n:ℕ) := by positivity
  dsimp only [f,w]
  rw [hp.1,hp.2,Weight.positiveSobolev_neg_half_positive,div_pow,one_pow,Real.sq_sqrt hn]
  ring

end NLS.KdV
