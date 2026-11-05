import NLS.Articles.KdVKdV2Frequencies.NativeRoughAbelianPacket
import NLS.SequenceSpaces.WeightedSourceSignedCompletion
import NLS.SequenceSpaces.SobolevHalfWeights
import NLS.KdV.HillAbelianCoordinateSequence

/-! # The original signed Abelian map is natively analytic in H-minus-one

The target is the literal Sobolev-minus-one-half sequence space. Physical
recovery holds throughout one rough ball with no physical L2 smallness,
including closed gaps and nonzero means. The whole rough real form is
preserved by the constructed holomorphic completion.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

theorem exists_hillHminus_native_signed_abelian_coordinates :
    ∃ η C : ℝ, ∃ Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2,
      0 < η ∧ 0 < C ∧ AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η) ∧ Z 0=0 ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) η, ‖Z q‖≤C*‖q‖ ∧ (Z q).val 0=0) ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) η, IsRealPeriodOneHminusOne q →
        ∀ j : ℤ, (Z q).val (-j)=conj ((Z q).val j)) ∧
      ∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
        (Z (hillPhysicalHminusEmbedding p).val).val j=
          hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j := by
  obtain ⟨r,A,P,hr,hA,hPa,hP0,hPb,hPp⟩ := exists_hillHminus_native_normalized_abelian_packet
  let v := Weight.sobolev (-1)
  let w := Weight.sobolev (-1/2)
  let I := WeightedCoeff.weightIsometry w 2
  let Y : PeriodOneHminusOne → WeightedCoeff w 2 := fun q => I.symm (P q)
  have hYa : AnalyticOnNhd ℂ Y (ball (0 : PeriodOneHminusOne) r) := fun q hq =>
    (I.symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp (hPa q hq)
  have hY0 : Y 0=0 := by simp only [Y,hP0,map_zero]
  have hYb (q : PeriodOneHminusOne) (hq : q∈ball 0 r) : ‖Y q‖≤A*(‖q‖+‖q‖^2) := by
    rw [show ‖Y q‖=‖P q‖ from I.symm.norm_map _]
    exact (hPb q hq).1.trans (by nlinarith [sq_nonneg ‖q‖])
  have hYnonpos (q : PeriodOneHminusOne) (hq : q∈ball 0 r) (j : ℤ) (hj : j≤0) : (Y q).val j=0 := by
    change P q j/(w j : ℂ)=0
    rw [(hPb q hq).2 j hj,zero_div]
  have hYp (p : RealPeriodOneHillPotential) (hp : (hillPhysicalHminusEmbedding p).val∈ball 0 r)
      (n : ℕ+) : (Y (hillPhysicalHminusEmbedding p).val).val (n : ℤ)=
      hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos := by
    change P (hillPhysicalHminusEmbedding p).val (n : ℤ)/(w (n : ℤ) : ℂ)=_
    have hw : (w (n : ℤ) : ℂ)=(Real.sqrt (1+(n : ℝ)) : ℂ)⁻¹ := by
      simp only [w,Weight.sobolev_neg_half_apply,Int.cast_natCast,
        abs_of_nonneg (show (0 : ℝ)≤(n : ℝ) by positivity),ofReal_inv]
    rw [hPp p hp n,hw,div_inv_eq_mul]
    exact div_mul_cancel₀ _ (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne')
  let Z := WeightedCoeff.weightedSourceSignedCompletion v w Y
  obtain ⟨hZa,hZ0,_hZbound⟩ :=
    WeightedCoeff.weightedSourceSignedCompletion_analytic_bound v w Y r A hYa hY0 hYb
  have hcoord (q : PeriodOneHminusOne) (j : ℤ) : (Z q).val j=
      (Y q).val j+conj ((Y (periodOneHminusConjugation q)).val (-j)) :=
    WeightedCoeff.weightedSourceSignedCompletion_apply v w (Weight.sobolev_neg (-1))
      (Weight.sobolev_neg (-1/2)) Y q j
  have hcenter (q : PeriodOneHminusOne) (hq : q∈ball 0 r) : (Z q).val 0=0 := by
    have hJq : periodOneHminusConjugation q∈ball (0 : PeriodOneHminusOne) r := by
      simpa only [mem_ball_zero_iff,norm_periodOneHminusConjugation] using hq
    rw [hcoord,hYnonpos q hq 0 le_rfl,neg_zero,hYnonpos _ hJq 0 le_rfl,map_zero,zero_add]
  have hreal (q : PeriodOneHminusOne) (hqr : IsRealPeriodOneHminusOne q) (j : ℤ) :
      (Z q).val (-j)=conj ((Z q).val j) := by
    have hJ : periodOneHminusConjugation q=q := (periodOneHminusConjugation_fixed_iff q).mpr hqr
    rw [hcoord,hcoord,hJ,neg_neg,map_add,conj_conj]
    exact add_comm _ _
  have hp (p : RealPeriodOneHillPotential) (hp : (hillPhysicalHminusEmbedding p).val∈ball 0 r) (j : ℤ) :
      (Z (hillPhysicalHminusEmbedding p).val).val j=
        hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j := by
    let q := (hillPhysicalHminusEmbedding p).val
    have hJ : periodOneHminusConjugation q=q :=
      (periodOneHminusConjugation_fixed_iff q).mpr (hillPhysicalHminusEmbedding p).property
    have hnat (n : ℕ) : (Y q).val (n : ℤ)=
        hillAbelianPositiveCoefficient SpectralWeight.one (hillUnitRealSourceUnembed p) n := by
      by_cases hn : 1≤n
      · let k : ℕ+ := ⟨n,by omega⟩
        have hh := hYp p hp k
        change (Y q).val (n : ℤ)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn at hh
        rw [hillAbelianPositiveCoefficient,dif_pos hn]
        have ht := congrArg (fun a : RealPeriodOneHillPotential =>
          hillDirichletAbelianCoordinate a.val a.property.1 a.property.2 n hn)
          (hillRealWeightedEmbedding_unitUnembed p)
        exact hh.trans ht.symm
      · have hn0 : n=0 := by omega
        subst n
        simpa only [Nat.cast_zero,hillAbelianPositiveCoefficient_zero] using hYnonpos q hp 0 le_rfl
    rw [hcoord,hJ]
    by_cases hj : 0≤j
    · rw [hYnonpos q hp (-j) (by omega),map_zero,add_zero,hillAbelianRawCoordinateSequence,if_pos hj]
      have hn : ((j.natAbs : ℕ) : ℤ)=j := by rw [Int.natCast_natAbs,abs_of_nonneg hj]
      rw [← hn]
      exact hnat _
    · rw [hYnonpos q hp j (by omega),zero_add,hillAbelianRawCoordinateSequence,if_neg hj]
      congr 1
      have hn : ((j.natAbs : ℕ) : ℤ)=-j := by rw [Int.natCast_natAbs,abs_of_nonpos (by omega : j≤0)]
      rw [← hn]
      exact hnat _
  obtain ⟨s,C,hs,hC,hSa,hlin⟩ := exists_analytic_zero_linear_bound Z (hZa 0 (mem_ball_self hr)) hZ0
  let η := min r s
  refine ⟨η,C,Z,lt_min hr hs,hC,hSa.mono (ball_subset_ball (min_le_right r s)),hZ0,?_,?_,?_⟩
  · intro q hq
    exact ⟨hlin q (ball_subset_ball (min_le_right r s) hq),hcenter q (ball_subset_ball (min_le_left r s) hq)⟩
  · intro q _hq hqr j
    exact hreal q hqr j
  · intro p hp0 j
    exact hp p (ball_subset_ball (min_le_left r s) hp0) j

end NLS.Articles.KdVKdV2Frequencies
