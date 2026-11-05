import NLS.KdV.HillHminusLocalActionAmplitude
import NLS.KdV.HillHminusGapSquareSequence
import NLS.ComplexAnalysis.AnalyticZeroLinearBound

/-! # Actual rough action amplitudes on any finite collection of gaps

The source ball is common to the prescribed finite collection, including
closed gaps. The infinite-tail estimate is a separate assembly obligation.
The native normalized energy gap squares are ell1 analytic on one ball
before all positive indices.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV NLS.ComplexAnalysis

private theorem zero_parity : SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0 := by simp
private theorem zero_real : IsRealHillPotential (SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by intro j; simp
private theorem zero_rough_real : IsRealPeriodOneHminusOne 0 := by intro j; simp

theorem exists_hillHminus_finite_physical_action_amplitudes (J : Finset ℕ+) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ n ∈ J,
      AnalyticOnNhd ℂ (hillHminusLocalActionAmplitude zero_parity zero_real n)
        (ball (0 : PeriodOneHminusOne) η) ∧
      (∀ q ∈ ball (0 : PeriodOneHminusOne) η,
        Real.sqrt (1+(n : ℝ))*‖hillHminusLocalActionAmplitude zero_parity zero_real n q‖ ≤ C) ∧
      ∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val ∈ ball (0 : PeriodOneHminusOne) η →
        hillHminusLocalActionAmplitude zero_parity zero_real n (hillPhysicalHminusEmbedding p).val =
          hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 (n : ℕ) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
      exact ⟨1,1,by norm_num,by norm_num,fun n hn => (Finset.notMem_empty n hn).elim⟩
  | @insert n J hn ih =>
      obtain ⟨r,B,hr,hB,ha,hb,hp⟩ :=
        exists_hillHminusLocalActionAmplitude_analytic_physical zero_parity zero_real n
      obtain ⟨s,D,hs,hD,hJ⟩ := ih
      refine ⟨min r s,B+D,lt_min hr hs,add_pos hB hD,?_⟩
      intro m hm
      rcases Finset.mem_insert.mp hm with hm | hm
      · subst m
        exact ⟨ha.mono (ball_subset_ball (min_le_left r s)),
          fun q hq => (hb q (ball_subset_ball (min_le_left r s) hq)).trans (by linarith),
          fun p hq => hp p (ball_subset_ball (min_le_left r s) hq)⟩
      · obtain ⟨hMa,hMb,hMp⟩ := hJ m hm
        exact ⟨hMa.mono (ball_subset_ball (min_le_right r s)),
          fun q hq => (hMb q (ball_subset_ball (min_le_right r s) hq)).trans (by linarith),
          fun p hq => hMp p (ball_subset_ball (min_le_right r s) hq)⟩

theorem exists_hillHminus_native_gap_square_packet :
    ∃ η C : ℝ, ∃ G : PeriodOneHminusOne → Coeff 1,
      0 < η ∧ 0 < C ∧ AnalyticOnNhd ℂ G (ball (0 : PeriodOneHminusOne) η) ∧ G 0 = 0 ∧
      (∀ q ∈ ball (0 : PeriodOneHminusOne) η, ‖G q‖ ≤ C*‖q‖ ∧
        ∀ hq : IsRealPeriodOneHminusOne q, ∀ n : ℕ+,
          G q (n : ℤ) = (((hillHminusRealLabels q hq (2*(n : ℕ)) : ℂ)-
            (hillHminusRealLabels q hq (2*(n : ℕ)-1) : ℂ))/(n : ℂ))^2) ∧
      ∀ q : PeriodOneHminusOne, ∀ j : ℤ, j ≤ 0 → G q j = 0 := by
  obtain ⟨V,G,hV,h0V,ha,hreal,hnonpos⟩ :=
    exists_hillHminus_native_gap_square_sequence 0 zero_rough_real
  have hG0 : G 0 = 0 := by
    ext j
    change G 0 j = 0
    by_cases hj : 0 < j
    · let n : ℕ+ := ⟨j.toNat,by omega⟩
      have he : j = (n : ℤ) := by
        change j = (j.toNat : ℤ)
        exact (Int.toNat_of_nonneg hj.le).symm
      rw [he,hreal 0 h0V zero_rough_real n]
      simp only [hillHminusRealLabels_zero]
      have hl : (2*(n : ℕ)-1+1)/2 = (n : ℕ) := by have hp := n.property; omega
      have hu : (2*(n : ℕ)+1)/2 = (n : ℕ) := by omega
      rw [hl,hu,sub_self,zero_div,zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    · exact hnonpos 0 j (not_lt.mp hj)
  obtain ⟨r,B,hr,hB,har,hbound⟩ := exists_analytic_zero_linear_bound G (ha 0 h0V) hG0
  obtain ⟨s,hs,hsub⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0V)
  let η := min r s
  exact ⟨η,B,G,lt_min hr hs,hB,har.mono (ball_subset_ball (min_le_left r s)),hG0,
    fun q hq => ⟨hbound q (ball_subset_ball (min_le_left r s) hq),
      hreal q (hsub (ball_subset_ball (min_le_right r s) hq))⟩,hnonpos⟩

end NLS.Articles.KdVKdV2Frequencies
