import NLS.Articles.KdVKdV2Frequencies.RoughActionAmplitudeHead
import NLS.KdV.HillHminusUniformActionAmplitude
import NLS.SequenceSpaces.BoundedCoordinateAnalytic
import NLS.SequenceSpaces.PositiveFourierInverseMajorant

/-! # A common rough ball for every physical action amplitude

The finite head and actual contour-action tail give one source ball before
all positive indices. Their weighted amplitudes also form a genuine native
ell-infinity analytic map, with exact original physical normalization.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV NLS.ComplexAnalysis

private theorem zero_parity : SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0 := by simp
private theorem zero_real : IsRealHillPotential (SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by intro j; simp

theorem exists_hillHminus_all_physical_action_amplitudes :
    ∃ η C : ℝ, ∃ B : ℕ+ → PeriodOneHminusOne → ℂ, 0 < η ∧ 0 < C ∧ ∀ n : ℕ+,
      AnalyticOnNhd ℂ (B n) (ball (0 : PeriodOneHminusOne) η) ∧
      (∀ q ∈ ball (0 : PeriodOneHminusOne) η, Real.sqrt (1+(n : ℝ))*‖B n q‖ ≤ C) ∧
      B n 0=(Real.sqrt (2*(n : ℝ)*Real.pi) : ℂ)⁻¹ ∧
      ∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val ∈ ball (0 : PeriodOneHminusOne) η →
        B n (hillPhysicalHminusEmbedding p).val =
          hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 (n : ℕ) := by
  classical
  obtain ⟨r,N,hr,_hN,htail⟩ := exists_hillHminus_high_physical_action_amplitudes zero_parity zero_real
  let J : Finset ℕ+ := (Finset.range N).image (fun k => (⟨k+1,by omega⟩ : ℕ+))
  obtain ⟨s,D,hs,hD,hhead⟩ := exists_hillHminus_finite_physical_action_amplitudes J
  let η := min r s
  let B : ℕ+ → PeriodOneHminusOne → ℂ := fun n =>
    if hn : N ≤ (n : ℕ) then Classical.choose (htail n hn)
    else hillHminusLocalActionAmplitude zero_parity zero_real n
  have hη : 0 < η := lt_min hr hs
  have hdata (n : ℕ+) : AnalyticOnNhd ℂ (B n) (ball (0 : PeriodOneHminusOne) η) ∧
      (∀ q ∈ ball (0 : PeriodOneHminusOne) η, Real.sqrt (1+(n : ℝ))*‖B n q‖ ≤ D+2) ∧
      ∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val ∈ ball (0 : PeriodOneHminusOne) η →
        B n (hillPhysicalHminusEmbedding p).val =
          hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 (n : ℕ) := by
    by_cases hn : N ≤ (n : ℕ)
    · simp only [B,dif_pos hn]
      obtain ⟨ha,hb,hp⟩ := Classical.choose_spec (htail n hn)
      exact ⟨ha.mono (ball_subset_ball (min_le_left r s)),
        fun q hq => (hb q (ball_subset_ball (min_le_left r s) hq)).trans (by linarith),
        fun p hp0 => hp p (ball_subset_ball (min_le_left r s) hp0)⟩
    · simp only [B,dif_neg hn]
      have hnJ : n ∈ J := by
        apply Finset.mem_image.mpr
        refine ⟨(n : ℕ)-1,Finset.mem_range.mpr (by omega),?_⟩
        apply Subtype.ext
        change (n : ℕ)-1+1=(n : ℕ)
        exact Nat.sub_add_cancel n.property
      obtain ⟨ha,hb,hp⟩ := hhead n hnJ
      exact ⟨ha.mono (ball_subset_ball (min_le_right r s)),
        fun q hq => (hb q (ball_subset_ball (min_le_right r s) hq)).trans (by linarith),
        fun p hp0 => hp p (ball_subset_ball (min_le_right r s) hp0)⟩
  refine ⟨η,D+2,B,hη,by linarith,?_⟩
  intro n
  obtain ⟨ha,hb,hp⟩ := hdata n
  refine ⟨ha,hb,?_,hp⟩
  have hz : B n 0=hillAbelianAmplitudePrefactor 0 zero_parity zero_real (n : ℕ) := by
    simpa only [hillPhysicalHminusEmbedding,map_zero] using
      hp (⟨0,zero_parity,zero_real⟩ : RealPeriodOneHillPotential)
        (by simpa only [hillPhysicalHminusEmbedding,map_zero] using
          mem_ball_self hη)
  exact hz.trans (hillAbelianAmplitudePrefactor_free zero_parity zero_real (n : ℕ) n.property)

theorem exists_hillHminus_native_action_amplitude_symbol :
    ∃ η C : ℝ, ∃ M : PeriodOneHminusOne → Coeff ⊤,
      0 < η ∧ 0 < C ∧ AnalyticOnNhd ℂ M (ball (0 : PeriodOneHminusOne) η) ∧
      (∀ q ∈ ball (0 : PeriodOneHminusOne) η, ‖M q‖ ≤ C ∧ ∀ j : ℤ, j ≤ 0 → M q j=0) ∧
      (∀ n : ℕ+, M 0 (n : ℤ)=
        (Real.sqrt (1+(n : ℝ)) : ℂ)*(Real.sqrt (2*(n : ℝ)*Real.pi) : ℂ)⁻¹) ∧
      ∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val ∈ ball (0 : PeriodOneHminusOne) η → ∀ n : ℕ+,
        M (hillPhysicalHminusEmbedding p).val (n : ℤ)=
          (Real.sqrt (1+(n : ℝ)) : ℂ)*
            hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 (n : ℕ) := by
  classical
  obtain ⟨η,C,B,hη,hC,hB⟩ := exists_hillHminus_all_physical_action_amplitudes
  let f (q : PeriodOneHminusOne) (n : ℕ+) : ℂ := (Real.sqrt (1+(n : ℝ)) : ℂ)*B n q
  let a (q : PeriodOneHminusOne) : ℤ → ℂ := Coeff.positiveFamilyCoordinates (f q)
  have hf (q : PeriodOneHminusOne) (hq : q ∈ ball 0 η) (n : ℕ+) : ‖f q n‖ ≤ C := by
    simpa only [f,norm_mul,norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)] using (hB n).2.1 q hq
  have hab (q : PeriodOneHminusOne) (hq : q ∈ ball 0 η) (j : ℤ) : ‖a q j‖ ≤ C := by
    by_cases hj : 0 < j
    · exact (by simpa only [a,Coeff.positiveFamilyCoordinates,dif_pos hj] using hf q hq (Coeff.positivePoleIndex j hj))
    · simp only [a,Coeff.positiveFamilyCoordinates,dif_neg hj,norm_zero]
      exact hC.le
  have hm (q : PeriodOneHminusOne) (hq : q ∈ ball 0 η) : Memℓp (a q) ⊤ :=
    memℓp_infty ⟨C,by rintro _ ⟨j,rfl⟩; exact hab q hq j⟩
  let M : PeriodOneHminusOne → Coeff ⊤ := fun q => Coeff.ofFunctionOrZero ⊤ (a q)
  have hval (q : PeriodOneHminusOne) (hq : q ∈ ball 0 η) (j : ℤ) : M q j=a q j :=
    Coeff.ofFunctionOrZero_apply_of_mem ⊤ _ (hm q hq) j
  have hbound (q : PeriodOneHminusOne) (hq : q ∈ ball 0 η) : ‖M q‖ ≤ C := by
    apply lp.norm_le_of_forall_le hC.le
    intro j
    rw [hval q hq j]
    exact hab q hq j
  have hcoord (j : ℤ) : AnalyticOnNhd ℂ (fun q => M q j) (ball (0 : PeriodOneHminusOne) η) := by
    intro q hq
    have he : (fun u => a u j) =ᶠ[𝓝 q] (fun u => M u j) := by
      filter_upwards [isOpen_ball.mem_nhds hq] with u hu
      exact (hval u hu j).symm
    apply AnalyticAt.congr (f := fun u => a u j) ?_ he
    by_cases hj : 0 < j
    · simp only [a,Coeff.positiveFamilyCoordinates,dif_pos hj,f]
      exact analyticAt_const.mul ((hB (Coeff.positivePoleIndex j hj)).1 q hq)
    · simpa only [a,Coeff.positiveFamilyCoordinates,dif_neg hj] using
        (analyticAt_const (v := (0 : ℂ)) (𝕜 := ℂ) (x := q))
  refine ⟨η,C,M,hη,hC,Coeff.analyticOnNhd_of_bounded_coordinatewise M isOpen_ball hcoord C hbound,?_,?_,?_⟩
  · intro q hq
    refine ⟨hbound q hq,?_⟩
    intro j hj
    rw [hval q hq j]
    simp only [a,Coeff.positiveFamilyCoordinates,dif_neg (not_lt.mpr hj)]
  · intro n
    rw [hval 0 (mem_ball_self hη) (n : ℤ)]
    change Coeff.positiveFamilyCoordinates (f 0) (n : ℤ)=_
    rw [Coeff.positiveFamilyCoordinates_nat]
    exact congrArg (fun z : ℂ => (Real.sqrt (1+(n : ℝ)) : ℂ)*z) (hB n).2.2.1
  · intro p hp n
    rw [hval _ hp (n : ℤ)]
    change Coeff.positiveFamilyCoordinates (f (hillPhysicalHminusEmbedding p).val) (n : ℤ)=_
    rw [Coeff.positiveFamilyCoordinates_nat]
    exact congrArg (fun z : ℂ => (Real.sqrt (1+(n : ℝ)) : ℂ)*z) ((hB n).2.2.2 p hp)

end NLS.Articles.KdVKdV2Frequencies
