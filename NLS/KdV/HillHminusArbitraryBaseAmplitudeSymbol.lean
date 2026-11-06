import NLS.KdV.HillHminusArbitraryBaseFiniteAmplitudes
import NLS.KdV.HillHminusArbitraryBaseActionAmplitudes
import NLS.SequenceSpaces.BoundedCoordinateAnalytic
import NLS.SequenceSpaces.PositiveFourierInverseMajorant
import NLS.SequenceSpaces.PositiveAnalyticReciprocal

/-! # All actual action amplitudes and their native reciprocal at any real rough base

The finite head and infinite tail share one complex H^-1 ball before all
positive indices. The weighted amplitudes and their reciprocals are native
ell-infinity analytic maps with uniform bounds and exact physical recovery.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem exists_hillHminus_arbitrary_base_all_action_amplitudes
    (q0 : PeriodOneHminusOne) (hr0 : IsRealPeriodOneHminusOne q0) :
    ∃ η a C : ℝ, ∃ B : ℕ+ → PeriodOneHminusOne → ℂ, 0 < η ∧ 0 < a ∧ 0 < C ∧
      ∀ n : ℕ+, AnalyticOnNhd ℂ (B n) (ball q0 η) ∧
        (∀ q ∈ ball q0 η, a ≤ Real.sqrt (1+(n : ℝ))*‖B n q‖ ∧
          Real.sqrt (1+(n : ℝ))*‖B n q‖ ≤ C) ∧
        ∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val ∈ ball q0 η →
          B n (hillOriginalHminusSource p.val) =
            hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 (n : ℕ) := by
  classical
  obtain ⟨N,V,_hN,hV,hqV,htail⟩ :=
    exists_hillHminus_arbitrary_base_high_physical_action_amplitudes q0
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hqV)
  let J : Finset ℕ+ := (Finset.range N).image (fun k => (⟨k+1,by omega⟩ : ℕ+))
  obtain ⟨s,a,D,H,hs,ha,hD,hhead⟩ :=
    exists_hillHminus_arbitrary_base_finite_action_amplitudes q0 hr0 J
  let η := min r s
  let B : ℕ+ → PeriodOneHminusOne → ℂ := fun n =>
    if hn : N ≤ (n : ℕ) then Classical.choose (htail n hn) else H n
  refine ⟨η,min a (1/8),D+2,B,lt_min hr hs,lt_min ha (by norm_num),by linarith,?_⟩
  intro n
  by_cases hn : N ≤ (n : ℕ)
  · simp only [B,dif_pos hn]
    obtain ⟨hBa,hbound,hphysical⟩ := Classical.choose_spec (htail n hn)
    have hηV : ball q0 η ⊆ V := fun _ h => hrV (ball_subset_ball (min_le_left r s) h)
    refine ⟨hBa.mono hηV,?_,fun p hp => hphysical p (hηV hp)⟩
    intro q hq
    have h := hbound q (hηV hq)
    exact ⟨(min_le_right a (1/8)).trans h.1,h.2.trans (by linarith)⟩
  · simp only [B,dif_neg hn]
    have hnJ : n ∈ J := by
      apply Finset.mem_image.mpr
      refine ⟨(n : ℕ)-1,Finset.mem_range.mpr (by omega),?_⟩
      apply Subtype.ext
      change (n : ℕ)-1+1 = (n : ℕ)
      exact Nat.sub_add_cancel n.property
    obtain ⟨hBa,hbound,hphysical⟩ := hhead n hnJ
    have hηs : ball q0 η ⊆ ball q0 s := ball_subset_ball (min_le_right r s)
    refine ⟨hBa.mono hηs,?_,fun p hp => hphysical p (hηs hp)⟩
    intro q hq
    have h := hbound q (hηs hq)
    exact ⟨(min_le_left a (1/8)).trans h.1,h.2.trans (by linarith)⟩

theorem exists_hillHminus_arbitrary_base_native_amplitude_reciprocal
    (q0 : PeriodOneHminusOne) (hr0 : IsRealPeriodOneHminusOne q0) :
    ∃ η a C : ℝ, ∃ M N : PeriodOneHminusOne → Coeff ⊤,
      0 < η ∧ 0 < a ∧ 0 < C ∧ AnalyticOnNhd ℂ M (ball q0 η) ∧
        AnalyticOnNhd ℂ N (ball q0 η) ∧
        (∀ q ∈ ball q0 η, ‖M q‖ ≤ C ∧ ‖N q‖ ≤ a⁻¹ ∧
          (∀ j : ℤ, j ≤ 0 → M q j = 0 ∧ N q j = 0) ∧
          ∀ n : ℕ+, a ≤ ‖M q (n : ℤ)‖ ∧ N q (n : ℤ) = (M q (n : ℤ))⁻¹ ∧
            M q (n : ℤ)*N q (n : ℤ) = 1) ∧
        ∀ p : RealPeriodOneHillPotential, hillOriginalHminusSource p.val ∈ ball q0 η →
          ∀ n : ℕ+, M (hillOriginalHminusSource p.val) (n : ℤ) =
            (Real.sqrt (1+(n : ℝ)) : ℂ)*
              hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 (n : ℕ) := by
  classical
  obtain ⟨η,a,C,B,hη,ha,hC,hB⟩ := exists_hillHminus_arbitrary_base_all_action_amplitudes q0 hr0
  let f (q : PeriodOneHminusOne) (n : ℕ+) : ℂ := (Real.sqrt (1+(n : ℝ)) : ℂ)*B n q
  let v (q : PeriodOneHminusOne) : ℤ → ℂ := Coeff.positiveFamilyCoordinates (f q)
  have hf (q : PeriodOneHminusOne) (hq : q ∈ ball q0 η) (n : ℕ+) : ‖f q n‖ ≤ C := by
    simpa only [f,norm_mul,norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)] using
      ((hB n).2.1 q hq).2
  have hv (q : PeriodOneHminusOne) (hq : q ∈ ball q0 η) (j : ℤ) : ‖v q j‖ ≤ C := by
    by_cases hj : 0 < j
    · simpa only [v,Coeff.positiveFamilyCoordinates,dif_pos hj] using hf q hq (Coeff.positivePoleIndex j hj)
    · simp only [v,Coeff.positiveFamilyCoordinates,dif_neg hj,norm_zero]
      exact hC.le
  have hm (q : PeriodOneHminusOne) (hq : q ∈ ball q0 η) : Memℓp (v q) ⊤ :=
    memℓp_infty ⟨C,by rintro _ ⟨j,rfl⟩; exact hv q hq j⟩
  let M : PeriodOneHminusOne → Coeff ⊤ := fun q => Coeff.ofFunctionOrZero ⊤ (v q)
  have hval (q : PeriodOneHminusOne) (hq : q ∈ ball q0 η) (j : ℤ) : M q j = v q j :=
    Coeff.ofFunctionOrZero_apply_of_mem ⊤ _ (hm q hq) j
  have hbound (q : PeriodOneHminusOne) (hq : q ∈ ball q0 η) : ‖M q‖ ≤ C := by
    apply lp.norm_le_of_forall_le hC.le
    intro j
    rw [hval q hq j]
    exact hv q hq j
  have hcoord (j : ℤ) : AnalyticOnNhd ℂ (fun q => M q j) (ball q0 η) := by
    intro q hq
    have he : (fun u => v u j) =ᶠ[𝓝 q] (fun u => M u j) := by
      filter_upwards [isOpen_ball.mem_nhds hq] with u hu
      exact (hval u hu j).symm
    apply AnalyticAt.congr (f := fun u => v u j) ?_ he
    by_cases hj : 0 < j
    · simp only [v,Coeff.positiveFamilyCoordinates,dif_pos hj,f]
      exact analyticAt_const.mul ((hB (Coeff.positivePoleIndex j hj)).1 q hq)
    · simpa only [v,Coeff.positiveFamilyCoordinates,dif_neg hj] using
        (analyticAt_const (v := (0 : ℂ)) (𝕜 := ℂ) (x := q))
  have hMa := Coeff.analyticOnNhd_of_bounded_coordinatewise M isOpen_ball hcoord C hbound
  have hlower (q : PeriodOneHminusOne) (hq : q ∈ ball q0 η) (n : ℕ+) : a ≤ ‖M q (n : ℤ)‖ := by
    rw [hval q hq (n : ℤ)]
    change a ≤ ‖Coeff.positiveFamilyCoordinates (f q) (n : ℤ)‖
    rw [Coeff.positiveFamilyCoordinates_nat]
    simpa only [f,norm_mul,norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)] using
      ((hB n).2.1 q hq).1
  obtain ⟨N,hNa,hNd⟩ := Coeff.exists_positive_analytic_reciprocal (ball q0 η) isOpen_ball M hMa a ha hlower
  refine ⟨η,a,C,M,N,hη,ha,hC,hMa,hNa,?_,?_⟩
  · intro q hq
    refine ⟨hbound q hq,(hNd q hq).1,?_,fun n => ⟨hlower q hq n,(hNd q hq).2.2 n⟩⟩
    intro j hj
    refine ⟨?_,(hNd q hq).2.1 j hj⟩
    rw [hval q hq j]
    simp only [v,Coeff.positiveFamilyCoordinates,dif_neg (not_lt.mpr hj)]
  · intro p hp n
    rw [hval _ hp (n : ℤ)]
    change Coeff.positiveFamilyCoordinates (f (hillOriginalHminusSource p.val)) (n : ℤ) = _
    rw [Coeff.positiveFamilyCoordinates_nat]
    exact congrArg (fun z : ℂ => (Real.sqrt (1+(n : ℝ)) : ℂ)*z) ((hB n).2.2 p hp)

end NLS.KdV
