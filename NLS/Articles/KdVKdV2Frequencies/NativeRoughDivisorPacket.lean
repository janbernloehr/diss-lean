import NLS.Articles.KdVKdV2Frequencies.NativeRoughDirichletPacket
import NLS.KdV.HillHminusGapMidpointSequence

/-! # Actual rough midpoint and Dirichlet divisor data on one Hilbert ball

The energy midpoint displacement and the Dirichlet displacement from that
midpoint are assembled before every positive index, with native analyticity
and a joint linear norm bound. These are inputs for the rough Abelian map.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV NLS.ComplexAnalysis

private theorem zero_real : IsRealPeriodOneHminusOne 0 := by intro j; simp

theorem exists_hillHminus_native_divisor_packet :
    ∃ η C : ℝ, ∃ T A K S : PeriodOneHminusOne → Coeff 2,
      0 < η ∧ 0 < C ∧
      AnalyticOnNhd ℂ T (ball (0 : PeriodOneHminusOne) η) ∧
      AnalyticOnNhd ℂ A (ball (0 : PeriodOneHminusOne) η) ∧
      AnalyticOnNhd ℂ K (ball (0 : PeriodOneHminusOne) η) ∧
      AnalyticOnNhd ℂ S (ball (0 : PeriodOneHminusOne) η) ∧
      T 0 = 0 ∧ A 0 = 0 ∧ K 0 = 0 ∧ S 0 = 0 ∧
      ∀ q ∈ ball (0 : PeriodOneHminusOne) η,
        ‖T q‖+‖A q‖+‖K q‖+‖S q‖ ≤ C*‖q‖ ∧
        (∀ n : ℕ+, hillHminusDirichlet q
          (((Real.pi : ℂ)*(n : ℕ))^2+(n : ℂ)*(A q (n : ℤ)+T q (n : ℤ))) = 0) ∧
        (∀ hq : IsRealPeriodOneHminusOne q, ∀ n : ℕ+,
          T q (n : ℤ) = ((hillHminusGapMidpoint q hq n : ℂ)-
            ((Real.pi : ℂ)*(n : ℕ))^2)/(n : ℂ) ∧
          A q (n : ℤ) = ((hillHminusDirichletEnergy q hq n : ℂ)-
            (hillHminusGapMidpoint q hq n : ℂ))/(n : ℂ) ∧
          K q (n : ℤ) = (hillHminusDirichletLogNorming q hq n : ℂ) ∧
          S q (n : ℤ) = (Real.sinh (hillHminusDirichletLogNorming q hq n) : ℂ)) ∧
        (∀ j : ℤ, j ≤ 0 → T q j = 0 ∧ A q j = 0 ∧ K q j = 0 ∧ S q j = 0) ∧
        ∀ j : ℤ, S q j = sinh (K q j) := by
  obtain ⟨V,T,hV,h0V,hTa,hTreal,hTnonpos⟩ :=
    exists_hillHminus_native_gap_midpoint_sequence 0 zero_real
  have hT0 : T 0 = 0 := by
    ext j
    change T 0 j = 0
    by_cases hj : 0 < j
    · let n : ℕ+ := ⟨j.toNat,by omega⟩
      have he : j = (n : ℤ) := by
        change j = (j.toNat : ℤ)
        exact (Int.toNat_of_nonneg hj.le).symm
      rw [he,hTreal 0 h0V zero_real n,hillHminusGapMidpoint_zero_potential]
      have hf : (freeHillValue (n : ℕ) : ℂ) = ((Real.pi : ℂ)*(n : ℕ))^2 := by
        simp only [freeHillValue,ofReal_mul,ofReal_pow,Int.cast_natCast,ofReal_natCast]
        ring
      rw [hf,sub_self,zero_div]
    · exact hTnonpos 0 j (not_lt.mp hj)
  obtain ⟨rT,CT,hrT,hCT,hTr,hTb⟩ := exists_analytic_zero_linear_bound T (hTa 0 h0V) hT0
  obtain ⟨rD,CD,D,K,S,hrD,hCD,hDa,hKa,hSa,hD0,hK0,hS0,hall⟩ :=
    exists_hillHminus_native_dirichlet_packet
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0V)
  let η := min r (min rT rD)
  have hη : 0 < η := lt_min hr (lt_min hrT hrD)
  have hηT : η ≤ rT := (min_le_right _ _).trans (min_le_left _ _)
  have hηD : η ≤ rD := (min_le_right _ _).trans (min_le_right _ _)
  have hsubV (q : PeriodOneHminusOne) (hq : q ∈ ball 0 η) : q ∈ V :=
    hball (ball_subset_ball (min_le_left _ _) hq)
  let A : PeriodOneHminusOne → Coeff 2 := fun q => D q-T q
  refine ⟨η,CD+2*CT,T,A,K,S,hη,by positivity,
    hTr.mono (ball_subset_ball hηT),?_,hKa.mono (ball_subset_ball hηD),
    hSa.mono (ball_subset_ball hηD),hT0,?_,hK0,hS0,?_⟩
  · exact (hDa.mono (ball_subset_ball hηD)).sub (hTr.mono (ball_subset_ball hηT))
  · simp only [A,hD0,hT0,sub_self]
  · intro q hq
    obtain ⟨hb,hroot,hreal,hnonpos,hsinh⟩ := hall q (ball_subset_ball hηD hq)
    have ht := hTb q (ball_subset_ball hηT hq)
    refine ⟨?_,?_,?_,?_,hsinh⟩
    · have ha : ‖A q‖ ≤ ‖D q‖+‖T q‖ := norm_sub_le _ _
      nlinarith
    · intro n
      simpa only [A,lp.coeFn_sub,Pi.sub_apply,sub_add_cancel] using hroot n
    · intro hqr n
      obtain ⟨hd,hk,hs⟩ := hreal hqr n
      have htval := hTreal q (hsubV q hq) hqr n
      refine ⟨htval,?_,hk,hs⟩
      change D q (n : ℤ)-T q (n : ℤ) = _
      rw [hd,htval]
      ring
    · intro j hj
      obtain ⟨hd,hk,hs⟩ := hnonpos j hj
      refine ⟨hTnonpos q j hj,?_,hk,hs⟩
      change D q j-T q j = 0
      rw [hd,hTnonpos q j hj,sub_self]

end NLS.Articles.KdVKdV2Frequencies
