import NLS.KdV.HillHminusOneTwoWeightedMomentBounds
import NLS.KdV.HillHminusOneFrequencyGapMajorant
import NLS.KdV.FrequencySeries
import NLS.SequenceSpaces.AnalyticTailSummation

/-! # The actual rough analytic normalized second-moment series near zero

The genuine rough gap majorant and actual twice-weighted moment bounds
give absolute and locally uniform convergence on a single Hminus1-open
neighborhood. Physical Hamiltonian frequency identification is separate.
-/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.KdV

def hillHminusSecondMomentSeriesTerm (C : HillHminusMiuraChart) (N : ℕ)
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (n : ℕ+)
    (q : PeriodOneHminusOne) (j : ℤ) : ℂ :=
  if hj : 0 < j then (j : ℂ)*hillHminusNormalizedMoment C N R n (positiveIntegerIndex j hj) 2 q else 0

theorem hillHminusSecondMomentSeriesTerm_positive (C : HillHminusMiuraChart) (N : ℕ)
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (n k : ℕ+) (q : PeriodOneHminusOne) :
    hillHminusSecondMomentSeriesTerm C N R n q (k : ℤ) =
      (k : ℂ)*hillHminusNormalizedMoment C N R n k 2 q := by
  have hk : (0 : ℤ) < k := by exact_mod_cast k.property
  have he : positiveIntegerIndex (k : ℤ) hk = k := by
    apply Subtype.ext
    simp only [positiveIntegerIndex,Int.toNat_natCast]
    rfl
  simp only [hillHminusSecondMomentSeriesTerm,dif_pos hk,he,Int.cast_natCast]

def hillHminusMomentFrequencyCorrection (C : HillHminusMiuraChart) (N : ℕ)
    (R : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  -12*∑' k : ℕ+, (k : ℂ)*hillHminusNormalizedMoment C N R n k 2 q

/-- The actual normalized family retains all earlier weighted, analytic,
free, exact-period and odd-cancellation data. One rough neighborhood works
before every output index. The finite contour head is handled by analyticity.
This constructs the source second-moment correction candidate near zero. -/
theorem exists_hillHminus_analytic_normalized_frequency_series :
    ∃ C : HillHminusMiuraChart, ∃ N M : ℕ, ∃ V U : Set PeriodOneHminusOne,
      ∃ T R S Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2), ∃ r B : ℝ,
        0 < N ∧ 0 < M ∧ IsOpen V ∧ 0 ∈ V ∧ U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧
        HillHminusTwoWeightedNormalizedMomentData C N V T R S Q ∧
        HillHminusCriticalPrimitiveCutData C N M U r B ∧ ∀ n : ℕ+,
          (∀ q ∈ U, Summable (fun k : ℕ+ => ‖(k : ℂ)*hillHminusNormalizedMoment C N R n k 2 q‖)) ∧
          AnalyticOnNhd ℂ (hillHminusMomentFrequencyCorrection C N R n) U ∧
          TendstoLocallyUniformlyOn
            (fun (L : ℕ) q => ∑ j ∈ Finset.Icc (1 : ℤ) L, hillHminusSecondMomentSeriesTerm C N R n q j)
            (fun q => ∑' k : ℕ+, (k : ℂ)*hillHminusNormalizedMoment C N R n k 2 q) atTop U := by
  obtain ⟨C,N,Mc,V,Uc,T,R,S,Q,r,B,hN,_,hV,h0V,hUcV,hUc,h0Uc,D,H,hbounds⟩ :=
    exists_hillHminus_weighted_second_gap_bounds
  obtain ⟨A,Dr⟩ := D.source_data
  obtain ⟨M,U,Bg,hM,hMcM,hUUc,hU,h0U,_,hg⟩ :=
    H.exists_frequency_gap_majorant hUc h0Uc (hUcV.trans Dr.chart_domain)
  have hUV : U ⊆ V := hUUc.trans hUcV
  have H' : HillHminusCriticalPrimitiveCutData C N M U r B :=
    ⟨H.radius_pos,H.radius_le,H.bound_pos,fun q hq k hk => H.data q (hUUc hq) k (hMcM.trans hk)⟩
  refine ⟨C,N,M,V,U,T,R,S,Q,r,B,hN,hM,hV,h0V,hUV,hU,h0U,D,H',?_⟩
  intro n
  let f := hillHminusSecondMomentSeriesTerm C N R n
  have ha (j : ℤ) : AnalyticOnNhd ℂ (fun q => f q j) U := by
    dsimp only [f,hillHminusSecondMomentSeriesTerm]
    split_ifs with hj
    · exact analyticOnNhd_const.mul ((D.moment_analytic n (positiveIntegerIndex j hj) 2).mono hUV)
    · exact analyticOnNhd_const
  have hz (q : PeriodOneHminusOne) (_ : q ∈ U) (j : ℤ) (hj : j ≤ 0) : f q j = 0 := by
    simp only [f,hillHminusSecondMomentSeriesTerm,dif_neg (by omega : ¬0 < j)]
  let K : ℝ := (1376*Real.pi^2*B^3)*(n : ℝ)^2
  have hB : 0 < B := H.bound_pos
  have hK : 0 ≤ K := by dsimp only [K];positivity
  have htail (q : PeriodOneHminusOne) (hq : q ∈ U) (j : ℤ)
      (hj : j ∉ Finset.Icc (1 : ℤ) (M : ℤ)) :
      ‖f q j‖ ≤ (K*(16*Real.pi^2))*‖C.canonicalFrequencyGapSquares q j‖ := by
    by_cases hjpos : 0 < j
    · let k := positiveIntegerIndex j hjpos
      have hkj : (k : ℤ) = j := positiveIntegerIndex_int j hjpos
      have hkM : M ≤ (k : ℕ) := by
        simp only [Finset.mem_Icc] at hj
        have hh : (M : ℤ) < j := by omega
        have : (M : ℤ) < (k : ℤ) := by rwa [hkj]
        exact_mod_cast this.le
      obtain ⟨l,u,F,hpair,_⟩ := H'.data q hq k hkM
      have hm := (hbounds q (hUUc hq) k (hMcM.trans hkM) l u hpair).2.2.1 n
      have hx := (hg q hq).2 k hkM l u hpair
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast k.property
      change ‖hillHminusSecondMomentSeriesTerm C N R n q j‖ ≤ _
      rw [← hkj,hillHminusSecondMomentSeriesTerm_positive,norm_mul,Complex.norm_natCast]
      calc
        _ ≤ (k : ℝ)*(K*(‖l-u‖^2/(k : ℕ)^2)/(k : ℕ)^2) :=
          mul_le_mul_of_nonneg_left hm (by positivity)
        _ ≤ K*(‖l-u‖^2/(k : ℕ)^2) := by
          rw [← mul_div_assoc]
          apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℕ)^2)).mpr
          nlinarith [mul_le_mul_of_nonneg_left (show (k : ℝ) ≤ (k : ℝ)^2 by nlinarith)
            (show 0 ≤ K*(‖l-u‖^2/(k : ℕ)^2) by positivity)]
        _ ≤ K*((16*Real.pi^2)*‖C.canonicalFrequencyGapSquares q (k : ℤ)‖) :=
          mul_le_mul_of_nonneg_left hx hK
        _ = _ := by ring
    · rw [hz q hq j (by omega),norm_zero]
      positivity
  obtain ⟨hs,hsum,hlocal⟩ := NLS.Coeff.analytic_tsum_of_bounded_one_tail f hU ha
    (Finset.Icc (1 : ℤ) (M : ℤ)) C.canonicalFrequencyGapSquares Bg (K*(16*Real.pi^2))
    (by positivity) (fun q hq => (hg q hq).1) htail
  obtain ⟨hsp,hsump,hlocalp⟩ := positive_frequency_series_of_integer_series f hz hs hsum hlocal hU
  have he (q : PeriodOneHminusOne) (k : ℕ+) : f q (k : ℤ) =
      (k : ℂ)*hillHminusNormalizedMoment C N R n k 2 q :=
    hillHminusSecondMomentSeriesTerm_positive C N R n k q
  refine ⟨?_,?_,?_⟩
  · intro q hq
    simpa only [he] using hsp q hq
  · exact analyticOnNhd_const.mul (by simpa only [hillHminusMomentFrequencyCorrection,he] using hsump)
  · simpa only [he] using hlocalp

end NLS.KdV
