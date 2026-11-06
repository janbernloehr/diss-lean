import NLS.KdV.HillHminusOneHilbertFrequencySeries
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-! A genuine Banach-analytic weighted ell2 packet of the actual normalized
second-moment corrections. The whole Hilbert sum is absolutely convergent
and uniformly bounded before coordinate evaluation; no inference from
individual column bounds or bounded scalar coordinates is used. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

theorem exists_hillHminus_analytic_hilbert_frequency_packet :
    ∃ C : HillHminusMiuraChart, ∃ N : ℕ, ∃ V U : Set PeriodOneHminusOne,
      ∃ T R S Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
      ∃ F : PeriodOneHminusOne → NLS.Coeff 2, ∃ K : ℝ,
        0<N ∧ IsOpen U ∧ (0 : PeriodOneHminusOne)∈U ∧ U⊆V ∧ 0<K ∧
        HillHminusTwoWeightedNormalizedMomentData C N V T R S Q ∧
        AnalyticOnNhd ℂ F U ∧
        (∀ q∈U, ‖F q‖≤K ∧ (∀ j : ℤ, j≤0 → F q j=0) ∧
          ∀ n : ℕ+, F q (n : ℤ)=hillHminusMomentFrequencyCorrection C N R n q/(n : ℂ)) ∧
        ∀ n : ℕ+,
          (∀ q∈U, Summable (fun k : ℕ+ => ‖(k : ℂ)*hillHminusNormalizedMoment C N R n k 2 q‖)) ∧
          AnalyticOnNhd ℂ (hillHminusMomentFrequencyCorrection C N R n) U := by
  obtain ⟨C,N,M,V,U₀,T,R,S,Q,r,B,hN,_,_,_,hU₀V,hU₀,h0U₀,D,H,hseries⟩ :=
    exists_hillHminus_analytic_normalized_frequency_series
  obtain ⟨A,Dr⟩ := D.source_data
  obtain ⟨W,Q1,_hWV,hW,h0W,_hQ1a,_hQ10,hQ1,hcompat⟩ :=
    Dr.exists_weighted_inverse_for_normalization T R
      (fun q hq m n => (D.entries q hq m n).1) (fun q hq => (D.inverses q hq).2.1)
  obtain ⟨L,Ug,Bg,_,hML,hUgU₀,hUg,h0Ug,hBg,hgap⟩ :=
    H.exists_frequency_gap_majorant hU₀ h0U₀ (hU₀V.trans Dr.chart_domain)
  let U := Ug∩W
  have hU : IsOpen U := hUg.inter hW
  have h0U : (0 : PeriodOneHminusOne)∈U := ⟨h0Ug,h0W⟩
  have hUU₀ : U⊆U₀ := fun _ hq => hUgU₀ hq.1
  have hUV : U⊆V := hUU₀.trans hU₀V
  let H' : HillHminusCriticalPrimitiveCutData C N L U r B :=
    ⟨H.radius_pos,H.radius_le,H.bound_pos,fun q hq k hk => H.data q (hUU₀ hq) k (hML.trans hk)⟩
  let F := hillHminusHilbertMomentFrequencyCorrection C N Q1
  let K := 12*((∑ j∈Finset.Icc (1 : ℤ) L, ‖(j : ℂ)*(320*A^3)‖)+
    (1376*Real.pi^2*B^3)*(16*Real.pi^2)*Bg)+1
  have hB := H.bound_pos
  have hK : 0<K := by dsimp only [K];positivity
  have hs (q : PeriodOneHminusOne) (hq : q∈U) :=
    Dr.summable_weightedSecondMomentVector_and_norm_bound H' hUV Q1 q hq (hQ1 q hq.2)
      (hgap q hq.1).1 (hgap q hq.1).2
  have hbound (q : PeriodOneHminusOne) (hq : q∈U) : ‖F q‖≤K :=
    (hs q hq).2.trans (by dsimp only [K];linarith)
  have hpos (q : PeriodOneHminusOne) (hq : q∈U) (n : ℕ+) :
      F q (n : ℤ)=hillHminusMomentFrequencyCorrection C N R n q/(n : ℂ) :=
    Dr.hilbertMomentFrequencyCorrection_positive R Q1 q (hUV hq) (hs q hq).1 (hcompat q hq.2) n
  have hneg (q : PeriodOneHminusOne) (hq : q∈U) (j : ℤ) (hj : j≤0) : F q j=0 :=
    hillHminusHilbertMomentFrequencyCorrection_nonpositive C N Q1 q (hs q hq).1 j hj
  have hFa : AnalyticOnNhd ℂ F U := by
    apply NLS.Coeff.analyticOnNhd_of_bounded_coordinatewise F hU ?_ K hbound
    intro j q hq
    by_cases hj : 0<j
    · let n := positiveIntegerIndex j hj
      have hnj : (n : ℤ)=j := positiveIntegerIndex_int j hj
      have he : (fun p => hillHminusMomentFrequencyCorrection C N R n p/(n : ℂ)) =ᶠ[𝓝 q]
          (fun p => F p j) := by
        filter_upwards [hU.mem_nhds hq] with p hp
        rw [←hnj,hpos p hp n]
      exact (((hseries n).2.1 q (hUU₀ hq)).div_const).congr he
    · apply (analyticAt_const (v := (0 : ℂ))).congr
      filter_upwards [hU.mem_nhds hq] with p hp
      exact (hneg p hp j (by omega)).symm
  refine ⟨C,N,V,U,T,R,S,Q,F,K,hN,hU,h0U,hUV,hK,D,hFa,
    (fun q hq => ⟨hbound q hq,hneg q hq,hpos q hq⟩),?_⟩
  intro n
  exact ⟨fun q hq => (hseries n).1 q (hUU₀ hq),(hseries n).2.1.mono hUU₀⟩

end NLS.KdV
