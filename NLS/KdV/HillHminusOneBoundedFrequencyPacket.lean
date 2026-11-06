import NLS.KdV.HillHminusOneLinearFrequencyBounds
import NLS.SequenceSpaces.PositiveBoundedAnalyticFamily

/-! The literal convergent rough normalized second-moment corrections form
ONE Banach-analytic weighted ell-infinity packet near zero. The own-index
normalization is exactly division by n. Scalar analyticity alone is not
used to infer sequence-valued analyticity: the full common norm bound is
proved from the uniform contour head and once-weighted gap tail. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

theorem exists_hillHminus_bounded_analytic_frequency_packet :
    ∃ C : HillHminusMiuraChart, ∃ N : ℕ, ∃ V U : Set PeriodOneHminusOne,
      ∃ T R S Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
      ∃ F : PeriodOneHminusOne → NLS.Coeff ⊤, ∃ K : ℝ,
        0<N ∧ IsOpen U ∧ (0 : PeriodOneHminusOne)∈U ∧ U⊆V ∧ 0<K ∧
        HillHminusTwoWeightedNormalizedMomentData C N V T R S Q ∧
        AnalyticOnNhd ℂ F U ∧
        (∀ q∈U, ‖F q‖≤K ∧ (∀ j : ℤ, j≤0 → F q j=0) ∧
          ∀ n : ℕ+, F q (n : ℤ)=hillHminusMomentFrequencyCorrection C N R n q/(n : ℂ)) ∧
        ∀ n : ℕ+,
          (∀ q∈U, Summable (fun k : ℕ+ => ‖(k : ℂ)*hillHminusNormalizedMoment C N R n k 2 q‖)) ∧
          AnalyticOnNhd ℂ (hillHminusMomentFrequencyCorrection C N R n) U := by
  obtain ⟨C,N,M,V,U₀,T,R,S,Q,r,B,hN,_,_,_,hUV,hU₀,h0U,D,H,hseries⟩ :=
    exists_hillHminus_analytic_normalized_frequency_series
  obtain ⟨A,Dr⟩ := D.source_data
  obtain ⟨L,U,Bg,_,hML,hUU₀,hU,h0,hBg,hgap⟩ :=
    H.exists_frequency_gap_majorant hU₀ h0U (hUV.trans Dr.chart_domain)
  have hUV' : U⊆V := hUU₀.trans hUV
  let H' : HillHminusCriticalPrimitiveCutData C N L U r B :=
    ⟨H.radius_pos,H.radius_le,H.bound_pos,fun q hq k hk => H.data q (hUU₀ hq) k (hML.trans hk)⟩
  let K := 12*(‖NLS.Coeff.finiteHead (p := 1) (Finset.Icc (1 : ℤ) L)
    (fun j => (j : ℂ)*(320*A^3))‖+(1376*Real.pi^2*B^3)*(16*Real.pi^2)*Bg)+1
  have hB := H.bound_pos
  have hK : 0<K := by dsimp only [K];positivity
  have hb (q : PeriodOneHminusOne) (hq : q∈U) (n : ℕ+) :
      ‖hillHminusMomentFrequencyCorrection C N R n q/(n : ℂ)‖≤K := by
    have h := D.norm_frequencyCorrection_div_index_le Dr H' hUV' q hq (hgap q hq).1 (hgap q hq).2 n
    exact h.trans (by dsimp only [K];linarith)
  obtain ⟨F,hF,hcoeff⟩ := NLS.Coeff.exists_positive_bounded_analytic_lift U hU
    (fun n q => hillHminusMomentFrequencyCorrection C N R n q/(n : ℂ)) K hK.le
    (fun n q hq => ((hseries n).2.1 q (hUU₀ hq)).div_const) hb
  refine ⟨C,N,V,U,T,R,S,Q,F,K,hN,hU,h0,hUV',hK,D,hF,hcoeff,?_⟩
  intro n
  exact ⟨fun q hq => (hseries n).1 q (hUU₀ hq),(hseries n).2.1.mono hUU₀⟩

end NLS.KdV
