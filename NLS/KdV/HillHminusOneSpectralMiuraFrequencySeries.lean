import NLS.KdV.HillHminusOneMiuraFrequencySeries
import NLS.KdV.HillHminusOneIsospectralSheets

/-! # Actual analytic correction series are spectral invariants near zero

One real-preserving actual Miura chart and normalized NLS family retain the
analytic moments, exact periods, odd cancellations and convergent second-moment
series. On the same common rough ball, equal intrinsic discriminants at real
inputs give equal moments of every order and equal corrections. This is the
spectral-invariance ingredient of action descent, prior to a physical action
coordinate realization and Hamiltonian-frequency identification.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

/-- A single actual family retains the full analytic moment/series construction
and spectral invariance, with its real-type chart and fixed real shift explicit.
All witnesses and the complex input ball precede both real inputs and all indices. -/
theorem exists_hillHminus_analytic_spectral_miura_frequency_series :
    ∃ C : HillHminusMiuraChart, ∃ δ : ℝ, ∃ W₀ W : Set (CoeffPair 2),
      ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
        0 < δ ∧ ball (0 : PeriodOneHminusOne) δ ⊆ C.domain ∧
        0 < C.energyShift.re ∧ C.energyShift.im = 0 ∧
        (∀ q ∈ C.domain, periodOneHminusConjugation q = q →
          IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) ∧
        SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s ∧
        (∀ q ∈ ball (0 : PeriodOneHminusOne) δ, C.criticalSource q ∈ W) ∧
        (∀ n : ℤ, AnalyticOnNhd ℂ (hillHminusMiuraEnergyPsi C s n)
          (univ ×ˢ ball (0 : PeriodOneHminusOne) δ)) ∧
        (∀ n k : ℕ+, ∀ m : ℕ, AnalyticOnNhd ℂ (hillHminusMiuraMoment C s n k m)
          (ball (0 : PeriodOneHminusOne) δ)) ∧
        (∀ q ∈ ball (0 : PeriodOneHminusOne) δ, ∀ n k : ℕ+,
          (2*(Real.pi : ℂ))⁻¹*hillHminusMiuraMoment C s n k 0 q = (if n = k then 1 else 0)) ∧
        (∀ q ∈ ball (0 : PeriodOneHminusOne) δ, ∀ n k : ℕ+, ∀ l : ℕ,
          hillHminusMiuraMoment C s n k (2*l+1) q = 0) ∧
        (∀ n : ℕ+, (∀ q ∈ ball (0 : PeriodOneHminusOne) δ,
          Summable (fun k : ℕ+ => ‖(k : ℂ)*hillHminusMiuraMoment C s n k 2 q‖)) ∧
          AnalyticOnNhd ℂ (hillHminusMiuraMomentFrequencyCorrection C s n) (ball (0 : PeriodOneHminusOne) δ) ∧
          TendstoLocallyUniformlyOn
            (fun (L : ℕ) q => ∑ j ∈ Finset.Icc (1 : ℤ) L, hillHminusMiuraSecondMomentSeriesTerm C s n q j)
            (fun q => ∑' k : ℕ+, (k : ℂ)*hillHminusMiuraMoment C s n k 2 q)
            atTop (ball (0 : PeriodOneHminusOne) δ)) ∧
        ∀ q ∈ ball (0 : PeriodOneHminusOne) δ, ∀ p ∈ ball (0 : PeriodOneHminusOne) δ,
          periodOneHminusConjugation q = q → periodOneHminusConjugation p = p →
          hillHminusDiscriminant p = hillHminusDiscriminant q → ∀ n : ℕ+,
          (∀ k : ℕ+, ∀ m : ℕ, hillHminusMiuraMoment C s n k m p = hillHminusMiuraMoment C s n k m q) ∧
          hillHminusMiuraMomentFrequencyCorrection C s n p = hillHminusMiuraMomentFrequencyCorrection C s n q := by
  obtain ⟨Dold,N,M,V,U,T,R,S,Q,r,B,hN,hM,hV,h0V,hUV,hU,h0U,D,Hcut,hseries⟩ :=
    exists_hillHminus_analytic_normalized_frequency_series
  obtain ⟨A,Dr⟩ := D.source_data
  obtain ⟨C,δP,W₀,W,s,hδP,hPV,hPC,hpos,hc,hr,H,hWP,hpsiP,hperiod⟩ :=
    exists_hillHminus_actual_original_periods Dold Dr.toHillHminusAllContourPeriodData
  obtain ⟨δR,hδR,_,hrepr⟩ := hillHminus_period_data_actual_numerator_representation C Dold
    Dr.toHillHminusAllContourPeriodData (hPC (mem_ball_self hδP)) hc hr
  let δ₀ := min δP δR
  have hδ₀ : 0 < δ₀ := lt_min hδP hδR
  have hP : ball (0 : PeriodOneHminusOne) δ₀ ⊆ ball 0 δP := ball_subset_ball (min_le_left _ _)
  have hR : ball (0 : PeriodOneHminusOne) δ₀ ⊆ ball 0 δR := ball_subset_ball (min_le_right _ _)
  have hδV := hP.trans hPV
  have hδC := hP.trans hPC
  have hW : ∀ q ∈ ball (0 : PeriodOneHminusOne) δ₀, C.criticalSource q ∈ W := fun q hq => hWP q (hP hq)
  have hpsi (n : ℤ) : AnalyticOnNhd ℂ (hillHminusMiuraEnergyPsi C s n)
      (univ ×ˢ ball (0 : PeriodOneHminusOne) δ₀) := (hpsiP n).mono (fun t ht => ⟨ht.1,hP ht.2⟩)
  have hreal (q : PeriodOneHminusOne) (hq : q ∈ ball (0 : PeriodOneHminusOne) δ₀)
      (hqr : periodOneHminusConjugation q = q) (n : ℕ+) (energy : ℂ) :
      hillHminusMiuraEnergyPsi C s (n : ℤ) (energy,q) = hillHminusNormalizedNumerator Dold N R n (energy,q) := by
    obtain ⟨hqC,hrep⟩ := hrepr q (hR hq)
    let a := hillHminusMiuraEnergyResidueHilbert C s (n : ℤ) q (hr q hqC hqr)
    have hF : ∀ e : ℂ, hillHminusMiuraEnergyPsi C s (n : ℤ) (e,q) =
        Coeff.dualPairing a (hillHminusNumeratorHilbert Dold N (e,q)) := hrep hqr s (n : ℤ)
    have ha := hillHminus_inverse_column_of_actual_periods Dold Dr q (hδV hq) (T q) (R q)
      (fun m j => (D.entries q (hδV hq) m j).1) (D.inverses q (hδV hq)).2.1 a
      (hillHminusMiuraEnergyResidueHilbert_apply_nonpos C s (n : ℤ) q (hr q hqC hqr))
      n _ hF (hperiod q (hP hq) hqr n)
    rw [hF,ha]
    rfl
  have hmatch (q : PeriodOneHminusOne) (hq : q ∈ ball (0 : PeriodOneHminusOne) δ₀)
      (n : ℕ+) (energy : ℂ) :
      hillHminusMiuraEnergyPsi C s (n : ℤ) (energy,q) = hillHminusNormalizedNumerator Dold N R n (energy,q) := by
    apply (periodOneHminus_real_form_identity isOpen_ball isPreconnected_ball (mem_ball_self hδ₀)
      (fun p => hillHminusMiuraEnergyPsi C s (n : ℤ) (energy,p))
      (fun p => hillHminusNormalizedNumerator Dold N R n (energy,p)) ?_ ?_ (fun p hp hpr => hreal p hp hpr n energy)) hq
    · intro p hp
      exact ((hpsi (n : ℤ)) (energy,p) ⟨mem_univ _,hp⟩).comp
        (f := fun p : PeriodOneHminusOne => (energy,p)) (analyticAt_const.prod analyticAt_id)
    · intro p hp
      exact ((D.numerator_analytic n) (energy,p) ⟨mem_univ _,hδV hp⟩).comp
        (f := fun p : PeriodOneHminusOne => (energy,p)) (analyticAt_const.prod analyticAt_id)
  obtain ⟨δS,hδS,_,hsheets⟩ := exists_hillHminus_isospectral_continued_sheets Dold Dr.toHillHminusAllContourPeriodData
  obtain ⟨δ,hδ,hballAll⟩ := Metric.isOpen_iff.mp ((hU.inter isOpen_ball).inter isOpen_ball) 0
    ⟨⟨h0U,mem_ball_self hδ₀⟩,mem_ball_self hδS⟩
  have hball {q : PeriodOneHminusOne} (hq : q ∈ ball (0 : PeriodOneHminusOne) δ) :
      q ∈ U ∩ ball (0 : PeriodOneHminusOne) δ₀ := (hballAll hq).1
  have hsub : ball (0 : PeriodOneHminusOne) δ ⊆ ball 0 δ₀ := fun q hq => (hball hq).2
  refine ⟨C,δ,W₀,W,s,hδ,hsub.trans hδC,hpos,hc,hr,H,fun q hq => hW q (hsub hq),
    fun n => (hpsi n).mono (fun t ht => ⟨ht.1,hsub ht.2⟩),?_,?_,?_,?_,?_⟩
  · intro n k m q hq
    have heq : hillHminusMiuraMoment C s n k m =ᶠ[𝓝 q] hillHminusNormalizedMoment Dold N R n k m := by
      filter_upwards [isOpen_ball.mem_nhds hq] with p hp
      exact hillHminusMiuraMoment_eq_normalized C Dold N R s p (hmatch p (hsub hp)) n k m
    exact (D.moment_analytic n k m q (hUV (hball hq).1)).congr heq.symm
  · intro q hq n k
    rw [hillHminusMiuraMoment_eq_normalized C Dold N R s q (hmatch q (hsub hq))]
    exact D.moment_zero q (hUV (hball hq).1) n k
  · intro q hq n k l
    rw [hillHminusMiuraMoment_eq_normalized C Dold N R s q (hmatch q (hsub hq))]
    exact D.moment_odd q (hUV (hball hq).1) n k l
  · intro n
    refine ⟨?_,?_,?_⟩
    · intro q hq
      have heq : (fun k : ℕ+ => ‖(k : ℂ)*hillHminusMiuraMoment C s n k 2 q‖) =
          (fun k : ℕ+ => ‖(k : ℂ)*hillHminusNormalizedMoment Dold N R n k 2 q‖) := by
        funext k
        rw [hillHminusMiuraMoment_eq_normalized C Dold N R s q (hmatch q (hsub hq))]
      rw [heq]
      exact (hseries n).1 q (hball hq).1
    · intro q hq
      have heq : hillHminusMiuraMomentFrequencyCorrection C s n =ᶠ[𝓝 q] hillHminusMomentFrequencyCorrection Dold N R n := by
        filter_upwards [isOpen_ball.mem_nhds hq] with p hp
        exact hillHminusMiuraMomentFrequencyCorrection_eq_normalized C Dold N R s p (hmatch p (hsub hp)) n
      exact ((hseries n).2.1 q (hball hq).1).congr heq.symm

    · have hl := ((hseries n).2.2.mono (fun q hq => (hball hq).1)).congr
          (G := fun (L : ℕ) q => ∑ j ∈ Finset.Icc (1 : ℤ) L, hillHminusMiuraSecondMomentSeriesTerm C s n q j)
          (fun L q hq => by
            apply Finset.sum_congr rfl
            intro j _
            exact (hillHminusMiuraSecondMomentSeriesTerm_eq_normalized C Dold N R s q
              (hmatch q (hsub hq)) n j).symm)
      apply hl.congr_right
      intro q hq
      apply tsum_congr
      intro k
      rw [hillHminusMiuraMoment_eq_normalized C Dold N R s q (hmatch q (hsub hq))]
  · intro q hq p hp hqr hpr htrace n
    have hnum := hillHminusMiuraEnergyPsi_eq_of_discriminant_eq C H q p
      (hδC (hsub hq)) (hδC (hsub hp)) (hr q (hδC (hsub hq)) hqr) (hr p (hδC (hsub hp)) hpr) htrace (n : ℤ)
    have he (k : ℕ+) (m : ℕ) : hillHminusMiuraMoment C s n k m p = hillHminusMiuraMoment C s n k m q := by
      unfold hillHminusMiuraMoment
      apply circleIntegral.integral_congr (by positivity)
      intro z hz
      dsimp only
      obtain ⟨hroot,hprim⟩ := hsheets q (hballAll hq).2 p (hballAll hp).2 hqr hpr htrace k z hz
      dsimp only [hillHminusFrequencyPrimitive]
      rw [hroot,hprim,congrFun hnum (z^2)]
    refine ⟨he,?_⟩
    unfold hillHminusMiuraMomentFrequencyCorrection
    congr 1
    exact tsum_congr (fun k => congrArg (fun v : ℂ => (k : ℂ)*v) (he k 2))

end NLS.KdV
