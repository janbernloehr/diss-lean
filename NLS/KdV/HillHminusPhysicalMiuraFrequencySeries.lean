import NLS.KdV.HillHminusMiuraPhysicalNumerators
import NLS.KdV.HillHminusOneSpectralMiuraFrequencySeries

/-! A genuinely convergent rough spectral series with its numerator identified
with the ORIGINAL physical normalized numerator. The contours in its moments
are still the rough frequency circles; comparison with the intrinsic moving
physical gap contours is a separate obligation. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV

/-- One actual rough ball and root factory support the convergent analytic
second-moment series and its exact ORIGINAL physical energy numerator.
No numerator agreement, outside-shift exclusion or summability is assumed. -/
theorem exists_hillHminus_physical_numerator_miura_frequency_series :
    ∃ C : HillHminusMiuraChart, ∃ δ : ℝ, ∃ W₀ W : Set (CoeffPair 2),
      ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
        0 < δ ∧ ball (0 : PeriodOneHminusOne) δ ⊆ C.domain ∧
        SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s ∧
        (∀ q : RealPeriodOneHillPotential, hillOriginalHminusSource q.val ∈ ball 0 δ →
          ∀ n : ℕ+, ∀ E : ℂ,
            hillHminusMiuraEnergyPsi C s (n : ℤ) (E,hillOriginalHminusSource q.val) =
              hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n n.pos E) ∧
        (∀ n k : ℕ+, ∀ m : ℕ, AnalyticOnNhd ℂ (hillHminusMiuraMoment C s n k m)
          (ball (0 : PeriodOneHminusOne) δ)) ∧
        ∀ n : ℕ+, (∀ q ∈ ball (0 : PeriodOneHminusOne) δ,
          Summable (fun k : ℕ+ => ‖(k : ℂ)*hillHminusMiuraMoment C s n k 2 q‖)) ∧
          AnalyticOnNhd ℂ (hillHminusMiuraMomentFrequencyCorrection C s n)
            (ball (0 : PeriodOneHminusOne) δ) ∧
          TendstoLocallyUniformlyOn
            (fun (L : ℕ) q => ∑ j ∈ Finset.Icc (1 : ℤ) L, hillHminusMiuraSecondMomentSeriesTerm C s n q j)
            (fun q => ∑' k : ℕ+, (k : ℂ)*hillHminusMiuraMoment C s n k 2 q)
            atTop (ball (0 : PeriodOneHminusOne) δ) := by
  obtain ⟨C,δ₀,W₀,W,s,hδ₀,hC,hpos,hshiftim,hr,H,_,_,hmom,_,_,hseries,_⟩ :=
    exists_hillHminus_analytic_spectral_miura_frequency_series
  have hz : hillHminusRadicand 0 (-C.energyShift) ≠ 0 := by
    intro he
    have h0r : IsRealPeriodOneHminusOne 0 := by intro k; simp
    obtain ⟨j,hj⟩ := (hillHminusRealLabels_root_iff 0 h0r _).mp he
    have heq := congrArg Complex.re hj
    simp only [neg_re,ofReal_re,hillHminusRealLabels_zero,freeHillValue] at heq
    have hnonneg : 0 ≤ (((j+1)/2 : ℕ) : ℝ)^2*Real.pi^2 := by positivity
    nlinarith
  have hcont : Continuous (fun a => hillHminusRadicand a (-C.energyShift)) := by
    apply continuous_iff_continuousAt.mpr
    intro a
    exact ((analyticOnNhd_hillHminusRadicand_joint (-C.energyShift,a) (mem_univ _)).comp
      (f := fun b : PeriodOneHminusOne => (-C.energyShift,b))
      (analyticAt_const.prod analyticAt_id)).continuousAt
  let U : Set PeriodOneHminusOne := {a | hillHminusRadicand a (-C.energyShift) ≠ 0}
  have hU : IsOpen U := isClosed_singleton.isOpen_compl.preimage hcont
  obtain ⟨δ,hδ,hsub⟩ := Metric.isOpen_iff.mp (isOpen_ball.inter hU) 0 ⟨mem_ball_self hδ₀,hz⟩
  have hball : ball (0 : PeriodOneHminusOne) δ ⊆ ball 0 δ₀ := fun a ha => (hsub ha).1
  have hc : C.energyShift = (Real.sqrt C.energyShift.re : ℂ)^2 := by
    rw [← ofReal_pow,Real.sq_sqrt hpos.le]
    exact Complex.ext (by simp) (by simpa using hshiftim)
  have hreal : ∀ a ∈ C.domain, IsRealPeriodOneHminusOne a →
      IsRealType (CoeffPair.toMax 2 (C.criticalSource a)) := fun a ha har =>
    hr a ha ((periodOneHminusConjugation_fixed_iff a).mpr har)
  obtain ⟨B⟩ := nonempty_miuraHillPsiFamily
  let P : HillHminusPsiChart := ⟨C,B⟩
  refine ⟨C,δ,W₀,W,s,hδ,hball.trans hC,H,?_,?_,?_⟩
  · intro q hq n E
    have hqP := P.original_source_mem_of_real q (hC (hball hq))
      (hreal _ (hC (hball hq)) (hillOriginalHminusSource_real q.val q.property.2))
    exact P.miuraEnergyPsi_eq_original H q hqP hreal
      (hsub hq).2 (Real.sqrt C.energyShift.re) hc n E
  · intro n k m
    exact (hmom n k m).mono hball
  · intro n
    exact ⟨fun q hq => (hseries n).1 q (hball hq),
      (hseries n).2.1.mono hball,(hseries n).2.2.mono hball⟩

end NLS.KdV
