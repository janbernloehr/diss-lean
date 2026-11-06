import NLS.KdV.HillHminusOneBoundedFrequencyPacket
import NLS.KdV.HillHminusOneSpectralMiuraFrequencySeries
import NLS.KdV.HillHminusChartPhysicalNumeratorBall
import NLS.KdV.HillHminusPhysicalMomentIdentification

/-! A bounded Banach-analytic weighted packet of the ORIGINAL physical
second-moment corrections. Exact actual Miura numerator calibration and
physical contour comparison retain the original root, primitive and Jacobian.
No physical numerator or summability agreement is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem exists_hillOriginal_bounded_analytic_frequency_packet :
    ∃ δ K : ℝ, ∃ F : PeriodOneHminusOne → NLS.Coeff ⊤,
      0<δ ∧ 0<K ∧ AnalyticOnNhd ℂ F (ball (0 : PeriodOneHminusOne) δ) ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) δ, ‖F q‖≤K ∧ ∀ j : ℤ, j≤0 → F q j=0) ∧
      ∀ q : RealPeriodOneHillPotential, hillOriginalHminusSource q.val∈ball (0 : PeriodOneHminusOne) δ →
        ∀ n : ℕ+,
          Summable (fun k : ℕ => ‖(k : ℂ)*hillIntrinsicFrequencyMoment
            q.val q.property.1 q.property.2 n n.pos k 2‖) ∧
          F (hillOriginalHminusSource q.val) (n : ℤ)=
            (-12*∑' k : ℕ, (k : ℂ)*hillIntrinsicFrequencyMoment
              q.val q.property.1 q.property.2 n n.pos k 2)/(n : ℂ) := by
  obtain ⟨Dold,N,V,U,T,R,S,Q,F,K,_hN,hU,h0U,hUV,hK,D,hF,hcoeff,hseries⟩ :=
    exists_hillHminus_bounded_analytic_frequency_packet
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
  have hrealC : ∀ q∈C.domain, IsRealPeriodOneHminusOne q →
      IsRealType (CoeffPair.toMax 2 (C.criticalSource q)) :=
    fun q hq hqr => hr q hq ((periodOneHminusConjugation_fixed_iff q).mpr hqr)
  obtain ⟨δnum,hδnum,_,hnum⟩ := C.exists_original_numerator_ball
    (hδC (mem_ball_self hδ₀)) hpos hc hrealC H
  obtain ⟨δmom,hδmom,hmom⟩ := exists_hillHminus_miura_moments_eq_original
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp
    ((hU.inter isOpen_ball).inter (isOpen_ball.inter isOpen_ball)) 0
    ⟨⟨h0U,mem_ball_self hδ₀⟩,mem_ball_self hδnum,mem_ball_self hδmom⟩
  have hsubU : ball (0 : PeriodOneHminusOne) δ⊆U := fun q hq => (hball hq).1.1
  have hsub0 : ball (0 : PeriodOneHminusOne) δ⊆ball 0 δ₀ := fun q hq => (hball hq).1.2
  have hsubnum : ball (0 : PeriodOneHminusOne) δ⊆ball 0 δnum := fun q hq => (hball hq).2.1
  have hsubmom : ball (0 : PeriodOneHminusOne) δ⊆ball 0 δmom := fun q hq => (hball hq).2.2
  refine ⟨δ,K,F,hδ,hK,hF.mono hsubU,fun q hq => ⟨(hcoeff q (hsubU hq)).1,(hcoeff q (hsubU hq)).2.1⟩,?_⟩
  intro q hq n
  have he (k : ℕ+) : hillHminusNormalizedMoment Dold N R n k 2 (hillOriginalHminusSource q.val)=
      hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n n.pos k 2 := by
    rw [←hillHminusMiuraMoment_eq_normalized C Dold N R s _ (hmatch _ (hsub0 hq)) n k 2]
    exact hmom C s q (hsubmom hq) n (hnum q (hsubnum hq) n) k 2
  have hs : Summable (fun k : ℕ+ => ‖(k : ℂ)*hillIntrinsicFrequencyMoment
      q.val q.property.1 q.property.2 n n.pos k 2‖) := by
    apply ((hseries n).1 _ (hsubU hq)).congr
    intro k
    rw [he k]
  refine ⟨summable_pnat_iff_summable_nat.mp hs,?_⟩
  rw [(hcoeff _ (hsubU hq)).2.2 n,hillHminusMomentFrequencyCorrection]
  congr 2
  calc
    _=∑' k : ℕ+, (k : ℂ)*hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n n.pos k 2 :=
      tsum_congr (fun k => by rw [he k])
    _=_ := tsum_pnat_eq_tsum_of_eq_zero
      (f := fun k : ℕ => (k : ℂ)*hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n n.pos k 2) (by simp)

end NLS.KdV
