import NLS.KdV.HillLabelContinuity
import NLS.KdV.HillEventualActionGapBound
import NLS.KdV.HillL2RealContourMoments
import NLS.KdV.HillRealGapIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # L2 continuity and locally uniform tails of actual real Hill actions

The signed arcosh integrand admits a continuous extension in the potential
and energy. Variable-endpoint integration proves continuity at open and
collapsed gaps. The high action-gap estimate holds with one cutoff on an
open real L2 neighborhood. These are inputs to the rough quadratic trace;
the rough trace and the explicit cutoff in Theorem 3 are not asserted here.
-/

noncomputable section
open Set Complex MeasureTheory
namespace NLS.KdV

theorem continuous_hillRealGapIntegral_family
    {T : Type*} [TopologicalSpace T]
    (Q : T → WeightedCoeff SpectralWeight.one.toWeight 2) (hQ : Continuous Q)
    (hq : ∀ t, SpectralWeight.one.toCoeff (Q t) ∈ Coeff.paritySubspace 0)
    (hr : ∀ t, IsRealHillPotential (SpectralWeight.one.toCoeff (Q t)))
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    Continuous (fun t => hillRealGapIntegral (Q t) (hq t) (hr t) n m) := by
  let F : T → ℝ → ℝ := fun t x => x^m * Real.arcosh
    (max 1 (((-1 : ℝ)^n * (hillL2Discriminant (SpectralWeight.one.toCoeff (Q t)) x).re)/2))
  have hDj : Continuous (fun p : ℂ × Coeff 2 => hillL2Discriminant p.2 p.1) :=
    continuous_iff_continuousAt.mpr (fun p =>
      (analyticOnNhd_hillL2Discriminant_joint p (mem_univ p)).continuousAt)
  let E : T × ℝ → ℂ × Coeff 2 := fun p =>
    ((p.2 : ℂ), SpectralWeight.one.toCoeff (Q p.1))
  have hE1 : Continuous (fun p : T × ℝ => (p.2 : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_snd
  have hE2 : Continuous (fun p : T × ℝ => SpectralWeight.one.toCoeff (Q p.1)) :=
    (SpectralWeight.one.toCoeff.continuous.comp hQ).comp continuous_fst
  have hE : Continuous E := hE1.prodMk hE2
  have hD : Continuous (fun p : T × ℝ =>
      hillL2Discriminant (SpectralWeight.one.toCoeff (Q p.1)) p.2) := by
    simpa only [Function.comp_def, E] using hDj.comp hE
  have harg : Continuous (fun p : T × ℝ =>
      max 1 (((-1 : ℝ)^n * (hillL2Discriminant (SpectralWeight.one.toCoeff (Q p.1)) p.2).re)/2)) :=
    continuous_const.max (((Complex.continuous_re.comp hD).const_mul _).div_const _)
  have hF : Continuous F.uncurry :=
    (continuous_snd.pow m).mul (Real.continuousOn_arcosh.comp_continuous harg
      (by intro p; exact (show (1 : ℝ) ≤ max 1 _ from le_max_left _ _)))
  let a := fun t => hillRealLabels (Q t) (hq t) (hr t) (2*n-1)
  let b := fun t => hillRealLabels (Q t) (hq t) (hr t) (2*n)
  have ha : Continuous a := continuous_hillRealLabels_family Q hQ hq hr _
  have hb : Continuous b := continuous_hillRealLabels_family Q hQ hq hr _
  have hIa : Continuous (fun t => ∫ x in (0:ℝ)..a t, F t x) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF ha
  have hIb : Continuous (fun t => ∫ x in (0:ℝ)..b t, F t x) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF hb
  have hI : Continuous (fun t => ∫ x in a t..b t, F t x) := by
    have he (t : T) : (∫ x in a t..b t, F t x) =
        (∫ x in (0:ℝ)..b t, F t x) - (∫ x in (0:ℝ)..a t, F t x) := by
      have hc : Continuous (F t) := hF.uncurry_left t
      have hi := intervalIntegral.integral_add_adjacent_intervals
        (μ := volume) (a := (0 : ℝ)) (b := a t) (c := b t) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
      linarith
    simp_rw [he]
    exact hIb.sub hIa
  have he (t : T) : hillRealGapIntegral (Q t) (hq t) (hr t) n m =
      (2/Real.pi) * ∫ x in a t..b t, F t x := by
    unfold hillRealGapIntegral
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    have horder : a t ≤ b t := monotone_hillRealLabels (Q t) (hq t) (hr t) (by omega)
    rw [uIcc_of_le horder] at hx
    have hge := hillL2Discriminant_signed_gap_ge_two (Q t) (hq t) (hr t) n hn x hx
    dsimp [F, hillRealGapProfile]
    rw [max_eq_right (by linarith)]
  simp_rw [he]
  exact hI.const_mul _


theorem continuous_hillRealGapIntegral (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    Continuous (fun q : RealPeriodOneHillPotential =>
      hillRealGapIntegral q.val q.property.1 q.property.2 n m) :=
  continuous_hillRealGapIntegral_family Subtype.val continuous_subtype_val
    (fun q => q.property.1) (fun q => q.property.2) n hn m

theorem continuous_hillL2RealContourMoment_family
    {T : Type*} [TopologicalSpace T]
    (Q : T → WeightedCoeff SpectralWeight.one.toWeight 2) (hQ : Continuous Q)
    (hq : ∀ t, SpectralWeight.one.toCoeff (Q t) ∈ Coeff.paritySubspace 0)
    (hr : ∀ t, IsRealHillPotential (SpectralWeight.one.toCoeff (Q t)))
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    Continuous (fun t => hillL2RealContourMoment (Q t) (hq t) (hr t) n m) := by
  have he : (fun t => hillL2RealContourMoment (Q t) (hq t) (hr t) n m) =
      (fun t => (hillRealGapIntegral (Q t) (hq t) (hr t) n m : ℂ)) := by
    funext t
    exact hillL2RealContourMoment_eq_gapIntegral (Q t) (hq t) (hr t) n hn m
  rw [he]
  exact Complex.continuous_ofReal.comp
    (continuous_hillRealGapIntegral_family Q hQ hq hr n hn m)
theorem exists_hillRealGapIntegral_uniform_local_tail
    (q : RealPeriodOneHillPotential) :
    ∃ N : ℕ, ∃ U : Set RealPeriodOneHillPotential, 2 ≤ N ∧ IsOpen U ∧ q ∈ U ∧
      ∀ p ∈ U, ∀ n : ℕ, N ≤ n →
        (n : ℝ) * hillRealGapIntegral p.val p.property.1 p.property.2 n 0 ≤
          (hillRealLabels p.val p.property.1 p.property.2 (2*n) -
            hillRealLabels p.val p.property.1 p.property.2 (2*n-1))^2 := by
  obtain ⟨N₀, V, hV, hqV, hbound⟩ :=
    exists_hillRealGapIntegral_local_quadratic_tail_bound (SpectralWeight.one.toCoeff q.val)
  obtain ⟨A, hA⟩ := exists_nat_ge (16 * (‖q.val‖ + 1))
  let N := max 2 (max N₀ A)
  let U : Set RealPeriodOneHillPotential :=
    {p | SpectralWeight.one.toCoeff p.val ∈ V} ∩ {p | ‖p.val‖ < ‖q.val‖ + 1}
  have hC : Continuous (fun p : RealPeriodOneHillPotential => SpectralWeight.one.toCoeff p.val) :=
    SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have hU : IsOpen U :=
    (hV.preimage hC).inter (isOpen_lt continuous_subtype_val.norm continuous_const)
  refine ⟨N, U, le_max_left _ _, hU, ⟨hqV, by dsimp; linarith⟩, ?_⟩
  intro p hp n hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnN : N₀ ≤ n := (le_max_left N₀ A).trans ((le_max_right 2 _).trans hn)
  have hnA : A ≤ n := (le_max_right N₀ A).trans ((le_max_right 2 _).trans hn)
  have hpn : ‖p.val‖ < ‖q.val‖ + 1 := hp.2
  have hcut : 16 * ‖p.val‖ ≤ (n : ℝ) :=
    (mul_le_mul_of_nonneg_left hpn.le (by norm_num : (0 : ℝ) ≤ 16)).trans
      (hA.trans (by exact_mod_cast hnA))
  exact hbound p.val p.property.1 p.property.2 hp.1 n hnN hn2 hcut


end NLS.KdV
