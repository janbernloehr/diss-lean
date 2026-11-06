import NLS.KdV.HillHminusIntrinsicPeriods
import NLS.KdV.HillFixedPhysicalAction
import NLS.ZakharovShabat.SourceHigherActionRegularity
import NLS.ZakharovShabat.SourceCriticalRootPeriodZero

/-! # The original Hill action is twice the first weighted Dirac action

The actual Miura energy contour has the original Hill sheet and index.
Its quadratic pullback retains the Jacobian and removes the energy
translation by the proved zero period, including at every closed gap.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart
variable (P : HillHminusPsiChart) (q : RealPeriodOneHillPotential)
    (hq : hillOriginalHminusSource q.val ∈ P.source)
    (hreal : ∀ a ∈ P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k) = conj (P.miura.lift a k))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift) ≠ 0)
    (c : ℝ) (hshift : P.miura.energyShift = (c : ℂ)^2)
include hq hreal houtside hshift

theorem miura_contour_action_eq_original (n : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (P.miura.lift (hillOriginalHminusSource q.val))) (n : ℤ)) :
    hillHminusMiuraContourAction (hillOriginalHminusSource q.val)
      (P.miura.lift (hillOriginalHminusSource q.val)) P.miura.energyShift
      (quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center : ℂ) D.radius) P.miura.energyShift) =
        (hillRealGapIntegral q.val q.property.1 q.property.2 (n : ℕ) 0 : ℂ) := by
  let a := hillOriginalHminusSource q.val
  let Γ := quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center : ℂ) D.radius) P.miura.energyShift
  let u : PeriodOneRealL2 := ⟨P.miura.lift a,hreal a hq.1 (hillOriginalHminusSource_real q.val q.property.2)⟩
  have hroot := P.energy_contour_inside_rootDomain n a hq D (miuraPeriodCircle_left_pos u n D)
  have hcut := P.energy_contour_inside_original_cut q hq hreal houtside c hshift n D
  have hshift' : P.miura.energyShift = ((c^2 : ℝ) : ℂ) := by simpa only [ofReal_pow] using hshift
  have htrace : hillHminusDiscriminant a = hillL2Discriminant (SpectralWeight.one.toCoeff q.val) :=
    funext (hillHminusDiscriminant_original_source_agreement q.val q.property.1)
  have he : Γ.integral (fun E => E*deriv (hillHminusDiscriminant a) E/
      hillHminusMiuraRoot (P.miura.lift a) P.miura.energyShift E) =
      Γ.integral (fun E => E*deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q.val)) E/
        hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E) := by
    apply Γ.integral_congr
      (D := {E : ℂ | (E,a) ∈ P.rootDomain} ∩ hillL2RealCutDomain q.val q.property.1 q.property.2)
      (fun i t => ⟨hroot i t,hcut i t⟩)
    intro E hE
    dsimp only
    rw [← show P.root (E,a) = hillHminusMiuraRoot (P.miura.lift a) P.miura.energyShift E from rfl,
      P.root_eq_original q u.property (c^2) hshift' E hE.1 hE.2,htrace]
  have hF : AnalyticOnNhd ℂ
      (fun E => E*deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q.val)) E) univ :=
    analyticOnNhd_id.mul (analyticOnNhd_hillL2Discriminant _).deriv
  have hi := P.energy_contour_integral_eq_intrinsic_circle q hq hreal houtside c hshift n D _ hF
  change (1/(Real.pi : ℂ))*Γ.integral _ = _
  rw [he,hi,one_div]
  obtain ⟨hd,hη,hleft,hright⟩ := hillRealGapContour_geometry q.val q.property.1 q.property.2 (n : ℕ) n.property
  obtain ⟨hl,hr⟩ := hillIntrinsicCircle_endpoints_in_bands q n
  exact hillFixedContourAction_eq_gapIntegral q.val q.property.1 q.property.2 (n : ℕ) n.property
    _ _ (add_nonneg hd hη.le) ⟨hl.1,hr.2⟩
    (hillRealGapSegment_subset_intrinsic_contour_ball q.val q.property.1 q.property.2 (n : ℕ) n.property)

theorem original_action_eq_twice_weighted_Dirac (n : ℕ+) :
    (hillRealGapIntegral q.val q.property.1 q.property.2 (n : ℕ) 0 : ℂ) =
      2*sourceComplexHigherAction (by norm_num) (by norm_num) (n : ℤ) 1
        (hillMiuraDiagonal (P.miura.lift (hillOriginalHminusSource q.val))) := by
  let a := hillOriginalHminusSource q.val
  let ψ := hillMiuraDiagonal (P.miura.lift a)
  let u : PeriodOneRealL2 := ⟨P.miura.lift a,hreal a hq.1 (hillOriginalHminusSource_real q.val q.property.2)⟩
  have hψ : IsRealType (CoeffPair.toMax 2 ψ) := (hillMiuraRealSource u).property
  obtain ⟨D⟩ := P.nonempty_periodCircle a hq n
  have hpos := miuraPeriodCircle_left_pos u n D
  have hΓ : (PiecewiseC1Loop.circle (D.center : ℂ) D.radius).Inside {z : ℂ | 0 < z.re} := by
    intro i t
    exact hpos.trans_le (re_bounds_of_mem_realCenteredClosedBall
      (sphere_subset_closedBall (circleMap_mem_sphere _ D.radius_pos.le _))).1
  have hpull := hillHminusMiuraContourAction_quadratic_pullback a (P.miura.lift a)
    P.miura.energyShift (P.miura.image a hq.1) _ hΓ
  rw [P.miura_contour_action_eq_original q hq hreal houtside c hshift n D,
    PiecewiseC1Loop.integral_circle] at hpull
  obtain ⟨V,_,_,hrealV,H⟩ := sourceLemma10_11CirclePeriods (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num)
  have hzero := H.zero ψ (hrealV hψ) (n : ℤ) D
  have hf : ContinuousOn (fun z => sourceCriticalRootRatioJoint (by norm_num) (by norm_num) (z,ψ))
      (sphere (D.center : ℂ) D.radius) := by
    intro z hz
    exact (sourceCriticalRootRatio_analyticOnNhd (by norm_num) (by norm_num) ψ z
      (D.sphere_subset_rootDomain hz)).continuousAt.continuousWithinAt
  have h₀ := hf.circleIntegrable D.radius_pos.le
  have h₂ := ((continuousOn_id.pow 2).mul hf).circleIntegrable D.radius_pos.le
  change CircleIntegrable (fun z : ℂ => z^2*sourceCriticalRootRatioJoint
    (by norm_num) (by norm_num) (z,ψ)) (D.center : ℂ) D.radius at h₂
  have hshiftint : CircleIntegrable (fun z => P.miura.energyShift*
      sourceCriticalRootRatioJoint (by norm_num) (by norm_num) (z,ψ)) (D.center : ℂ) D.radius := by
    have hs := h₀.const_smul (a := P.miura.energyShift)
    change CircleIntegrable (fun z => P.miura.energyShift •
      sourceCriticalRootRatioJoint (by norm_num) (by norm_num) (z,ψ)) (D.center : ℂ) D.radius at hs
    simpa only [smul_eq_mul] using hs
  have he : (∮ z in C((D.center : ℂ),D.radius),
      (z^2-P.miura.energyShift)*sourceCriticalRootRatioJoint (by norm_num) (by norm_num) (z,ψ)) =
      ∮ z in C((D.center : ℂ),D.radius), z^2*sourceCriticalRootRatioJoint (by norm_num) (by norm_num) (z,ψ) := by
    simp_rw [sub_mul]
    rw [circleIntegral.integral_sub h₂ hshiftint,
      circleIntegral.integral_const_mul,hzero,mul_zero,sub_zero]
  have haction := sourceHigherActionCircle_eq_real_of_realCentered_enclosingCircle
    (by norm_num) (by norm_num) (⟨ψ,hψ⟩ : realTypeSourceSubmodule 2) (n : ℤ) 1
    (D.center : ℂ) D.radius (ofReal_im _) D.radius_pos D.gap D.closedBall_subset_omittedDomain
  have hactual : sourceHigherActionCircle (by norm_num) (by norm_num) ψ (D.center : ℂ) D.radius 1 =
      sourceComplexHigherAction (by norm_num) (by norm_num) (n : ℤ) 1 ψ :=
    haction.trans (sourceComplexHigherAction_eq_real (by norm_num) (by norm_num) ⟨ψ,hψ⟩ (n : ℤ) 1).symm
  rw [he] at hpull
  rw [← hactual]
  rw [hpull]
  unfold sourceHigherActionCircle
  norm_num only [Nat.cast_one]
  ring

end NLS.KdV.HillHminusPsiChart
