import NLS.KdV.HillHminusCutContourTransfer
import NLS.KdV.HillHminusPhysicalPrimitivePullback
import NLS.KdV.HillHminusFixedPhysicalNumerators
import NLS.KdV.HillPhysicalIntrinsicFrequencyMoments
import NLS.KdV.MiuraAbelianMomentPair
import NLS.SequenceSpaces.SignedWeightedMomentPairs

/-! # Exact shifted-Miura pullback of the physical second moment

All contours have positive orientation. The quadratic Jacobian pairs
the opposite-frequency numerators with no additional scalar factor.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart

theorem physical_secondMoment_eq_miura_pair (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val ∈ P.source)
    (hreal : ∀ a ∈ P.miura.domain, IsRealPeriodOneHminusOne a → ∀ j : ℤ,
      P.miura.lift a (-j) = conj (P.miura.lift a j))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift) ≠ 0)
    (c : ℝ) (hshift : P.miura.energyShift = (c : ℂ)^2)
    {W : Set (CoeffPair 2)}
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W P.family.roots)
    (n k : ℕ+) :
    hillPhysicalFrequencyMoment q.val q.property.1 q.property.2 n n.pos k 2 =
      A.moment (n : ℤ) (k : ℤ) 2 (hillMiuraDiagonal (P.miura.lift (hillOriginalHminusSource q.val))) -
        A.moment (n : ℤ) (-(k : ℤ)) 2 (hillMiuraDiagonal (P.miura.lift (hillOriginalHminusSource q.val))) := by
  let a := hillOriginalHminusSource q.val
  let u : PeriodOneRealL2 := ⟨P.miura.lift a,hreal a hq.1 (hillOriginalHminusSource_real q.val q.property.2)⟩
  let φ := hillMiuraRealSource u
  obtain ⟨D⟩ := P.nonempty_periodCircle a hq k
  have hpos := miuraPeriodCircle_left_pos u k D
  let Γ := quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center : ℂ) D.radius) P.miura.energyShift
  let H (E : ℂ) := (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q.val) E + I*(Real.pi : ℂ)*(k : ℂ))^2
  let F (E : ℂ) := H E * hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n n.pos E
  have hF : AnalyticOnNhd ℂ F (hillL2RealCutDomain q.val q.property.1 q.property.2) :=
    (((analyticOnNhd_hillL2RealCutPrimitive q.val q.property.1 q.property.2).add
      analyticOnNhd_const).pow 2).mul
        ((analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q.val q.property.1 q.property.2 n n.pos).mono (subset_univ _))
  have hroot := P.energy_contour_inside_rootDomain k a hq D hpos
  have hcut := P.energy_contour_inside_original_cut q hq hreal houtside c hshift k D
  have he : Γ.integral (fun E => H E * P.differential n (E,a)) =
      Γ.integral (fun E => F E / hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E) := by
    apply Γ.integral_congr
      (D := {E : ℂ | (E,a) ∈ P.rootDomain} ∩ hillL2RealCutDomain q.val q.property.1 q.property.2)
      (fun i t => ⟨hroot i t,hcut i t⟩)
    intro E hE
    dsimp only [a]
    rw [P.differential_eq_original_normalized q hq hreal houtside c hshift n E hE.1 hE.2]
    dsimp only [F]
    ring
  have hΓ : (PiecewiseC1Loop.circle (D.center : ℂ) D.radius).Inside {z : ℂ | 0 < z.re} := by
    intro i t
    exact hpos.trans_le (re_bounds_of_mem_realCenteredClosedBall
      (sphere_subset_closedBall (circleMap_mem_sphere _ D.radius_pos.le _))).1
  have hpull := integral_quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center : ℂ) D.radius)
    P.miura.energyShift (fun E => H E * P.differential n (E,a))
    (fun z => H (z^2-P.miura.energyShift) * (2*z*P.numerator n (z^2-P.miura.energyShift,a)) /
      sourceCanonicalRoot (by simp) (by norm_num) φ.val z)
    {z : ℂ | 0 < z.re} hΓ (by
      intro z hz
      change (H _ * (P.numerator n _ / hillHminusMiuraRoot u.val P.miura.energyShift _)) * (2*z) = _
      rw [hillHminusMiuraRoot_at_squared_energy _ _ _ hz]
      dsimp only [φ,hillMiuraRealSource]
      ring)
  rw [PiecewiseC1Loop.integral_circle] at hpull
  have hφ : φ.val ∈ A.sourceBall φ := mem_ball_self (A.localChart φ).radius_pos
  obtain ⟨B⟩ := (A.localChart φ).charts φ.val hφ
  have hpair := miura_secondMoment_pair_eq_circle u A (n : ℤ) (k : ℤ) D
  have hcircle :
      (∮ z in C((D.center : ℂ),D.radius), H (z^2-P.miura.energyShift) *
        (2*z*P.numerator n (z^2-P.miura.energyShift,a)) /
          sourceCanonicalRoot (by simp) (by norm_num) φ.val z) =
        A.moment (n : ℤ) (k : ℤ) 2 φ.val - A.moment (n : ℤ) (-(k : ℤ)) 2 φ.val := by
    rw [hpair]
    apply circleIntegral_eq_of_eq_on_nonreal _ _ D.center D.radius D.radius_pos
    intro z hz hi
    have hzr : 0 < z.re := hpos.trans_le
      (re_bounds_of_mem_realCenteredClosedBall (sphere_subset_closedBall hz)).1
    have hprim := P.full_primitive_squared_frequency q hq u.property c hshift B (k : ℤ) z hzr hi
    have hnum := P.family.numerator_frequency_identity n u.val z
    have hnumeq : 2*z*P.numerator n (z^2-P.miura.energyShift,a) =
        sourcePsiCandidate (n : ℤ) (z,(P.family.roots (n : ℤ) φ.val : Coeff 2)) -
          sourcePsiCandidate (n : ℤ) (-z,(P.family.roots (n : ℤ) φ.val : Coeff 2)) := by
      simpa only [numerator,sub_add_cancel] using! hnum
    rw [hnumeq]
    dsimp only [H,φ,hillMiuraRealSource,u,a]
    rw [hprim]
    simp only [Int.cast_natCast]
  have htransfer := P.energy_contour_integral_eq_intrinsic_circle_of_cut_analytic
    q hq hreal houtside c hshift k D F hF
  rw [hillPhysicalFrequencyMoment_eq_intrinsic q.val q.property.1 q.property.2 n n.pos k k.pos 2]
  calc
    _ = Γ.integral (fun E => F E / hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E) := by
      rw [htransfer]
      unfold hillIntrinsicFrequencyMoment frequencyMoment hillL2ShiftedPrimitive
      apply circleIntegral.integral_congr
        (add_nonneg (hillRealGapContour_geometry q.val q.property.1 q.property.2 k k.pos).1
          (hillRealGapContour_geometry q.val q.property.1 q.property.2 k k.pos).2.1.le)
      intro E _hE
      dsimp only [F,H]
      ring
    _ = Γ.integral (fun E => H E * P.differential n (E,a)) := he.symm
    _ = _ := hpull.trans hcircle

end NLS.KdV.HillHminusPsiChart
