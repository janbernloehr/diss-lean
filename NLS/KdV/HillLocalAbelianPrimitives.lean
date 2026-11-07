import NLS.KdV.HillCanonicalEnergyDifferentials
import NLS.ComplexAnalysis.ParametricConvexPrimitivePathIntegral

/-! Actual local Abelian integrals of the intrinsic normalized Hill
differentials. Energy/source boxes are chosen BEFORE ALL n. Primitives
are jointly analytic, vanish at the fixed energy center, and have the
ACTUAL differential as their energy derivative. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical unitInterval
namespace NLS.KdV.HillHminusEnergyRootBox

def abelianPrimitive (B : HillHminusEnergyRootBox) (n : ℕ+) : ℂ × PeriodOneHminusOne → ℂ :=
  parametricConvexPrimitive (hillHminusCanonicalEnergyDifferential n) B.energyCenter

theorem energy_segment_inside (B : HillHminusEnergyRootBox) (E : ℂ)
    (hE : E ∈ ball B.energyCenter B.energyRadius) (q : PeriodOneHminusOne) (hq : q ∈ B.source)
    (u : ℝ) (hu : u ∈ uIcc (0:ℝ) 1) :
    (B.energyCenter+(u:ℂ)*(E-B.energyCenter),q) ∈ B.domain := by
  have hu' : u ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hu
  have hline := (convex_ball B.energyCenter B.energyRadius).segment_subset
    (mem_ball_self B.energyRadius_pos) hE (lineMap_mem_segment ℝ B.energyCenter E hu')
  have hpoint : AffineMap.lineMap B.energyCenter E u = B.energyCenter+(u:ℂ)*(E-B.energyCenter) := by
    rw [AffineMap.lineMap_apply_module']
    simp only [Complex.real_smul]
    ring
  exact ⟨hpoint ▸ hline,hq⟩

theorem analytic_abelianPrimitive (B : HillHminusEnergyRootBox) (n : ℕ+) :
    AnalyticOnNhd ℂ (B.abelianPrimitive n) B.domain := by
  exact analyticOnNhd_parametricConvexPrimitive _ (ball B.energyCenter B.energyRadius) B.source
    B.energyCenter isOpen_ball (convex_ball _ _) isOpen_ball (mem_ball_self B.energyRadius_pos)
    ((analyticOnNhd_hillHminusCanonicalEnergyDifferential n).mono (fun _ ht => mem_iUnion.mpr ⟨B,ht⟩))

theorem abelianPrimitive_at_center (B : HillHminusEnergyRootBox) (n : ℕ+) (q : PeriodOneHminusOne) :
    B.abelianPrimitive n (B.energyCenter,q) = 0 :=
  parametricConvexPrimitive_anchor _ _ _

theorem abelianPrimitive_eq_curveIntegral (B : HillHminusEnergyRootBox) (n : ℕ+)
    (E : ℂ) (q : PeriodOneHminusOne) :
    B.abelianPrimitive n (E,q) = ∫ᶜ z in Path.segment B.energyCenter E,
      holomorphicOneForm (fun w => hillHminusCanonicalEnergyDifferential n (w,q)) z :=
  parametricConvexPrimitive_eq_curveIntegral _ _ _ _

theorem analytic_energyDifferential (B : HillHminusEnergyRootBox) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) :
    AnalyticOnNhd ℂ (fun E => hillHminusCanonicalEnergyDifferential n (E,q))
      (ball B.energyCenter B.energyRadius) := by
  intro E hE
  have hdom : (E,q) ∈ hillHminusCanonicalEnergyRootDomain := mem_iUnion.mpr ⟨B,hE,hq⟩
  exact (analyticOnNhd_hillHminusCanonicalEnergyDifferential n (E,q) hdom).comp
    (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)

theorem hasDerivAt_abelianPrimitive (B : HillHminusEnergyRootBox) (n : ℕ+)
    (E : ℂ) (q : PeriodOneHminusOne) (ht : (E,q) ∈ B.domain) :
    HasDerivAt (fun z => B.abelianPrimitive n (z,q)) (hillHminusCanonicalEnergyDifferential n (E,q)) E :=
  hasDerivAt_parametricConvexPrimitive _ _ B.source B.energyCenter isOpen_ball (convex_ball _ _)
    (mem_ball_self B.energyRadius_pos)
    ((analyticOnNhd_hillHminusCanonicalEnergyDifferential n).mono (fun _ ht => mem_iUnion.mpr ⟨B,ht⟩)) q ht.2 E ht.1

theorem curveIntegral_eq_abelianPrimitive_sub (B : HillHminusEnergyRootBox) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) {a b : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hinside : ∀ t ∈ Icc (0:ℝ) 1, γ.extend t ∈ ball B.energyCenter B.energyRadius) :
    (∫ᶜ z in γ, holomorphicOneForm (fun E => hillHminusCanonicalEnergyDifferential n (E,q)) z) =
      B.abelianPrimitive n (b,q)-B.abelianPrimitive n (a,q) := by
  exact curveIntegral_eq_parametricConvexPrimitive_sub _ _ B.source B.energyCenter isOpen_ball
    (convex_ball _ _) (mem_ball_self B.energyRadius_pos)
    ((analyticOnNhd_hillHminusCanonicalEnergyDifferential n).mono (fun _ ht => mem_iUnion.mpr ⟨B,ht⟩))
    q hq γ hγ hinside

theorem abelianPrimitive_eq_local_segment (B : HillHminusEnergyRootBox) (n : ℕ+)
    (E : ℂ) (q : PeriodOneHminusOne) (ht : (E,q) ∈ B.domain) :
    B.abelianPrimitive n (E,q) =
      parametricConvexPrimitive (B.parent.energyDifferential B.family n) B.energyCenter (E,q) := by
  unfold abelianPrimitive parametricConvexPrimitive
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp only
  rw [B.canonical_differential_eq n _ (B.energy_segment_inside E ht.1 q ht.2 u hu)]

theorem abelianPrimitive_overlap_difference (B C : HillHminusEnergyRootBox) (n : ℕ+)
    (q : PeriodOneHminusOne) (E F : ℂ) (hE : (E,q) ∈ B.domain ∩ C.domain)
    (hF : (F,q) ∈ B.domain ∩ C.domain) :
    B.abelianPrimitive n (E,q)-C.abelianPrimitive n (E,q) =
      B.abelianPrimitive n (F,q)-C.abelianPrimitive n (F,q) := by
  let U := ball B.energyCenter B.energyRadius ∩ ball C.energyCenter C.energyRadius
  have hd : ∀ z ∈ U, HasDerivAt
      (fun w => B.abelianPrimitive n (w,q)-C.abelianPrimitive n (w,q)) 0 z := by
    intro z hz
    convert (B.hasDerivAt_abelianPrimitive n z q ⟨hz.1,hE.1.2⟩).sub
      (C.hasDerivAt_abelianPrimitive n z q ⟨hz.2,hE.2.2⟩) using 1 <;> first | rfl | simp only [sub_self]
  have hnorm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hd z hz).hasDerivWithinAt)
    (fun _ _ => le_of_eq (norm_zero : ‖(0:ℂ)‖ = 0))
    ((convex_ball B.energyCenter B.energyRadius).inter (convex_ball C.energyCenter C.energyRadius))
    (show F ∈ U from ⟨hF.1.1,hF.2.1⟩) (show E ∈ U from ⟨hE.1.1,hE.2.1⟩)
  apply sub_eq_zero.mp
  exact norm_eq_zero.mp (le_antisymm (by simpa only [zero_mul] using hnorm) (norm_nonneg _))

theorem analytic_abelianPrimitive_overlap_transition (B C : HillHminusEnergyRootBox) (n : ℕ+)
    (E : ℂ) (hB : E ∈ ball B.energyCenter B.energyRadius) (hC : E ∈ ball C.energyCenter C.energyRadius) :
    AnalyticOnNhd ℂ (fun q => B.abelianPrimitive n (E,q)-C.abelianPrimitive n (E,q)) (B.source ∩ C.source) := by
  intro q hq
  exact ((B.analytic_abelianPrimitive n (E,q) ⟨hB,hq.1⟩).comp
    (f := fun y : PeriodOneHminusOne => (E,y)) (analyticAt_const.prod analyticAt_id)).sub
      ((C.analytic_abelianPrimitive n (E,q) ⟨hC,hq.2⟩).comp
        (f := fun y : PeriodOneHminusOne => (E,y)) (analyticAt_const.prod analyticAt_id))

end NLS.KdV.HillHminusEnergyRootBox
