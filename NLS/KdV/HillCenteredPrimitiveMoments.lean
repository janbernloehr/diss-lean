import NLS.KdV.HillAbelianJointFrequencyDomain
import NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-! Actual centered primitive moments for the ORIGINAL rough Hill problem.
The contour is the positive-frequency pullback of the original energy loop;
its normalized differential retains the exact two-z Jacobian. One complex
source neighborhood supports ALL rows, selected gaps and even moment orders. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch
variable {W : Set (CoeffPair 2)}

def momentSource (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W) : Set PeriodOneHminusOne :=
  {q | q ∈ P.source ∧ P.sourcePsi q ∈ ball C.discs.source.val C.discs.sourceRadius}

theorem momentSource_open (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W) : IsOpen (P.momentSource C) :=
  P.analytic_sourcePsi.continuousOn.isOpen_inter_preimage P.source_open isOpen_ball

def momentJointDomain (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W) : Set (ℂ × PeriodOneHminusOne) :=
  P.abelianJointFrequencyDomain ∩ Prod.snd ⁻¹' P.momentSource C

theorem momentJointDomain_open (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W) : IsOpen (P.momentJointDomain C) :=
  P.abelianJointFrequencyDomain_open.inter ((P.momentSource_open C).preimage continuous_snd)

def centeredMomentIntegrand (P : HillProductEquationPatch) (W : Set (CoeffPair 2))
    (n m : ℕ+) (d : ℕ) (t : ℂ × PeriodOneHminusOne) : ℂ :=
  (sourceFullAbelianPrimitive (by simp) (by norm_num) W (m:ℤ) (t.1,P.sourcePsi t.2))^(2*d)*
    P.abelianFrequencyDifferential n t

def centeredMoment (P : HillProductEquationPatch) (W : Set (CoeffPair 2))
    (n m : ℕ+) (d : ℕ) (q : PeriodOneHminusOne) : ℂ :=
  ∮ z in C((P.centers (m:ℤ):ℂ),P.radii (m:ℤ)), P.centeredMomentIntegrand W n m d (z,q)

theorem analytic_centeredMomentIntegrand (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n m : ℕ+) (d : ℕ) :
    AnalyticOnNhd ℂ (P.centeredMomentIntegrand W n m d) (P.momentJointDomain C) := by
  intro t ht
  have hF := (C.full_analytic (m:ℤ) (t.1,P.sourcePsi t.2) ⟨ht.2.2,ht.1.2⟩).comp
    (f := fun x : ℂ × PeriodOneHminusOne => (x.1,P.sourcePsi x.2))
    (analyticAt_fst.prod ((P.analytic_sourcePsi t.2 ht.1.1).comp (f := Prod.snd) analyticAt_snd))
  exact (hF.pow (2*d)).mul (P.analytic_abelianFrequencyDifferential_joint n t ht.1)

theorem analytic_centeredMoment (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n m : ℕ+) (d : ℕ) : AnalyticOnNhd ℂ (P.centeredMoment W n m d) (P.momentSource C) := by
  apply analyticOnNhd_circleIntegral_of_jointAnalytic _ (P.momentJointDomain_open C)
    (P.analytic_centeredMomentIntegrand C n m d) _ _ (P.radii_pos (m:ℤ)).le (P.momentSource_open C)
  intro q hq z hz
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq.1).2 (m:ℤ)
    (P.centers (m:ℤ)) (P.radii (m:ℤ)) (P.radii_pos _) (P.discs_eq _)
  exact ⟨⟨hq.1,D.sphere_subset_rootDomain hz⟩,hq⟩

theorem centeredMoment_zero_order (P : HillProductEquationPatch) (W : Set (CoeffPair 2))
    (n m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source) :
    (2*Real.pi:ℂ)⁻¹*P.centeredMoment W n m 0 q=if m=n then 1 else 0 := by
  have he : P.centeredMoment W n m 0 q=
      ∮ z in C((P.centers (m:ℤ):ℂ),P.radii (m:ℤ)), P.abelianFrequencyDifferential n (z,q) := by
    simp only [centeredMoment,centeredMomentIntegrand,mul_zero,pow_zero,one_mul]
  rw [he]
  exact P.abelianFrequencyDifferential_period n m q hq
    (P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 (m:ℤ)
      (P.centers (m:ℤ)) (P.radii (m:ℤ)) (P.radii_pos _) (P.discs_eq _))

theorem exists_centeredMoment_neighborhood (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ W : Set (CoeffPair 2), ∃ C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W,
      q ∈ P.momentSource C ∧ ∀ n m : ℕ+, ∀ d : ℕ,
        AnalyticOnNhd ℂ (P.centeredMoment W n m d) (P.momentSource C) := by
  obtain ⟨W,_,_,hfamily⟩ := exists_sourceFullAbelianUniformCauchyFamilies (p := 2) (by simp) (by norm_num)
  let u : PeriodOneRealL2 := ⟨P.parent.parent.miuraBall.actionBall.lift q,
    P.parent.parent.miuraBall.actionBall.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
  let φ : realTypeSourceSubmodule 2 := ⟨P.sourcePsi q,(hillMiuraRealSource u).property⟩
  obtain ⟨C,hC⟩ := hfamily φ
  refine ⟨W,C,⟨hq,?_⟩,fun n m d => P.analytic_centeredMoment C n m d⟩
  rw [hC]
  exact mem_ball_self C.discs.sourceRadius_pos

theorem centeredMoment_independent_primitive_neighborhood (P : HillProductEquationPatch)
    {V : Set (CoeffPair 2)}
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (E : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) V)
    (n m : ℕ+) (d : ℕ) (q : PeriodOneHminusOne)
    (hq : q ∈ P.momentSource C ∩ P.momentSource E) :
    P.centeredMoment W n m d q=P.centeredMoment V n m d q := by
  obtain ⟨D⟩ := C.charts (P.sourcePsi q) hq.1.2
  obtain ⟨F⟩ := E.charts (P.sourcePsi q) hq.2.2
  let R := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq.1.1).2 (m:ℤ)
    (P.centers (m:ℤ)) (P.radii (m:ℤ)) (P.radii_pos _) (P.discs_eq _)
  apply circleIntegral.integral_congr (P.radii_pos (m:ℤ)).le
  intro z hz
  dsimp only [centeredMomentIntegrand]
  rw [sourceFullAbelianPrimitive_independent_neighborhood D F (m:ℤ) z
    (sourceCanonicalRootDomain_subset_openGapComplement (by simp) (by norm_num) _ (R.sphere_subset_rootDomain hz))]

end NLS.KdV.HillProductEquationPatch
