import NLS.KdV.HillAbelianCartesian

/-! Exact complete Abelian phase formulas at the ACTUAL auxiliary
physical divisor. Both its frequency and its norming-sheet sign are
retained, and the correction is the literal infinite physical sum. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem exists_common_complete_Abelian_patch_ball (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ r : ℝ, 0 < r ∧ ball q r ⊆ P.physicalDirichletSource ∩ hillHminusOffIndexAnalyticDomain ∧
      ∀ n : ℕ+, ∀ a ∈ ball q r,
        hillHminusAbelianCartesianPlus n a = P.physicalOnIndexCartesianPlus n a*
          Complex.exp (I*P.physicalOffIndexAbelianCorrection n a) ∧
        hillHminusAbelianCartesianMinus n a = P.physicalOnIndexCartesianMinus n a*
          Complex.exp (-I*P.physicalOffIndexAbelianCorrection n a) := by
  obtain ⟨rd,hrd,hbd,hd⟩ := exists_common_intrinsic_diagonal_Cartesian_patch_ball P q hq hr
  obtain ⟨rb,hrb,hbb,hb⟩ := exists_common_offIndex_correction_patch_ball P q hq hr
  have hopen := isOpen_hillHminusOffIndexAnalyticDomain
  have hqW := real_mem_hillHminusOffIndexAnalyticDomain q hr
  obtain ⟨r,hrpos,hsub⟩ := Metric.mem_nhds_iff.mp
    (((isOpen_ball.inter isOpen_ball).inter hopen).mem_nhds
      ⟨⟨mem_ball_self hrd,mem_ball_self hrb⟩,hqW⟩)
  refine ⟨r,hrpos,(fun a ha => ⟨(hbd (hsub ha).1.1).1,(hsub ha).2⟩),?_⟩
  intro n a ha
  have had := (hsub ha).1.1
  have hab := (hsub ha).1.2
  simp only [hillHminusAbelianCartesianPlus,hillHminusAbelianCartesianMinus,
    (hd n a had).1,(hd n a had).2,(hb n a hab).2.2,and_self]

theorem complete_Abelian_phase_formula_at_physical_terminal (P : HillProductEquationPatch)
    (n : ℕ+) (q : PeriodOneHminusOne)
    (hplus : hillHminusAbelianCartesianPlus n q = P.physicalOnIndexCartesianPlus n q*
      Complex.exp (I*P.physicalOffIndexAbelianCorrection n q))
    (hminus : hillHminusAbelianCartesianMinus n q = P.physicalOnIndexCartesianMinus n q*
      Complex.exp (-I*P.physicalOffIndexAbelianCorrection n q)) (δ θ : ℂ)
    (hpoint : cosineGapPoint (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)) δ θ =
      P.physicalDirichletFrequency ((n:ℕ):ℤ) q)
    (hroot : -I*δ*Complex.sin θ = P.physicalDirichletRootCoefficient n q) :
    hillHminusAbelianCartesianPlus n q =
      (4*sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)*δ)*
        Complex.exp (I*(P.onIndexAbelianCosinePhase n q δ θ+P.physicalOffIndexAbelianCorrection n q)) ∧
    hillHminusAbelianCartesianMinus n q =
      (4*sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)*δ)*
        Complex.exp (-I*(P.onIndexAbelianCosinePhase n q δ θ+P.physicalOffIndexAbelianCorrection n q)) := by
  rw [hplus,hminus,P.physicalOnIndexCartesianPlus_eq_gap_mul_phase_exp n q δ θ hpoint hroot,
    P.physicalOnIndexCartesianMinus_eq_gap_mul_phase_exp n q δ θ hpoint hroot]
  constructor <;> rw [mul_add,Complex.exp_add,mul_assoc]

end NLS.KdV
