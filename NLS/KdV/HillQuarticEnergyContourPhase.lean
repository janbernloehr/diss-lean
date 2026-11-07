import NLS.KdV.HillCompletePhasePrimitive
import NLS.Poisson.GardnerBracketCircleIntegral

/-! The actual Gardner variation of the fixed quartic contour. Its
physical energy normalization gives exactly 2/(i*pi) times the raw
cubic Hill contour. No ambient H-minus-one energy identity is asserted. -/
noncomputable section
open Set Metric Complex NLS.Poisson NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch
variable {W : Set (CoeffPair 2)}

def weightedQuarticPrimitiveCircle (P : HillProductEquationPatch) (W : Set (CoeffPair 2))
    (c : ℂ) (R : ℝ) (q : PeriodOneHminusOne) : ℂ :=
  ∮ z in C(c,R), z*(P.liftedAbelianPrimitive W 0 (z,q))^4

def quarticEnergyContour (P : HillProductEquationPatch) (W : Set (CoeffPair 2))
    (c : ℂ) (R : ℝ) (q : PeriodOneHminusOne) : ℂ :=
  (2*I/(Real.pi:ℂ))*P.weightedQuarticPrimitiveCircle W c R q

theorem analyticAt_weightedQuarticPrimitiveCircle (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) (P.sourcePsi q)) :
    AnalyticAt ℂ (P.weightedQuarticPrimitiveCircle W c R) q := by
  let F : ℂ × PeriodOneHminusOne → ℂ := fun t => t.1*(P.liftedAbelianPrimitive W 0 t)^4
  have hF : AnalyticOnNhd ℂ F (P.momentJointDomain C) :=
    fun t ht => analyticAt_fst.mul ((P.analytic_liftedAbelianPrimitive C 0 t ht).pow 4)
  obtain ⟨V,hV,hqV,_,_,hbound⟩ := exists_uniform_joint_fderiv_bound_on_circle F _
    (P.momentJointDomain_open C) hF c R q (fun z hz => ⟨⟨hq.1,hcircle hz⟩,hq⟩)
  exact analyticOnNhd_circleIntegral_of_jointAnalytic F (P.momentJointDomain_open C) hF c R hR hV
    (fun a ha z hz => (hbound z hz a ha).1) q hqV

theorem analyticAt_quarticEnergyContour (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) (P.sourcePsi q)) :
    AnalyticAt ℂ (P.quarticEnergyContour W c R) q :=
  analyticAt_const.mul (P.analyticAt_weightedQuarticPrimitiveCircle C c R hR q hq hcircle)

end NLS.KdV.HillProductEquationPatch
namespace NLS.KdV.HillPhysicalOnIndexPhaseChart
variable {P : HillProductEquationPatch} {n : ℕ+} {W : Set (CoeffPair 2)}

theorem completePhase_weightedQuarticCircle_Gardner_of_real
    (A : HillPhysicalOnIndexPhaseChart P n)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (q : PeriodOneHminusOne) (hq : q ∈ A.source)
    (hC : q ∈ P.momentSource C) (hr : IsRealPeriodOneHminusOne q)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) (P.sourcePsi q)) :
    hminusGardnerBracket A.completePhase (P.weightedQuarticPrimitiveCircle W c R) q =
      ∮ z in C(c,R), (P.liftedAbelianPrimitive W 0 (z,q))^3*P.abelianFrequencyDifferential n (z,q) := by
  let F : ℂ × PeriodOneHminusOne → ℂ := fun t => t.1*(P.liftedAbelianPrimitive W 0 t)^4
  have hF : AnalyticOnNhd ℂ F (P.momentJointDomain C) :=
    fun t ht => analyticAt_fst.mul ((P.analytic_liftedAbelianPrimitive C 0 t ht).pow 4)
  change gardnerCotangentBivector (fderiv ℂ A.completePhase q)
    (fderiv ℂ (fun a => ∮ z in C(c,R), F (z,a)) q)=_
  rw [gardnerCotangentBivector_circleIntegral_of_jointAnalytic F _ (P.momentJointDomain_open C)
    hF c R hR q (fun z hz => ⟨⟨hC.1,hcircle hz⟩,hC⟩)]
  apply circleIntegral.integral_congr hR
  intro z hz
  exact A.completePhase_weightedQuarticIntegrand_Gardner_of_real C z q hq hC hr (hcircle hz)

theorem quarticEnergyContour_completePhase_Gardner_of_real
    (A : HillPhysicalOnIndexPhaseChart P n)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (q : PeriodOneHminusOne) (hq : q ∈ A.source)
    (hC : q ∈ P.momentSource C) (hr : IsRealPeriodOneHminusOne q)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) (P.sourcePsi q)) :
    hminusGardnerBracket (P.quarticEnergyContour W c R) A.completePhase q =
      (2/(I*(Real.pi:ℂ)))*
        (∮ z in C(c,R), (P.liftedAbelianPrimitive W 0 (z,q))^3*P.abelianFrequencyDifferential n (z,q)) := by
  rw [hminusGardnerBracket_antisymm]
  have hd := ((P.analyticAt_weightedQuarticPrimitiveCircle C c R hR q hC hcircle).differentiableAt.hasFDerivAt).const_mul
    (2*I/(Real.pi:ℂ))
  change -(gardnerCotangentBivector (fderiv ℂ A.completePhase q)
    (fderiv ℂ (fun a => (2*I/(Real.pi:ℂ))*P.weightedQuarticPrimitiveCircle W c R a) q))=_
  rw [hd.fderiv,map_smul,smul_eq_mul]
  have he := A.completePhase_weightedQuarticCircle_Gardner_of_real C c R hR q hq hC hr hcircle
  change gardnerCotangentBivector (fderiv ℂ A.completePhase q)
    (fderiv ℂ (P.weightedQuarticPrimitiveCircle W c R) q)=_ at he
  rw [he]
  field_simp
  rw [I_sq]
  ring

end NLS.KdV.HillPhysicalOnIndexPhaseChart
