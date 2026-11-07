import NLS.KdV.HillPhysicalOffIndexAbelianValue
import NLS.KdV.HillAbelianPhysicalEnergyPullback
import NLS.ComplexAnalysis.AnalyticRadicandEquation

/-! Filled Abelian quotients in ORIGINAL Hill energy coordinates.
The physical divisor value is the actual norming sheet times this
quotient; its equation uses only the intrinsic Hill radicand and Psi. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def abelianEnergyCoordinates (P : HillProductEquationPatch) (t : ℂ × PeriodOneHminusOne) : ℂ × PeriodOneHminusOne :=
  (Complex.sqrt (t.1+(P.parent.parent.miuraBall.actionBall.shift:ℂ)),t.2)

def abelianFilledEnergyDomain (P : HillProductEquationPatch) (m : ℕ+) : Set (ℂ × PeriodOneHminusOne) :=
  {t | t.1+(P.parent.parent.miuraBall.actionBall.shift:ℂ) ∈ slitPlane} ∩
    P.abelianEnergyCoordinates ⁻¹' (ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ×ˢ P.source)

def offIndexAbelianEnergyQuotient (P : HillProductEquationPatch) (n m : ℕ+)
    (t : ℂ × PeriodOneHminusOne) : ℂ :=
  P.offIndexAbelianFilledQuotient n m (P.abelianEnergyCoordinates t)/
    P.abelianGapRootMultiplier m (P.abelianEnergyCoordinates t)

theorem analytic_abelianEnergyCoordinates (P : HillProductEquationPatch) :
    AnalyticOnNhd ℂ P.abelianEnergyCoordinates
      {t | t.1+(P.parent.parent.miuraBall.actionBall.shift:ℂ) ∈ slitPlane} := by
  intro t ht
  have hs : AnalyticAt ℂ Complex.sqrt (t.1+(P.parent.parent.miuraBall.actionBall.shift:ℂ)) :=
    Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds ht)
  exact (hs.comp (f := fun x : ℂ × PeriodOneHminusOne => x.1+(P.parent.parent.miuraBall.actionBall.shift:ℂ))
    (analyticAt_fst.add analyticAt_const)).prod analyticAt_snd

theorem abelianFilledEnergyDomain_open (P : HillProductEquationPatch) (m : ℕ+) :
    IsOpen (P.abelianFilledEnergyDomain m) :=
  P.analytic_abelianEnergyCoordinates.continuousOn.isOpen_inter_preimage
    (isOpen_slitPlane.preimage (continuous_fst.add continuous_const)) (isOpen_ball.prod P.source_open)

theorem analytic_offIndexAbelianEnergyQuotient (P : HillProductEquationPatch) (n m : ℕ+) (hmn : m ≠ n) :
    AnalyticOnNhd ℂ (P.offIndexAbelianEnergyQuotient n m) (P.abelianFilledEnergyDomain m) := by
  intro t ht
  exact (((P.analytic_offIndexAbelianFilledQuotient n m hmn _ ht.2).div
    (P.analytic_abelianGapRootMultiplier m _ ht.2) (P.abelianGapRootMultiplier_ne_zero m _ ht.2)).comp
    (f := P.abelianEnergyCoordinates) (P.analytic_abelianEnergyCoordinates t ht.1))

theorem abelianFilledEnergyDomain_mem_of_positive_frequency (P : HillProductEquationPatch) (m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (z : ℂ) (hz : 0 < z.re)
    (hd : z ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))) :
    (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q) ∈ P.abelianFilledEnergyDomain m := by
  refine ⟨?_,?_⟩
  · change z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ)+(P.parent.parent.miuraBall.actionBall.shift:ℂ) ∈ slitPlane
    simpa only [sub_add_cancel] using sq_mem_slitPlane_of_re_pos z hz
  · change Complex.sqrt (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ)+(P.parent.parent.miuraBall.actionBall.shift:ℂ)) ∈ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ∧ q ∈ P.source
    simpa only [sub_add_cancel,sqrt_sq_of_re_pos z hz] using And.intro hd hq

theorem offIndexAbelianEnergyQuotient_at_positive_frequency (P : HillProductEquationPatch) (n m : ℕ+)
    (q : PeriodOneHminusOne) (z : ℂ) (hz : 0 < z.re) :
    P.offIndexAbelianEnergyQuotient n m (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q) =
      P.offIndexAbelianFilledQuotient n m (z,q)/P.abelianGapRootMultiplier m (z,q) := by
  simp only [offIndexAbelianEnergyQuotient,abelianEnergyCoordinates,sub_add_cancel,sqrt_sq_of_re_pos z hz]

end NLS.KdV.HillProductEquationPatch
