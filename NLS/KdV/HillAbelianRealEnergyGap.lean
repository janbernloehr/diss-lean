import NLS.KdV.HillAbelianNativeEnergyEquation
import NLS.KdV.HminusOneDirichletAllGaps
import NLS.ComplexAnalysis.RealGapSquareRoot
import Mathlib.Analysis.Normed.Module.Convex

/-! Every original real energy gap, with ALL low and collapsed gaps,
lies in the filled energy domain of each available Miura patch. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem real_energy_mem_abelianFilledEnergyDomain (P : HillProductEquationPatch) (m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (x : ℝ) (hx : x ∈ Icc (hillHminusLabels q hr (2*(m:ℕ)-1)) (hillHminusLabels q hr (2*(m:ℕ)))) :
    ((x:ℂ),q) ∈ P.abelianFilledEnergyDomain m := by
  let k : ℤ := ((m:ℕ):ℤ)
  let l := canonicalPeriodicLeft (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) k
  let r := canonicalPeriodicRight (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) k
  let c := P.parent.parent.miuraBall.actionBall.shift
  let u : PeriodOneRealL2 := ⟨P.parent.parent.miuraBall.actionBall.lift q,
    P.parent.parent.miuraBall.actionBall.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
  have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType (by norm_num) (by norm_num)
    (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _)
    (isRealType_periodOnePotential _ (hillMiuraRealSource u).property) k
  have hl : (l.re:ℂ) = l := Complex.ext rfl (by simpa only [ofReal_im] using him.1.symm)
  have hr' : (r.re:ℂ) = r := Complex.ext rfl (by simpa only [ofReal_im] using him.2.symm)
  have hlD : l ∈ ball (P.centers k:ℂ) (P.radii k) := by
    rw [← P.discs_eq]
    exact P.isolating.gap (P.sourcePsi q) (P.image q hq).2 k (left_mem_segment ℝ _ _)
  have hrD : r ∈ ball (P.centers k:ℂ) (P.radii k) := by
    rw [← P.discs_eq]
    exact P.isolating.gap (P.sourcePsi q) (P.image q hq).2 k (right_mem_segment ℝ _ _)
  have hlpos : 0 < l.re := P.abelianGapDisc_re_pos_of_real m q hq hr l hlD
  have hrpos : 0 < r.re := P.abelianGapDisc_re_pos_of_real m q hq hr r hrD
  have he := P.abelian_gap_endpoint_energies_eq_original_labels m q hq hr
  change l^2-(c:ℂ) = _ ∧ r^2-(c:ℂ) = _ at he
  have hel : l.re^2-c = hillHminusLabels q hr (2*(m:ℕ)-1) := by
    have h := congrArg Complex.re he.1
    rw [← hl] at h
    simpa only [sub_re,ofReal_re,← ofReal_pow] using h
  have her : r.re^2-c = hillHminusLabels q hr (2*(m:ℕ)) := by
    have h := congrArg Complex.re he.2
    rw [← hr'] at h
    simpa only [sub_re,ofReal_re,← ofReal_pow] using h
  have hxc : 0 < x+c := by rw [← hel,← her] at hx; nlinarith [hx.1]
  let z : ℂ := (Real.sqrt (x+c):ℂ)
  have hzpos : 0 < z.re := by exact Real.sqrt_pos.mpr hxc
  have hbounds : Real.sqrt (x+c) ∈ Icc l.re r.re := by
    have hs := Real.sq_sqrt hxc.le
    have hn := Real.sqrt_nonneg (x+c)
    rw [← hel,← her] at hx
    constructor <;> nlinarith [hx.1,hx.2]
  have hzD : z ∈ ball (P.centers k:ℂ) (P.radii k) :=
    ofReal_mem_convex_of_mem_Icc _ (convex_ball _ _) l.re r.re _ (hl.symm ▸ hlD) (hr'.symm ▸ hrD) hbounds
  have hez : z^2-(c:ℂ) = (x:ℂ) := by
    have hs : (Real.sqrt (x+c))^2 = x+c := Real.sq_sqrt hxc.le
    dsimp only [z]
    rw [← ofReal_pow,← ofReal_sub]
    exact_mod_cast (show (Real.sqrt (x+c))^2-c = x by rw [hs]; ring)
  have h := P.abelianFilledEnergyDomain_mem_of_positive_frequency m q hq z hzpos hzD
  change (z^2-(c:ℂ),q) ∈ P.abelianFilledEnergyDomain m at h
  simpa only [hez] using h

theorem original_energy_segment_mem_filled_domain (P : HillProductEquationPatch) (m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    segment ℝ (hillHminusLabels q hr (2*(m:ℕ)-1):ℂ) (hillHminusLabels q hr (2*(m:ℕ)):ℂ) ⊆
      {E | (E,q) ∈ P.abelianFilledEnergyDomain m} := by
  let l := hillHminusLabels q hr (2*(m:ℕ)-1)
  let r := hillHminusLabels q hr (2*(m:ℕ))
  have hlr : l ≤ r := monotone_hillHminusLabels q hr (by omega)
  have he : segment ℝ (l:ℂ) (r:ℂ) = Complex.ofReal '' Icc l r := by
    rw [← segment_eq_Icc hlr]
    exact (image_segment ℝ Complex.ofRealCLM.toLinearMap.toAffineMap l r).symm
  intro E hE
  rw [he] at hE
  obtain ⟨x,hx,rfl⟩ := hE
  exact P.real_energy_mem_abelianFilledEnergyDomain m q hq hr x hx

end NLS.KdV.HillProductEquationPatch
