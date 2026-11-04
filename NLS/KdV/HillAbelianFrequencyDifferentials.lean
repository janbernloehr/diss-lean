import NLS.KdV.HillCanonicalEnergyLoopPeriods
import NLS.ZakharovShabat.SourceStandardRootOmittedJointAnalytic

/-! The actual canonical Hill differential in a fixed local Miura
frequency coordinate. Deleting the selected root gives a numerator
analytic across its ENTIRE closed gap disc, on ONE complex native
source neighborhood BEFORE ALL differential and gap indices. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def abelianFrequencyNumerator (P : HillProductEquationPatch) (n : ℕ+)
    (t : ℂ × PeriodOneHminusOne) : ℂ :=
  2*t.1*hillHminusCanonicalPsi n (t.1^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),t.2)

def abelianFrequencyDifferential (P : HillProductEquationPatch) (n : ℕ+)
    (t : ℂ × PeriodOneHminusOne) : ℂ :=
  P.abelianFrequencyNumerator n t/sourceCanonicalRoot (by norm_num) (by norm_num) (P.sourcePsi t.2) t.1

def abelianGapNumerator (P : HillProductEquationPatch) (n m : ℕ+)
    (t : ℂ × PeriodOneHminusOne) : ℂ :=
  P.abelianFrequencyNumerator n t/(2*I*sourceStandardRootOmittedProduct
    (by norm_num) (by norm_num) ((m:ℕ):ℤ) (P.sourcePsi t.2) t.1)

theorem analytic_abelianFrequencyNumerator (P : HillProductEquationPatch) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.abelianFrequencyNumerator n) (univ ×ˢ P.source) := by
  intro t ht
  have hsource : t.2 ∈ hillHminusCanonicalPsiDomain := mem_iUnion.mpr ⟨P.parent,P.subset ht.2⟩
  have hpsi := (analyticOnNhd_hillHminusCanonicalPsi n
    (t.1^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),t.2) ⟨mem_univ _,hsource⟩).comp
    (f := fun x : ℂ × PeriodOneHminusOne => (x.1^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),x.2))
    ((analyticAt_fst.pow 2 |>.sub analyticAt_const).prod analyticAt_snd)
  exact (analyticAt_const.mul analyticAt_fst).mul hpsi

theorem abelianFrequencyNumerator_eq_local (P : HillProductEquationPatch) (n : ℕ+)
    (z : ℂ) (q : PeriodOneHminusOne) (hq : q ∈ P.source) :
    P.abelianFrequencyNumerator n (z,q) = 2*z*P.parent.parent.psiNumerator P.parent.family n
      (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q) := by
  rw [abelianFrequencyNumerator,P.parent.canonical_numerator_eq n _ q (P.subset hq)]
  rfl

theorem abelianFrequencyDifferential_period (P : HillProductEquationPatch) (n m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)) :
    (2*Real.pi:ℂ)⁻¹*(∮ z in C((D.center:ℂ),D.radius), P.abelianFrequencyDifferential n (z,q)) =
      if m = n then 1 else 0 := by
  have he : (fun z => P.abelianFrequencyDifferential n (z,q)) =
      (fun z => (2*z*P.parent.parent.psiNumerator P.parent.family n
        (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q))/
        sourceCanonicalRoot (by norm_num) (by norm_num) (P.sourcePsi q) z) := by
    funext z
    rw [abelianFrequencyDifferential,P.abelianFrequencyNumerator_eq_local n z q hq]
  rw [he]
  exact P.parent.parent.psiNumerator_pullback_period P.parent.family n m q
    (P.parent.subset (P.subset hq)) D

theorem abelianFrequencyDifferential_eq_gap_quotient (P : HillProductEquationPatch) (n m : ℕ+)
    (t : ℂ × PeriodOneHminusOne) (ht : t.1 ∈ sourceCanonicalRootDomain
      (by norm_num) (by norm_num) (P.sourcePsi t.2)) :
    P.abelianFrequencyDifferential n t = P.abelianGapNumerator n m t/
      sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi t.2) ((m:ℕ):ℤ) t.1 := by
  rw [abelianFrequencyDifferential,sourceCanonicalRoot_eq_omitted
    (by norm_num) (by norm_num) ((m:ℕ):ℤ),abelianGapNumerator]
  have hQ := sourceStandardRoot_ne_zero_off_segment (by norm_num) (by norm_num)
    (P.sourcePsi t.2) ((m:ℕ):ℤ) t.1 (ht _)
  have hO := sourceStandardRootOmittedProduct_ne_zero (by norm_num) (by norm_num)
    (P.sourcePsi t.2) t.1 ((m:ℕ):ℤ) (fun j _ => ht j)
  field_simp [hQ,hO]

theorem exists_common_analytic_abelianGapNumerator_neighborhood (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q ∈ V ∧ V ⊆ P.source ∧
      ∀ n m : ℕ+, AnalyticOnNhd ℂ (P.abelianGapNumerator n m)
        (closedBall (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) ×ˢ V) := by
  obtain ⟨W,hW,_,hRW,hO⟩ := exists_global_source_analytic_omittedJointProduct (p := 2) (by norm_num) (by norm_num)
  let V := P.source ∩ P.sourcePsi ⁻¹' W
  have hV : IsOpen V := P.analytic_sourcePsi.continuousOn.isOpen_inter_preimage P.source_open hW
  have hreal : IsRealType (CoeffPair.toMax 2 (P.sourcePsi q)) := by
    let u : PeriodOneRealL2 := ⟨P.parent.parent.miuraBall.actionBall.lift q,
      P.parent.parent.miuraBall.actionBall.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
    exact (hillMiuraRealSource u).property
  refine ⟨V,hV,⟨hq,hRW hreal⟩,inter_subset_left,?_⟩
  intro n m t ht
  let D := P.isolating.periodCircle (P.sourcePsi t.2) (P.image t.2 ht.2.1).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  have hz := D.closedBall_subset_omittedDomain ht.1
  have hprod := ((hO ((m:ℕ):ℤ)).2.1 (t.1,P.sourcePsi t.2) ⟨ht.2.2,hz⟩).comp
    (f := fun x : ℂ × PeriodOneHminusOne => (x.1,P.sourcePsi x.2))
    (analyticAt_fst.prod ((P.analytic_sourcePsi t.2 ht.2.1).comp (f := Prod.snd) analyticAt_snd))
  exact (P.analytic_abelianFrequencyNumerator n t ⟨mem_univ _,ht.2.1⟩).div
    ((analyticAt_const.mul analyticAt_const).mul hprod)
    (mul_ne_zero (by simp) (sourceStandardRootOmittedProduct_ne_zero (by norm_num) (by norm_num)
      (P.sourcePsi t.2) t.1 ((m:ℕ):ℤ) hz))

end NLS.KdV.HillProductEquationPatch
