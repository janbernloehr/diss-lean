import NLS.KdV.HillHminusCommonDirichletFamily
import NLS.KdV.HillHminusCommonDirichletSheets

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

/-- One common complex H-minus-one neighborhood supports ALL actual
Dirichlet energy charts and ALL fixed original normalized numerators.
Their original physical labels, terminal multipliers and signed sheets
agree throughout one original real neighborhood mapped into that complex
domain, with a uniform full signed L2 displacement bound. -/
theorem exists_hillOriginal_dirichlet_numerators_common_hminus_extension
    (q : RealPeriodOneHillPotential) (M : ℝ) :
    ∃ P : HillHminusPsiChart, ∃ c R : ℝ, ∃ V : Set PeriodOneHminusOne,
      ∃ W : Set RealPeriodOneHillPotential,
      0<c ∧ M<c ∧ 0<R ∧ P.miura.energyShift=(c:ℂ)^2 ∧
      IsOpen V ∧ hillOriginalHminusSource q.val∈V ∧ V⊆P.source ∧
      IsOpen W ∧ q∈W ∧ (∀ p∈W, hillOriginalHminusSource p.val∈V) ∧
      SourceLemma12_12Data (by norm_num) (by norm_num)
        P.family.originalDomain P.family.domain P.family.roots ∧
      AnalyticOnNhd ℂ P.dirichletDisplacement V ∧
      (∀ a∈V, ‖P.dirichletDisplacement a‖≤R) ∧
      ∀ n : ℕ+, AnalyticOnNhd ℂ (P.dirichletEnergy n) V ∧
        AnalyticOnNhd ℂ (P.numerator n) (univ ×ˢ V) ∧
        AnalyticOnNhd ℂ (P.dirichletTerminal n) V ∧
        AnalyticOnNhd ℂ (P.dirichletSheet n) V ∧
        (∀ a∈V, hillHminusDirichlet a (P.dirichletEnergy n a)=0 ∧
          P.dirichletFrequency (n:ℕ) a≠0 ∧ P.dirichletTerminal n a≠0 ∧
          P.dirichletSheet n a^2=hillHminusRadicand a (P.dirichletEnergy n a)) ∧
        ∀ p∈W,
          P.dirichletEnergy n (hillOriginalHminusSource p.val)=
            (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos:ℂ) ∧
          P.dirichletTerminal n (hillOriginalHminusSource p.val)=
            hillL2DirichletSlope (SpectralWeight.one.toCoeff p.val)
              (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos) ∧
          P.dirichletSheet n (hillOriginalHminusSource p.val)=
            hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
              (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos) ∧
          ∀ E : ℂ, P.numerator n (E,hillOriginalHminusSource p.val)=
            hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n n.pos E := by
  obtain ⟨P,c,hc,hMc,hshift,hqP,hreal,houtside,hest⟩ :=
    exists_hillHminusPsiChart_real_form_outside_shift (hillOriginalHminusSource q.val)
      (hillOriginalHminusSource_real q.val q.property.2) M
  obtain ⟨R,hR,V,hV,hqV,hVP,hdisp,hbound,hfamily⟩ := P.exists_common_dirichlet_family
    (hillOriginalHminusSource q.val) hqP
    (hreal _ hqP.1 (hillOriginalHminusSource_real q.val q.property.2))
  let W : Set RealPeriodOneHillPotential := {p | hillOriginalHminusSource p.val∈V}
  have hW : IsOpen W := hV.preimage (hillOriginalHminusSource.continuous.comp continuous_subtype_val)
  refine ⟨P,c,R,V,W,hc,hMc,hR,hshift,hV,hqV,hVP,hW,hqV,(fun p hp => hp),hest,hdisp,hbound,?_⟩
  intro n
  have hsheet := P.common_dirichlet_terminal_sheet V hVP n (hfamily n).1
    (fun a ha => ((hfamily n).2 a ha).2)
  refine ⟨(hfamily n).1,?_,hsheet.1,hsheet.2.1,?_,?_⟩
  · intro t ht
    exact P.analytic_numerator n t ⟨ht.1,hVP ht.2⟩
  · intro a ha
    exact ⟨((hfamily n).2 a ha).2,((hfamily n).2 a ha).1,
      (hsheet.2.2 a ha).1,(hsheet.2.2 a ha).2.2⟩
  · intro p hp
    have hpP := hVP hp
    exact ⟨P.dirichletEnergy_eq_original p hpP hreal (houtside _ hpP.1) c hshift n,
      P.dirichletTerminal_eq_original p hpP hreal (houtside _ hpP.1) c hshift n,
      P.dirichletSheet_eq_original p hpP hreal (houtside _ hpP.1) c hshift n,
      fun E => congrFun (P.numerator_eq_original p hpP hreal (houtside _ hpP.1) c hshift n) E⟩

end NLS.KdV
