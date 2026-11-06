import NLS.KdV.HillHminusCommonDirichletFamily
import NLS.KdV.HillHminusNormingCharts
import NLS.KdV.HillDirichletSheetRoot

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV
namespace HillHminusPsiChart

/-- The actual derivative-one terminal multiplier on the actual common
Dirichlet energy branch. -/
def dirichletTerminal (P : HillHminusPsiChart) (n : ℕ+) : PeriodOneHminusOne → ℂ :=
  P.miura.dirichletTerminal (P.dirichletEnergy n)

/-- The ORIGINAL physical sheet convention is T minus its inverse.
This definition retains that sign before any square-root choice. -/
def dirichletSheet (P : HillHminusPsiChart) (n : ℕ+) (a : PeriodOneHminusOne) : ℂ :=
  2*P.dirichletTerminal n a-hillHminusDiscriminant a (P.dirichletEnergy n a)

/-- Every common actual Dirichlet family has common analytic terminal
and sheet families, with genuine nonzero multipliers and radicand squares. -/
theorem common_dirichlet_terminal_sheet (P : HillHminusPsiChart) (V : Set PeriodOneHminusOne)
    (hVP : V⊆P.source) (n : ℕ+) (henergy : AnalyticOnNhd ℂ (P.dirichletEnergy n) V)
    (hroot : ∀ a∈V, hillHminusDirichlet a (P.dirichletEnergy n a)=0) :
    AnalyticOnNhd ℂ (P.dirichletTerminal n) V ∧ AnalyticOnNhd ℂ (P.dirichletSheet n) V ∧
      ∀ a∈V, P.dirichletTerminal n a≠0 ∧
        P.dirichletSheet n a=P.dirichletTerminal n a-(P.dirichletTerminal n a)⁻¹ ∧
        P.dirichletSheet n a^2=hillHminusRadicand a (P.dirichletEnergy n a) := by
  have hT : AnalyticOnNhd ℂ (P.dirichletTerminal n) V := fun a ha =>
    P.miura.analyticAt_dirichletTerminal _ a (hVP ha).1 (henergy a ha)
  have hS : AnalyticOnNhd ℂ (P.dirichletSheet n) V := by
    intro a ha
    rw [show P.dirichletSheet n=(fun b => 2*P.dirichletTerminal n b-
      hillHminusDiscriminant b (P.dirichletEnergy n b)) from rfl]
    exact (analyticAt_const.mul (hT a ha)).sub
      ((analyticOnNhd_hillHminusDiscriminant_joint (P.dirichletEnergy n a,a) (mem_univ _)).comp
        (f := fun b => (P.dirichletEnergy n b,b)) ((henergy a ha).prod analyticAt_id))
  refine ⟨hT,hS,?_⟩
  intro a ha
  have hn := P.miura.dirichletTerminal_ne_zero_of_root _ a (hVP ha).1 (hroot a ha)
  change P.dirichletTerminal n a≠0 at hn
  have ht := P.miura.discriminant_eq_dirichletTerminal_inv_add _ a (hVP ha).1 (hroot a ha)
  have hs : P.dirichletSheet n a=P.dirichletTerminal n a-(P.dirichletTerminal n a)⁻¹ := by
    rw [dirichletSheet,ht]
    change 2*P.dirichletTerminal n a-((P.dirichletTerminal n a)⁻¹+P.dirichletTerminal n a)=_
    ring
  refine ⟨hn,hs,?_⟩
  rw [hs,hillHminusRadicand,ht]
  change (P.dirichletTerminal n a-(P.dirichletTerminal n a)⁻¹)^2=
    ((P.dirichletTerminal n a)⁻¹+P.dirichletTerminal n a)^2-4
  field_simp [hn]
  ring

/-- The actual common terminal multiplier is the literal ORIGINAL
physical Dirichlet slope at the original labelled energy. -/
theorem dirichletTerminal_eq_original (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val∈P.source)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k)=conj (P.miura.lift a k))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
    (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2) (n : ℕ+) :
    P.dirichletTerminal n (hillOriginalHminusSource q.val)=
      hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos) := by
  have hE := P.dirichletEnergy_eq_original q hq hreal houtside c hshift n
  have hz : hillHminusDirichlet (hillOriginalHminusSource q.val)
      (P.dirichletEnergy n (hillOriginalHminusSource q.val))=0 := by
    rw [hE,hillHminusDirichlet_original_source_agreement q.val q.property.1]
    exact hillDirichletEnergy_zero q.val q.property.1 q.property.2 n n.pos
  change P.miura.dirichletTerminal (P.dirichletEnergy n) (hillOriginalHminusSource q.val)=_
  rw [P.miura.dirichletTerminal_original_source _ q.val q.property.1 hq.1 hz,hE]

/-- The actual common sheet retains precisely the ORIGINAL physical
Dirichlet root sign, including its zero at collapsed gaps. -/
theorem dirichletSheet_eq_original (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val∈P.source)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k)=conj (P.miura.lift a k))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
    (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2) (n : ℕ+) :
    P.dirichletSheet n (hillOriginalHminusSource q.val)=
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos) := by
  rw [dirichletSheet,P.dirichletTerminal_eq_original q hq hreal houtside c hshift n,
    P.dirichletEnergy_eq_original q hq hreal houtside c hshift n,
    hillHminusDiscriminant_original_source_agreement q.val q.property.1]
  rfl

end HillHminusPsiChart
end NLS.KdV
