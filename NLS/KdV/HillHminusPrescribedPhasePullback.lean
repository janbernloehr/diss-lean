import NLS.KdV.HillHminusPrescribedSheets
import NLS.KdV.HillHminusPhaseNumeratorCompatibility
import NLS.ZakharovShabat.SourceAngularIntegrand
import NLS.ComplexAnalysis.QuadraticEnergyPath

noncomputable section
set_option autoImplicit false
open Set Metric Complex MeasureTheory NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart

/-- The fixed normalized physical numerator on the ACTUAL energy
sheet prescribed by the terminal value w. -/
def prescribedDifferential (P : HillHminusPsiChart) (n : ℕ+) (w : ℂ)
    (t : ℂ × PeriodOneHminusOne) : ℂ :=
  P.numerator n t/hillHminusPrescribedRoot w t

theorem analytic_prescribedDifferential (P : HillHminusPsiChart) (n : ℕ+)
    (w : ℂ) (hw : w≠0) :
    AnalyticOnNhd ℂ (P.prescribedDifferential n w)
      ((univ ×ˢ P.source)∩hillHminusPrescribedRootDomain w) := by
  intro t ht
  exact (P.analytic_numerator n t ht.1).div
    (analyticOnNhd_hillHminusPrescribedRoot w t ht.2)
    (hillHminusPrescribedRoot_ne_zero w hw t ht.2)

/-- ONE complex neighborhood precedes ALL indices, terminal sheet
values and frequencies. The exact two-z Jacobian gives the difference
of the actual source integrands at opposite frequencies on the SAME
prescribed sheet, including values on canonical cuts. -/
theorem exists_common_prescribedDifferential_sourcePhase (P : HillHminusPsiChart)
    (q : PeriodOneHminusOne) (hq : q∈P.source)
    (hreal : ∀ k : ℤ, P.miura.lift q (-k)=conj (P.miura.lift q k)) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q∈U ∧ U⊆P.source ∧
      ∀ a∈U, ∀ n : ℕ+, ∀ w z : ℂ,
        P.prescribedDifferential n w (z^2-P.miura.energyShift,a)*(2*z)=
          sourceAngularIntegrand ((n:ℕ):ℤ) P.family.roots (sourceAngularRootSheet (by simp) w)
            (z,P.dirichletSource a)-
          sourceAngularIntegrand ((n:ℕ):ℤ) P.family.roots (sourceAngularRootSheet (by simp) w)
            (-z,P.dirichletSource a) := by
  obtain ⟨U,hU,hqU,hUP,hmatch⟩ := P.exists_common_dirichletSource_numerator_agreement q hq hreal
  refine ⟨U,hU,hqU,hUP,?_⟩
  intro a ha n w z
  have hf := ((hmatch a ha).2 n).2 z
  rw [prescribedDifferential,P.prescribedRoot_squared_frequency_eq_sourcePhase a (hUP ha),
    sourceAngularIntegrand,sourceAngularIntegrand,P.sourcePhase_prescribedRoot_neg a (hUP ha),
    ← sub_div,div_mul_eq_mul_div]
  congr 1
  exact (mul_comm _ _).trans hf

/-- The ORIGINAL physical differential is retained literally when the
H-minus-one source is the original even physical source. -/
theorem prescribedDifferential_eq_original (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val∈P.source)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k)=conj (P.miura.lift a k))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
    (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2) (n : ℕ+) (w E : ℂ) :
    P.prescribedDifferential n w (E,hillOriginalHminusSource q.val)=
      hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n n.pos E/
        prescribedSquareRoot (hillL2Radicand (SpectralWeight.one.toCoeff q.val)) w E := by
  rw [prescribedDifferential,
    congrFun (P.numerator_eq_original q hq hreal houtside c hshift n) E,
    hillHminusPrescribedRoot_original_source_agreement q.val q.property.1]

end NLS.KdV.HillHminusPsiChart
