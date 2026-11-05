import NLS.MKdV.MiuraFiniteRealActionProjection
import NLS.FunctionalAnalysis.RealAnalyticSubmersionSection

/-! # Real-preserving finite physical action sections

The actual real H1 action submersion has constructed real analytic
sections through every original real H1 base point, including zero mean.
Each section realizes the literal signed mean and physical Hill actions,
stays in any prescribed real H1 neighborhood and keeps all selected
actions positive. No independent global Birkhoff chart is assumed.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraFiniteRealActionCoordinates_pos (a : MiuraRealH1)
    (S : Finset (MiuraOpenActionIndex a.val a.property)) (n : S) :
    0 < miuraFiniteRealActionCoordinates a S a (some n) := by
  change 0 < (miuraL2Action n.val.val (scalarInclusion a.val)).re
  rw [miuraL2Action_eq_physical a.val a.property n.val.val n.val.property.1]
  have hJ := miuraMKdVAction_nonnegative_and_zero_iff a.val a.property n.val.val n.val.property.1
  have hn : (miuraMKdVAction a.val a.property n.val.val).re ≠ 0 := by
    intro hz
    exact n.val.property.2 (Complex.ext hz hJ.2.1)
  exact lt_of_le_of_ne hJ.1 hn.symm

theorem exists_miuraFiniteRealAction_section (a : MiuraRealH1)
    (S : Finset (MiuraOpenActionIndex a.val a.property))
    (U : Set MiuraRealH1) (hU : IsOpen U) (haU : a ∈ U) :
    ∃ R : (Option S → ℝ) →L[ℝ] MiuraRealH1,
      ∃ g : (Option S → ℝ) → MiuraRealH1, ∃ V : Set (Option S → ℝ),
        (fderiv ℝ (miuraFiniteRealActionCoordinates a S) a).comp R = ContinuousLinearMap.id ℝ (Option S → ℝ) ∧
        IsOpen V ∧ miuraFiniteRealActionCoordinates a S a ∈ V ∧
        AnalyticOnNhd ℝ g V ∧ g (miuraFiniteRealActionCoordinates a S a) = a ∧ MapsTo g V U ∧
        (∀ z ∈ V, (g z).val.val 0 = (z none : ℂ) ∧
          ∀ n : S, 0 < z (some n) ∧ miuraMKdVAction (g z).val (g z).property n.val.val = (z (some n) : ℂ)) ∧
        fderiv ℝ g (miuraFiniteRealActionCoordinates a S a) = R := by
  obtain ⟨R,hR⟩ := exists_miuraFiniteRealActionDerivative_rightInverse a S
  obtain ⟨g,V,hVo,hVa,hg,hga,hmem,hrec,hdg⟩ :=
    NLS.FunctionalAnalysis.exists_realAnalytic_section_of_derivative_rightInverse
      (miuraFiniteRealActionCoordinates a S) a (analyticAt_miuraFiniteRealActionCoordinates a S) R hR U hU haU
  let P : Set (Option S → ℝ) := {z | ∀ n : S, 0 < z (some n)}
  have hPo : IsOpen P := by
    change IsOpen {z : Option S → ℝ | ∀ n : S, 0 < z (some n)}
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite (fun n => isOpen_lt continuous_const (continuous_apply (some n)))
  have haP : miuraFiniteRealActionCoordinates a S a ∈ P :=
    fun n => miuraFiniteRealActionCoordinates_pos a S n
  refine ⟨R,g,V ∩ P,hR,hVo.inter hPo,⟨hVa,haP⟩,hg.mono inter_subset_left,hga,
    fun z hz => hmem hz.1,?_,hdg⟩
  intro z hz
  have hc (i : Option S) : miuraFiniteActionCoordinates a.val a.property S (g z).val i = (z i : ℂ) := by
    apply Complex.ext
    · exact congrFun (hrec z hz.1) i
    · exact finiteActionCoordinates_real_values a.val a.property S (g z).val (g z).property i
  refine ⟨hc none,?_⟩
  intro n
  refine ⟨hz.2 n,?_⟩
  have he := hc (some n)
  change miuraL2Action n.val.val (scalarInclusion (g z).val) = _ at he
  rw [miuraL2Action_eq_physical (g z).val (g z).property n.val.val n.val.property.1] at he
  exact he

end NLS.MKdV
