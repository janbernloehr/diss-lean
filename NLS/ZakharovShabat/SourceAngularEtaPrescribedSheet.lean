import NLS.ZakharovShabat.SourceAngularEtaRemainderBoundary
import NLS.ZakharovShabat.SourceAngularGluedSheetPrimitive
import NLS.ComplexAnalysis.QuadraticRootPrimitive

/-!
# Model and remainder differentials on a prescribed eta root sheet

Dividing the prescribed full root by `2i` times the omitted product
gives a root of the selected endpoint polynomial. The diagonal model
and remainder split the literal angular differential on this sheet,
including at interior points of the canonical cut.
-/

noncomputable section
open Set Filter Topology Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAngularEtaSelectedSheetRoot (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (ψ : CoeffPair p) (w z : ℂ) : ℂ :=
  sourceAngularRootSheet hp w (z,ψ)/(2*I*sourceStandardRootOmittedProduct hp hp1 n ψ z)

def sourceAngularEtaModelSheetIntegrand (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (ψ : CoeffPair p) (w z : ℂ) : ℂ :=
  -(2*sourceStandardRootOmittedProduct hp hp1 n ψ z)/sourceAngularRootSheet hp w (z,ψ)

def sourceAngularEtaRemainderSheetIntegrand (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (ψ : CoeffPair p) (w z : ℂ) : ℂ :=
  (sourcePsiCandidate n (z,(s n ψ : Coeff p))+2*sourceStandardRootOmittedProduct hp hp1 n ψ z)/
    sourceAngularRootSheet hp w (z,ψ)

/-- Exact decomposition of the original psi/root differential. -/
theorem sourceAngularIntegrand_eq_eta_sheet_model_add_remainder
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) (w z : ℂ) :
    sourceAngularIntegrand n s (sourceAngularRootSheet hp w) (z,ψ) =
      sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w z+
        sourceAngularEtaRemainderSheetIntegrand hp hp1 n s ψ w z := by
  unfold sourceAngularIntegrand sourceAngularEtaModelSheetIntegrand sourceAngularEtaRemainderSheetIntegrand
  simp only [div_eq_mul_inv]
  ring

theorem sourceAngularEtaSelectedSheetRoot_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (w z : ℂ)
    (hw : w ≠ 0) (hz : (z,ψ) ∈ sourceAngularRootSheetDomain hp w)
    (hother : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sourceAngularEtaSelectedSheetRoot hp hp1 n ψ w z ≠ 0 :=
  div_ne_zero (sourceAngularRootSheet_ne_zero hp w hw (z,ψ) hz)
    (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z n hother))

/-- The selected square identity holds throughout the omitted-root
domain, also at the singular periodic endpoints outside the sheet slit. -/
theorem sourceAngularEtaSelectedSheetRoot_sq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (w z : ℂ)
    (hw : w ≠ 0) (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sourceAngularEtaSelectedSheetRoot hp hp1 n ψ w z^2 =
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z)*
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z) := by
  unfold sourceAngularEtaSelectedSheetRoot
  rw [div_pow,sourceAngularRootSheet_sq hp w hw]
  dsimp only [sourceAngularRadicand]
  rw [canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 _ (periodOnePotential_mem ψ) n z,
    ← sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct hp hp1 ψ n z hz]
  have hPne := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z n hz
  rw [mul_pow,mul_pow,I_sq]
  field_simp
  ring

theorem sourceAngularEtaSelectedSheetRoot_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (w : ℂ)
    (c : ℂ) (R : ℝ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ n) :
    AnalyticOnNhd ℂ (sourceAngularEtaSelectedSheetRoot hp hp1 n ψ w)
      (sourceAngularRegularSheetDisc hp ψ c R w) := by
  intro z hz
  have hD := hother (ball_subset_closedBall hz.1)
  exact ((analyticOnNhd_sourceAngularRootSheet hp hp1 w (z,ψ) hz.2).comp
    (f := fun u : ℂ => (u,ψ)) (analyticAt_id.prod analyticAt_const)).div
    (analyticAt_const.mul (hdata.analytic_omitted z hD))
    (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z n hD))

theorem sourceAngularEtaModelSheetIntegrand_eq_selectedRoot
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (w z : ℂ) :
    sourceAngularEtaModelSheetIntegrand hp hp1 n ψ w z =
      I/sourceAngularEtaSelectedSheetRoot hp hp1 n ψ w z := by
  unfold sourceAngularEtaModelSheetIntegrand sourceAngularEtaSelectedSheetRoot
  rw [div_div_eq_mul_div]
  have heq : I*(2*I*sourceStandardRootOmittedProduct hp hp1 n ψ z) =
      -(2*sourceStandardRootOmittedProduct hp hp1 n ψ z) := by
    calc
      _ = 2*(I*I)*sourceStandardRootOmittedProduct hp hp1 n ψ z := by ring
      _ = _ := by rw [I_mul_I]; ring
  rw [heq]

theorem sourceAngularEtaRemainderSheetIntegrand_eq_gapNumerator
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) (w z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sourceAngularEtaRemainderSheetIntegrand hp hp1 n s ψ w z =
      (sourceAngularGapNumerator hp hp1 n n s ψ z-I)/sourceAngularEtaSelectedSheetRoot hp hp1 n ψ w z := by
  have hK : 2*I*sourceStandardRootOmittedProduct hp hp1 n ψ z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z n hz)
  unfold sourceAngularEtaRemainderSheetIntegrand sourceAngularGapNumerator sourceAngularEtaSelectedSheetRoot
  rw [sub_div,div_div_div_cancel_right₀ hK,div_div_eq_mul_div]
  have heq : I*(2*I*sourceStandardRootOmittedProduct hp hp1 n ψ z) =
      -(2*sourceStandardRootOmittedProduct hp hp1 n ψ z) := by
    calc
      _ = 2*(I*I)*sourceStandardRootOmittedProduct hp hp1 n ψ z := by ring
      _ = _ := by rw [I_mul_I]; ring
  rw [heq]
  simp only [div_eq_mul_inv]
  ring

end NLS.ZakharovShabat
