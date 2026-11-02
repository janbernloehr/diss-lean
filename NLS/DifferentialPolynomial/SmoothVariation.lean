import NLS.DifferentialPolynomial.EulerLagrange
import NLS.DifferentialPolynomial.PolynomialVariation
import NLS.FunctionalAnalysis.UnitIntervalMean
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Physical first variations of periodic differential-polynomial integrals

Differentiation takes place in the Banach algebra of continuous curves. Its
bounded complex-linear integral commutes with differentiation; the Euler
formula then follows by repeated periodic integration by parts.
-/
noncomputable section
open MvPolynomial Set MeasureTheory
open scoped ContDiff
namespace NLS.DifferentialPolynomial
open NLS.LinearVolterra

/-- Restrict a continuous physical field to the closed unit interval. -/
def fieldCurve (f : ℝ → ℂ) (hf : Continuous f) : Curve ℂ :=
  ⟨fun x => f x, hf.comp continuous_subtype_val⟩

theorem unitIntervalMean_fieldCurve (f : ℝ → ℂ) (hf : Continuous f) :
    unitIntervalMean (fieldCurve f hf) = ∫ x in (0 : ℝ)..1, f x := by
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
  change f (projIcc 0 1 (by norm_num) x) = f x
  rw [projIcc_of_mem (by norm_num) hx']

/-- Each physical jet is a continuous curve. -/
def jetCurve (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (v : Jet) : Curve ℂ :=
  fieldCurve (iteratedDeriv v.2 (if v.1 then b else a))
    (NLS.FunctionalAnalysis.contDiff_iteratedDeriv _ (by split <;> assumption) v.2).continuous

@[simp] theorem jetCurve_apply (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (v : Jet) (x : Icc (0 : ℝ) 1) :
    jetCurve a b ha hb v x = iteratedDeriv v.2 (if v.1 then b else a) x := rfl

theorem aeval_jetCurve (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (p : Polynomial) :
    MvPolynomial.aeval (jetCurve a b ha hb) p =
      fieldCurve (evaluate a b p) (continuous_evaluate a b ha hb p) := by
  ext x
  have he := MvPolynomial.comp_aeval_apply (f := jetCurve a b ha hb)
    (ContinuousMap.evalAlgHom ℂ ℂ x) p
  simpa only [ContinuousMap.evalAlgHom_apply, jetCurve_apply, aeval_eq_eval, evaluate,
    fieldCurve, ContinuousMap.coe_mk] using he

theorem iteratedDeriv_affine (f h : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hh : ContDiff ℝ ∞ h) (z : ℂ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun t => f t + z*h t) x =
      iteratedDeriv n f x + z*iteratedDeriv n h x := by
  have hs : ContDiff ℝ ∞ (fun t => z*h t) := contDiff_const.mul hh
  rw [iteratedDeriv_fun_add (contDiff_infty.mp hf n).contDiffAt
    (contDiff_infty.mp hs n).contDiffAt]
  congr 1
  exact iteratedDeriv_fun_const_smul_field z h

/-- Actual complex first variation of any smooth differential-polynomial
integral, before moving derivatives off the variation. -/
theorem hasDerivAt_integral_evaluate (a b h k : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hh : ContDiff ℝ ∞ h) (hk : ContDiff ℝ ∞ k) (p : Polynomial) :
    HasDerivAt (fun z : ℂ => ∫ x in (0 : ℝ)..1,
      evaluate (fun t => a t + z*h t) (fun t => b t + z*k t) p x)
      (∫ x in (0 : ℝ)..1, firstVariationDensity a b h k p x) 0 := by
  classical
  let A := jetCurve a b ha hb
  let V := jetCurve h k hh hk
  have hc (v : Jet) : HasDerivAt (fun z : ℂ => A v + z • V v) (V v) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const (V v) |>.const_add (A v)
  have hp := hasDerivAt_aeval_mvPolynomial (fun z v => A v + z • V v) V 0 hc p
  have hm := (unitIntervalMean (E := ℂ)).hasFDerivAt.comp_hasDerivAt 0 hp
  have he (z : ℂ) : MvPolynomial.aeval (fun v => A v + z • V v) p =
      fieldCurve
        (evaluate (fun t => a t + z*h t) (fun t => b t + z*k t) p)
        (continuous_evaluate _ _ (ha.add (contDiff_const.mul hh))
          (hb.add (contDiff_const.mul hk)) p) := by
    rw [← aeval_jetCurve _ _ (ha.add (contDiff_const.mul hh))
      (hb.add (contDiff_const.mul hk)) p]
    apply congrArg (fun f : Jet → Curve ℂ => MvPolynomial.aeval f p)
    funext v
    ext x
    simp only [A, V, jetCurve_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      smul_eq_mul]
    cases v.1
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (iteratedDeriv_affine a h ha hh z v.2 x).symm
    · simp only [↓reduceIte]
      exact (iteratedDeriv_affine b k hb hk z v.2 x).symm
  have hd : (∑ v ∈ p.vars, V v * MvPolynomial.aeval (fun i => A i + (0 : ℂ) • V i) (pderiv v p)) =
      fieldCurve (firstVariationDensity a b h k p)
        (by
          unfold firstVariationDensity
          exact continuous_finsetSum _ (fun v _ =>
            (NLS.FunctionalAnalysis.contDiff_iteratedDeriv _ (by split <;> assumption) v.2).continuous.mul
              (continuous_evaluate a b ha hb _))) := by
    have hz : (fun i => A i + (0 : ℂ) • V i) = A := by
      funext i
      ext x
      simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul, zero_mul, add_zero]
    rw [hz]
    ext x
    simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply, A, V,
      aeval_jetCurve, fieldCurve, ContinuousMap.coe_mk, firstVariationDensity, jetCurve_apply]
  simpa only [Function.comp_def, he, unitIntervalMean_fieldCurve, hd] using hm

/-- The two formal Euler derivatives are the physical variational gradients
for every smooth complex period-one pair and every smooth periodic variation. -/
theorem hasDerivAt_integral_evaluate_euler (a b h k : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hh : ContDiff ℝ ∞ h) (hk : ContDiff ℝ ∞ k)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hph : Function.Periodic h 1) (hpk : Function.Periodic k 1) (p : Polynomial) :
    HasDerivAt (fun z : ℂ => ∫ x in (0 : ℝ)..1,
      evaluate (fun t => a t + z*h t) (fun t => b t + z*k t) p x)
      (∫ x in (0 : ℝ)..1, h x * evaluate a b (eulerDerivative false p) x +
        k x * evaluate a b (eulerDerivative true p) x) 0 := by
  rw [← integral_firstVariationDensity a b h k ha hb hh hk hpa hpb hph hpk]
  exact hasDerivAt_integral_evaluate a b h k ha hb hh hk p

end NLS.DifferentialPolynomial
