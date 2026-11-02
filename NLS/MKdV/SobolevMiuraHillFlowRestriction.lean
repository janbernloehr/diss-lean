import NLS.MKdV.SobolevMiuraHillHamiltonian
import NLS.ZakharovShabat.SobolevEvenHierarchyGradient
import NLS.Fourier.PeriodOneSobolevDistribution

/-! # Diagonal flow restriction on the full complex H^m domain

The two vector fields use actual Fréchet gradients represented by full
Sobolev duality. The scalar Hamiltonian was independently constructed from
the Hill Riccati density. Smooth physical equality and density give the
coefficient identity; Mathlib's genuine distribution derivative gives the
physical weak Gardner identity, including nonsmooth inputs.
-/
noncomputable section
open Complex NLS.Fourier NLS.ZakharovShabat
open scoped ContDiff SchwartzMap
namespace NLS.MKdV

def sobolevEvenHierarchyVectorField (m : ℕ) (hm : 1 ≤ m) (ab : SobolevSource m) :
    NegativeScalarSobolev m × NegativeScalarSobolev m :=
  (-I • (sobolevEvenHierarchyGradient m hm ab).2, I • (sobolevEvenHierarchyGradient m hm ab).1)

theorem analyticAt_sobolevEvenHierarchyVectorField (m : ℕ) (hm : 1 ≤ m) (ab : SobolevSource m) :
    AnalyticAt ℂ (sobolevEvenHierarchyVectorField m hm) ab := by
  have h1 := ((ContinuousLinearMap.fst ℂ (NegativeScalarSobolev m) (NegativeScalarSobolev m)).analyticAt
    (sobolevEvenHierarchyGradient m hm ab)).comp (analyticAt_sobolevEvenHierarchyGradient m hm ab)
  have h2 := ((ContinuousLinearMap.snd ℂ (NegativeScalarSobolev m) (NegativeScalarSobolev m)).analyticAt
    (sobolevEvenHierarchyGradient m hm ab)).comp (analyticAt_sobolevEvenHierarchyGradient m hm ab)
  exact (h2.const_smul (c := -I)).prod (h1.const_smul (c := I))

private theorem coefficient_const_mul (c : ℂ) (f : ℝ → ℂ) (n : ℤ) :
    periodOneCoefficient (fun x => c*f x) n = c*periodOneCoefficient f n := by
  change periodOneCoefficient (c • f) n = _
  rw [periodOneCoefficient, fourierCoeffOn.const_smul]
  rfl

/-- Every source input is in the exact H^m domain. The right side is the
physical derivative multiplier of the independently certified scalar gradient. -/
theorem sobolevMiuraHillFlowRestriction_coefficients (m : ℕ) (hm : 1 ≤ m)
    (u : ScalarSobolev m) (n : ℤ) :
    ((sobolevEvenHierarchyVectorField m hm (u,u)).1.val n,
      (sobolevEvenHierarchyVectorField m hm (u,u)).2.val n) =
      (2*I*(Real.pi : ℂ)*n*(sobolevMiuraHillGradient m hm u).val n,
        2*I*(Real.pi : ℂ)*n*(sobolevMiuraHillGradient m hm u).val n) := by
  let E : NegativeScalarSobolev m →L[ℂ] ℂ := WeightedCoeff.evalCLM _ 2 n
  have hV : Continuous (fun v : ScalarSobolev m => sobolevEvenHierarchyVectorField m hm (v,v)) :=
    (continuous_iff_continuousAt.mpr (fun ab =>
      (analyticAt_sobolevEvenHierarchyVectorField m hm ab).continuousAt)).comp
      (hierarchyDiagonal m).continuous
  have hK : Continuous (sobolevMiuraHillGradient m hm) :=
    continuous_iff_continuousAt.mpr (fun v => (analyticAt_sobolevMiuraHillGradient m hm v).continuousAt)
  have hF : Continuous (fun v : ScalarSobolev m =>
      ((sobolevEvenHierarchyVectorField m hm (v,v)).1.val n,
        (sobolevEvenHierarchyVectorField m hm (v,v)).2.val n)) :=
    (E.continuous.comp (continuous_fst.comp hV)).prodMk (E.continuous.comp (continuous_snd.comp hV))
  have hG : Continuous (fun v : ScalarSobolev m =>
      (2*I*(Real.pi : ℂ)*n*(sobolevMiuraHillGradient m hm v).val n,
        2*I*(Real.pi : ℂ)*n*(sobolevMiuraHillGradient m hm v).val n)) :=
    (continuous_const.mul (E.continuous.comp hK)).prodMk
      (continuous_const.mul (E.continuous.comp hK))
  have he := (WeightedCoeff.denseRange_ofFinsupp (Weight.sobolev (m : ℝ)) 2 (by simp)).equalizer hF hG (by
    funext a
    let v : ScalarSobolev m := WeightedCoeff.ofFinsupp _ 2 a
    let f := polynomial a
    have hf : ContDiff ℝ ∞ f := contDiff_source_polynomial a
    have hp : Function.Periodic f 1 := periodic_source_polynomial a
    have hc (j : ℤ) : v.val j = periodOneCoefficient f j := by
      simp only [v, f, WeightedCoeff.ofFinsupp_apply, periodOneCoefficient_source_polynomial]
    have hn := sobolevEvenHierarchyGradient_eq_classical m hm (v,v) f f hf hf hp hp hc hc n
    have hk := sobolevMiuraHillGradient_eq_classical m hm v f hf hp hc n
    have hflow (x : ℝ) :
        (-I*(classicalNLSHierarchyGradient f f (2*m) x).2,
          I*(classicalNLSHierarchyGradient f f (2*m) x).1) =
          (deriv (classicalMiuraHillGradient f m) x, deriv (classicalMiuraHillGradient f m) x) := by
      obtain ⟨r,hr⟩ : ∃ r, m = r+1 := ⟨m-1, by omega⟩
      rw [hr, show 2*(r+1) = 2*r+2 by omega]
      exact classicalNLSHierarchyVectorField_even_diagonal f hf hp r x
    have h1 : (fun x => -I*(classicalNLSHierarchyGradient f f (2*m) x).2) =
        deriv (classicalMiuraHillGradient f m) := funext (fun x => congrArg Prod.fst (hflow x))
    have h2 : (fun x => I*(classicalNLSHierarchyGradient f f (2*m) x).1) =
        deriv (classicalMiuraHillGradient f m) := funext (fun x => congrArg Prod.snd (hflow x))
    have hd1 := congrArg (fun g : ℝ → ℂ => periodOneCoefficient g n) h1
    have hd2 := congrArg (fun g : ℝ → ℂ => periodOneCoefficient g n) h2
    rw [coefficient_const_mul, periodOneCoefficient_deriv_of_smooth_periodic _
      (contDiff_classicalMiuraHillGradient f hf m) (periodic_classicalMiuraHillGradient f hp m)] at hd1 hd2
    change (-I*(sobolevEvenHierarchyGradient m hm (v,v)).2.val n,
      I*(sobolevEvenHierarchyGradient m hm (v,v)).1.val n) = _
    exact Prod.ext
      (((congrArg (fun z : ℂ => -I*z) (congrArg Prod.snd hn)).trans hd1).trans
        (congrArg (fun z : ℂ => 2*I*(Real.pi : ℂ)*n*z) hk.symm))
      (((congrArg (fun z : ℂ => I*z) (congrArg Prod.fst hn)).trans hd2).trans
        (congrArg (fun z : ℂ => 2*I*(Real.pi : ℂ)*n*z) hk.symm)))
  exact congrFun he u

def sobolevMiuraHillVectorField (m : ℕ) (hm : 1 ≤ m) (u : ScalarSobolev m) : 𝓢'(ℝ,ℂ) :=
  TemperedDistribution.derivCLM ℂ
    (periodOneSobolevDistribution (-(m : ℝ)) (sobolevMiuraHillGradient m hm u))

/-- The full complex H^m flow identity uses actual physical distributions.
In particular its scalar derivative is represented at order -m by each
NLS field component, rather than being only a formal Fourier expression. -/
theorem sobolevMiuraHillFlowRestriction (m : ℕ) (hm : 1 ≤ m) (u : ScalarSobolev m) :
    (periodOneSobolevDistribution (-(m : ℝ)) (sobolevEvenHierarchyVectorField m hm (u,u)).1,
      periodOneSobolevDistribution (-(m : ℝ)) (sobolevEvenHierarchyVectorField m hm (u,u)).2) =
        (sobolevMiuraHillVectorField m hm u, sobolevMiuraHillVectorField m hm u) := by
  apply Prod.ext
  · symm
    exact periodOneSobolevDistribution_derivative_eq _ _ _ _
      (fun n => congrArg Prod.fst (sobolevMiuraHillFlowRestriction_coefficients m hm u n))
  · symm
    exact periodOneSobolevDistribution_derivative_eq _ _ _ _
      (fun n => congrArg Prod.snd (sobolevMiuraHillFlowRestriction_coefficients m hm u n))

end NLS.MKdV
