import NLS.MKdV.HierarchyGradientRecurrence
import NLS.ZakharovShabat.SobolevHierarchyGradientSymmetries

/-! # The corrected hierarchy recurrence on the original Sobolev domain -/
noncomputable section
open Complex NLS.Fourier NLS.ZakharovShabat
namespace NLS.MKdV

private theorem coefficient_const_mul (c : ℂ) (f : ℝ → ℂ) (j : ℤ) :
    periodOneCoefficient (fun x => c*f x) j = c*periodOneCoefficient f j := by
  change periodOneCoefficient (c • f) j = _
  rw [periodOneCoefficient, fourierCoeffOn.const_smul]
  rfl

/-- The physical 2*pi*i*j recurrence holds for every complex diagonal H^(2m+1)
source, including nonsmooth inputs. -/
theorem sobolevHierarchyGradient_diagonal_recurrence (m : ℕ) (u : ScalarSobolev (2*m+1)) (j : ℤ) :
    (I*(sobolevNLSHierarchyGradient (2*m+1) (2*m+2) (u,u)).1 j,
      -I*(sobolevNLSHierarchyGradient (2*m+1) (2*m+2) (u,u)).2 j) =
      ((2*I*(Real.pi : ℂ)*j)*(sobolevNLSHierarchyGradient (2*m+1) (2*m+1) (u,u)).1 j,
        (2*I*(Real.pi : ℂ)*j)*(sobolevNLSHierarchyGradient (2*m+1) (2*m+1) (u,u)).2 j) := by
  let V (k : ℕ) (v : ScalarSobolev (2*m+1)) := sobolevNLSHierarchyGradient (2*m+1) k (v,v)
  have hV (k : ℕ) : Continuous (V k) :=
    (continuous_iff_continuousAt.mpr (fun cd =>
      (analyticAt_sobolevNLSHierarchyGradient (2*m+1) k cd).continuousAt)).comp
        (continuous_id.prodMk continuous_id)
  let e := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j
  have hF : Continuous (fun v => (I*(V (2*m+2) v).1 j,-I*(V (2*m+2) v).2 j)) :=
    (continuous_const.mul (e.continuous.comp (hV _).fst)).prodMk
      (continuous_const.mul (e.continuous.comp (hV _).snd))
  have hG : Continuous (fun v => ((2*I*(Real.pi : ℂ)*j)*(V (2*m+1) v).1 j,
      (2*I*(Real.pi : ℂ)*j)*(V (2*m+1) v).2 j)) :=
    (continuous_const.mul (e.continuous.comp (hV _).fst)).prodMk
      (continuous_const.mul (e.continuous.comp (hV _).snd))
  have he := (WeightedCoeff.denseRange_ofFinsupp (Weight.sobolev ((2*m+1 : ℕ) : ℝ)) 2 (by simp)).equalizer
    hF hG (by
      funext c
      let a := WeightedCoeff.ofFinsupp (Weight.sobolev ((2*m+1 : ℕ) : ℝ)) 2 c
      let f := polynomial c
      have hf := contDiff_source_polynomial c
      have hp := periodic_source_polynomial c
      have hq (n : ℤ) : a.val n = periodOneCoefficient f n := by
        simp [a, f]
      have hE := sobolevNLSHierarchyGradient_eq_classical (2*m+1) (2*m+2) (by omega)
        (a,a) f f hf hf hp hp hq hq j
      have hO := sobolevNLSHierarchyGradient_eq_classical (2*m+1) (2*m+1) (by omega)
        (a,a) f f hf hf hp hp hq hq j
      have hE1 : (V (2*m+2) a).1 j = periodOneCoefficient
          (fun x => (classicalNLSHierarchyGradient f f (2*m+2) x).1) j := congrArg Prod.fst hE
      have hE2 : (V (2*m+2) a).2 j = periodOneCoefficient
          (fun x => (classicalNLSHierarchyGradient f f (2*m+2) x).2) j := congrArg Prod.snd hE
      have hO1 : (V (2*m+1) a).1 j = periodOneCoefficient
          (fun x => (classicalNLSHierarchyGradient f f (2*m+1) x).1) j := congrArg Prod.fst hO
      have hO2 : (V (2*m+1) a).2 j = periodOneCoefficient
          (fun x => (classicalNLSHierarchyGradient f f (2*m+1) x).2) j := congrArg Prod.snd hO
      have hs := classicalHierarchyGradient_diagonal_recurrence f hf hp m
      have hs1 : (fun x => I*(classicalNLSHierarchyGradient f f (2*m+2) x).1) =
          deriv (fun x => (classicalNLSHierarchyGradient f f (2*m+1) x).1) :=
        funext (fun x => congrArg Prod.fst (hs x))
      have hs2 : (fun x => -I*(classicalNLSHierarchyGradient f f (2*m+2) x).2) =
          deriv (fun x => (classicalNLSHierarchyGradient f f (2*m+1) x).2) :=
        funext (fun x => congrArg Prod.snd (hs x))
      have hc := contDiff_classicalNLSHierarchyGradient f f hf hf (2*m+1)
      have hper := periodic_classicalNLSHierarchyGradient f f hp hp (2*m+1)
      have he1 := congrArg (fun g => periodOneCoefficient g j) hs1
      have he2 := congrArg (fun g => periodOneCoefficient g j) hs2
      rw [coefficient_const_mul, periodOneCoefficient_deriv_of_smooth_periodic _ hc.fst
        (fun x => congrArg Prod.fst (hper x))] at he1
      rw [coefficient_const_mul, periodOneCoefficient_deriv_of_smooth_periodic _ hc.snd
        (fun x => congrArg Prod.snd (hper x))] at he2
      change (I*(V (2*m+2) a).1 j,-I*(V (2*m+2) a).2 j) =
        ((2*I*(Real.pi : ℂ)*j)*(V (2*m+1) a).1 j,
          (2*I*(Real.pi : ℂ)*j)*(V (2*m+1) a).2 j)
      rw [hE1, hE2, hO1, hO2]
      exact Prod.ext he1 he2)
  exact congrFun he u

/-- Nonzero proportional components reduce to the diagonal by a reciprocal
scaling. This stronger complex statement includes every source phase condition. -/
theorem sobolevHierarchyGradient_proportional_recurrence (m : ℕ)
    (ab : SobolevSource (2*m+1)) (d : ℂ) (hd : d ≠ 0) (hab : ab.2 = (d*d) • ab.1) (j : ℤ) :
    (I*(sobolevNLSHierarchyGradient (2*m+1) (2*m+2) ab).1 j,
      -I*(sobolevNLSHierarchyGradient (2*m+1) (2*m+2) ab).2 j) =
      ((2*I*(Real.pi : ℂ)*j)*(sobolevNLSHierarchyGradient (2*m+1) (2*m+1) ab).1 j,
        (2*I*(Real.pi : ℂ)*j)*(sobolevNLSHierarchyGradient (2*m+1) (2*m+1) ab).2 j) := by
  let u := d • ab.1
  have he : ab = hierarchyReciprocalScaling (2*m+1) d⁻¹ (u,u) := by
    simp only [hierarchyReciprocalScaling_apply, u, inv_inv, smul_smul, inv_mul_cancel₀ hd, one_smul]
    exact Prod.ext rfl hab
  have hE := sobolevNLSHierarchyGradient_reciprocal_scaling (2*m+1) (2*m+2) (by omega)
    (u,u) d⁻¹ (inv_ne_zero hd)
  have hO := sobolevNLSHierarchyGradient_reciprocal_scaling (2*m+1) (2*m+1) (by omega)
    (u,u) d⁻¹ (inv_ne_zero hd)
  rw [he, hE, hO]
  simp only [inv_inv, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  have h := sobolevHierarchyGradient_diagonal_recurrence m u j
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  apply Prod.ext
  · dsimp only at h1 ⊢
    linear_combination d*h1
  · dsimp only at h2 ⊢
    linear_combination d⁻¹*h2

end NLS.MKdV
