import NLS.ZakharovShabat.NLSHierarchyReflectionNonlocal

/-! # The genuine integral graph of the smooth reflected Lenard recurrence -/
noncomputable section
open Complex MeasureTheory NLS.DifferentialPolynomial
open scoped ContDiff
namespace NLS.ZakharovShabat

theorem continuous_classicalNLSHierarchyRPairing (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (k : ℕ) :
    Continuous (classicalNLSHierarchyRPairing a b k) := by
  have hg := (contDiff_classicalNLSHierarchyGradient a b ha hb k).continuous
  exact ((continuous_const.mul ha.continuous).mul hg.fst).add
    ((continuous_const.mul hb.continuous).mul hg.snd)

theorem classicalNLSHierarchyGradient_reflection_integral
    (ε : ℂ) (hε : ε=1 ∨ ε = -1) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hTa : ∀ x, ε*a (1-x)=a x) (hTb : ∀ x, ε*b (1-x)=b x) (m : ℕ) (x : ℝ) :
    ((classicalNLSHierarchyGradient a b (2*m+1) x).1-(classicalNLSHierarchyGradient a b (2*m+1) 0).1,
     (classicalNLSHierarchyGradient a b (2*m+1) x).2-(classicalNLSHierarchyGradient a b (2*m+1) 0).2) =
      (I*(∫ y in (0:ℝ)..x, (classicalNLSHierarchyGradient a b (2*m+2) y).1)-
        (2*I)*(∫ y in (0:ℝ)..x, b y*(∫ z in (0:ℝ)..y, classicalNLSHierarchyRPairing a b (2*m+1) z)),
       -I*(∫ y in (0:ℝ)..x, (classicalNLSHierarchyGradient a b (2*m+2) y).2)-
        (2*I)*(∫ y in (0:ℝ)..x, -(a y*(∫ z in (0:ℝ)..y, classicalNLSHierarchyRPairing a b (2*m+1) z)))) := by
  let P := fun y => ∫ z in (0:ℝ)..y, classicalNLSHierarchyRPairing a b (2*m+1) z
  have hR := continuous_classicalNLSHierarchyRPairing a b ha hb (2*m+1)
  have hP : Continuous P := continuous_iff_continuousAt.mpr fun y =>
    (intervalIntegral.integral_hasDerivAt_right (hR.intervalIntegrable 0 y)
      hR.stronglyMeasurable.stronglyMeasurableAtFilter hR.continuousAt).continuousAt
  have hE := (contDiff_classicalNLSHierarchyGradient a b ha hb (2*m+2)).continuous
  have hi₁ : IntervalIntegrable (fun y => I*(classicalNLSHierarchyGradient a b (2*m+2) y).1) volume 0 x :=
    (continuous_const.mul hE.fst).intervalIntegrable 0 x
  have hi₂ : IntervalIntegrable (fun y => -I*(classicalNLSHierarchyGradient a b (2*m+2) y).2) volume 0 x :=
    (continuous_const.mul hE.snd).intervalIntegrable 0 x
  have hN₁ : IntervalIntegrable (fun y => (2*I)*(b y*P y)) volume 0 x :=
    (continuous_const.mul (hb.continuous.mul hP)).intervalIntegrable 0 x
  have hN₂ : IntervalIntegrable (fun y => (2*I)*(-(a y*P y))) volume 0 x :=
    (continuous_const.mul (ha.continuous.mul hP).neg).intervalIntegrable 0 x
  have hd₁ (y : ℝ) : HasDerivAt (fun z => (classicalNLSHierarchyGradient a b (2*m+1) z).1)
      (I*(classicalNLSHierarchyGradient a b (2*m+2) y).1-(2*I)*(b y*P y)) y := by
    have hd := (hasDerivAt_evaluate a b ha hb
      (eulerDerivative false (nlsHamiltonianPolynomial (2*m+1))) y).differentiableAt.hasDerivAt
    change HasDerivAt (fun z => (classicalNLSHierarchyGradient a b (2*m+1) z).1)
      (deriv (fun z => (classicalNLSHierarchyGradient a b (2*m+1) z).1) y) y at hd
    have he := congrArg Prod.fst
      (classicalNLSHierarchyGradient_reflection_nonlocal ε hε a b ha hb hpa hpb hTa hTb m y)
    dsimp only at he
    convert! hd using 1
    dsimp only [P]
    linear_combination he
  have hd₂ (y : ℝ) : HasDerivAt (fun z => (classicalNLSHierarchyGradient a b (2*m+1) z).2)
      (-I*(classicalNLSHierarchyGradient a b (2*m+2) y).2-(2*I)*(-(a y*P y))) y := by
    have hd := (hasDerivAt_evaluate a b ha hb
      (eulerDerivative true (nlsHamiltonianPolynomial (2*m+1))) y).differentiableAt.hasDerivAt
    change HasDerivAt (fun z => (classicalNLSHierarchyGradient a b (2*m+1) z).2)
      (deriv (fun z => (classicalNLSHierarchyGradient a b (2*m+1) z).2) y) y at hd
    have he := congrArg Prod.snd
      (classicalNLSHierarchyGradient_reflection_nonlocal ε hε a b ha hb hpa hpb hTa hTb m y)
    dsimp only at he
    convert! hd using 1
    dsimp only [P]
    linear_combination he
  have h₁ := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd₁ y) (hi₁.sub hN₁)
  have h₂ := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd₂ y) (hi₂.sub hN₂)
  rw [intervalIntegral.integral_sub hi₁ hN₁,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h₁
  rw [intervalIntegral.integral_sub hi₂ hN₂,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h₂
  exact Prod.ext h₁.symm h₂.symm

end NLS.ZakharovShabat
