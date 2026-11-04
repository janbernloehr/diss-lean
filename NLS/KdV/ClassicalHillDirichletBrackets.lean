import NLS.KdV.HillDirichletLagrange

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

theorem classicalHill_dirichlet_squared_pairing_zero
    (q : Curve ℂ) (a b : ℂ) (hab : a≠b)
    (ha : (classicalHillFlow q a (0,1) 1).1=0)
    (hb : (classicalHillFlow q b (0,1) 1).1=0) :
    (∫ x in (0 : ℝ)..1, (classicalHillFlow q a (0,1) x).1^2*
      (classicalHillFlow q b (0,1) x).1*(classicalHillFlow q b (0,1) x).2)=0 := by
  let A := classicalHillFlow q a (0,1)
  let B := classicalHillFlow q b (0,1)
  let W (x : ℝ) := (A x).1*(B x).2-(A x).2*(B x).1
  let P (x : ℝ) := (A x).1^2*(B x).1*(B x).2
  let Q (x : ℝ) := (A x).1*(A x).2*(B x).1^2
  have hA : Continuous A := continuous_classicalHillFlow q a (0,1)
  have hB : Continuous B := continuous_classicalHillFlow q b (0,1)
  have hP : Continuous P := by dsimp [P];fun_prop
  have hQ : Continuous Q := by dsimp [Q];fun_prop
  have hAf (t : Icc (0 : ℝ) 1) : HasDerivAt (fun x : ℝ => (A x).1) (A t).2 t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q a (0,1) t).fst
  have hAg (t : Icc (0 : ℝ) 1) : HasDerivAt (fun x : ℝ => (A x).2) ((q t-a)*(A t).1) t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q a (0,1) t).snd
  have hBf (t : Icc (0 : ℝ) 1) : HasDerivAt (fun x : ℝ => (B x).1) (B t).2 t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (0,1) t).fst
  have hBg (t : Icc (0 : ℝ) 1) : HasDerivAt (fun x : ℝ => (B x).2) ((q t-b)*(B t).1) t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q b (0,1) t).snd
  have hWd (t : Icc (0 : ℝ) 1) : HasDerivAt W ((a-b)*(A t).1*(B t).1) t.val := by
    convert! ((hAf t).mul (hBg t)).sub ((hAg t).mul (hBf t)) using 1
    ring
  have hWWd (t : Icc (0 : ℝ) 1) : HasDerivAt (fun x : ℝ => W x^2)
      (2*(a-b)*(P t-Q t)) t.val := by
    convert! (hWd t).pow 2 using 1
    dsimp [W,P,Q]
    ring
  have hSSd (t : Icc (0 : ℝ) 1) : HasDerivAt (fun x : ℝ => (A x).1^2*(B x).1^2)
      (2*(P t+Q t)) t.val := by
    convert! ((hAf t).pow 2).mul ((hBf t).pow 2) using 1
    dsimp [P,Q]
    ring
  have hWWc : Continuous (fun x : ℝ => W x^2) := by dsimp [W];fun_prop
  have hSSc : Continuous (fun x : ℝ => (A x).1^2*(B x).1^2) := by fun_prop
  have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ)≤1)
    hWWc.continuousOn (fun x (hx : x∈Ioo (0 : ℝ) 1) => hWWd ⟨x,hx.1.le,hx.2.le⟩)
    ((continuous_const.mul (hP.sub hQ)).intervalIntegrable 0 1)
  have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ)≤1)
    hSSc.continuousOn (fun x (hx : x∈Ioo (0 : ℝ) 1) => hSSd ⟨x,hx.1.le,hx.2.le⟩)
    ((continuous_const.mul (hP.add hQ)).intervalIntegrable 0 1)
  change (∫ x in (0 : ℝ)..1,2*(a-b)*(P x-Q x))=W 1^2-W 0^2 at h1
  change (∫ x in (0 : ℝ)..1,2*(P x+Q x))=(A 1).1^2*(B 1).1^2-(A 0).1^2*(B 0).1^2 at h2
  simp only [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub (hP.intervalIntegrable 0 1) (hQ.intervalIntegrable 0 1),
    intervalIntegral.integral_add (hP.intervalIntegrable 0 1) (hQ.intervalIntegrable 0 1)] at h1 h2
  have h1' : 2*(a-b)*((∫ x in (0 : ℝ)..1,P x)-(∫ x in (0 : ℝ)..1,Q x))=0 := by
    simpa [W,A,B,ha,hb,classicalHillFlow_zero] using h1
  have h2' : 2*((∫ x in (0 : ℝ)..1,P x)+(∫ x in (0 : ℝ)..1,Q x))=0 := by
    simpa [A,B,ha,hb,classicalHillFlow_zero] using h2
  have hdiff : (∫ x in (0 : ℝ)..1,P x)-(∫ x in (0 : ℝ)..1,Q x)=0 :=
    (mul_eq_zero.mp h1').resolve_left (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hab))
  change (∫ x in (0 : ℝ)..1,P x)=0
  linear_combination hdiff/2+h2'/4

end NLS.KdV
