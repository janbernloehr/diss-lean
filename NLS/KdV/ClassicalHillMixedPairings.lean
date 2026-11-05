import NLS.KdV.ClassicalHillDirichletBrackets

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

theorem classicalHill_dirichlet_mixed_pairing_zero_of_ne
    (q : Curve ℂ) (a b : ℂ) (hab : a≠b)
    (ha : (classicalHillFlow q a (0,1) 1).1=0)
    (hb : (classicalHillFlow q b (0,1) 1).1=0) :
    (∫ x in (0 : ℝ)..1, (classicalHillFlow q a (0,1) x).1^2*
      ((classicalHillFlow q b (1,0) x).2*(classicalHillFlow q b (0,1) x).1+
        (classicalHillFlow q b (1,0) x).1*(classicalHillFlow q b (0,1) x).2))=0 := by
  let A := classicalHillFlow q a (0,1)
  let C := classicalHillFlow q b (1,0)
  let S := classicalHillFlow q b (0,1)
  let Wc (x : ℝ) := (A x).1*(C x).2-(A x).2*(C x).1
  let Ws (x : ℝ) := (A x).1*(S x).2-(A x).2*(S x).1
  let P (x : ℝ) := (A x).1^2*((C x).2*(S x).1+(C x).1*(S x).2)
  let Q (x : ℝ) := 2*(A x).1*(A x).2*(C x).1*(S x).1
  have hcont (e : ℂ) (v : ℂ × ℂ) : Continuous (classicalHillFlow q e v) := continuous_classicalHillFlow q e v
  have hf (e : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
      HasDerivAt (fun x : ℝ => (classicalHillFlow q e v x).1) (classicalHillFlow q e v t).2 t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q e v t).fst
  have hg (e : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
      HasDerivAt (fun x : ℝ => (classicalHillFlow q e v x).2)
        ((q t-e)*(classicalHillFlow q e v t).1) t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q e v t).snd
  have hWc (t : Icc (0 : ℝ) 1) : HasDerivAt Wc ((a-b)*(A t).1*(C t).1) t.val := by
    convert! ((hf a (0,1) t).mul (hg b (1,0) t)).sub ((hg a (0,1) t).mul (hf b (1,0) t)) using 1
    ring
  have hWs (t : Icc (0 : ℝ) 1) : HasDerivAt Ws ((a-b)*(A t).1*(S t).1) t.val := by
    convert! ((hf a (0,1) t).mul (hg b (0,1) t)).sub ((hg a (0,1) t).mul (hf b (0,1) t)) using 1
    ring
  have hprodW (t : Icc (0 : ℝ) 1) : HasDerivAt (fun x : ℝ => Wc x*Ws x)
      ((a-b)*(P t-Q t)) t.val := by
    convert! (hWc t).mul (hWs t) using 1
    dsimp [Wc,Ws,P,Q]
    ring
  have hprodS (t : Icc (0 : ℝ) 1) : HasDerivAt
      (fun x : ℝ => (A x).1^2*(C x).1*(S x).1) (P t+Q t) t.val := by
    convert! (((hf a (0,1) t).pow 2).mul (hf b (1,0) t)).mul (hf b (0,1) t) using 1
    dsimp [P,Q]
    ring
  have hP : Continuous P := by dsimp [P,A,C,S];fun_prop
  have hQ : Continuous Q := by dsimp [Q,A,C,S];fun_prop
  have hWcont : Continuous (fun x : ℝ => Wc x*Ws x) := by dsimp [Wc,Ws,A,C,S];fun_prop
  have hScont : Continuous (fun x : ℝ => (A x).1^2*(C x).1*(S x).1) := by dsimp [A,C,S];fun_prop
  have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ)≤1)
    hWcont.continuousOn (fun x (hx : x∈Ioo (0 : ℝ) 1) => hprodW ⟨x,hx.1.le,hx.2.le⟩)
    ((continuous_const.mul (hP.sub hQ)).intervalIntegrable 0 1)
  have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ)≤1)
    hScont.continuousOn (fun x (hx : x∈Ioo (0 : ℝ) 1) => hprodS ⟨x,hx.1.le,hx.2.le⟩)
    ((hP.add hQ).intervalIntegrable 0 1)
  change (∫ x in (0 : ℝ)..1,(a-b)*(P x-Q x))=Wc 1*Ws 1-Wc 0*Ws 0 at h1
  change (∫ x in (0 : ℝ)..1,P x+Q x)=(A 1).1^2*(C 1).1*(S 1).1-(A 0).1^2*(C 0).1*(S 0).1 at h2
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub (hP.intervalIntegrable 0 1) (hQ.intervalIntegrable 0 1)] at h1
  rw [intervalIntegral.integral_add (hP.intervalIntegrable 0 1) (hQ.intervalIntegrable 0 1)] at h2
  have h1' : (a-b)*((∫ x in (0 : ℝ)..1,P x)-(∫ x in (0 : ℝ)..1,Q x))=0 := by
    simpa [Wc,Ws,A,C,S,ha,hb,classicalHillFlow_zero] using h1
  have h2' : (∫ x in (0 : ℝ)..1,P x)+(∫ x in (0 : ℝ)..1,Q x)=0 := by
    simpa [A,C,S,ha,hb,classicalHillFlow_zero] using h2
  have hdiff : (∫ x in (0 : ℝ)..1,P x)-(∫ x in (0 : ℝ)..1,Q x)=0 :=
    (mul_eq_zero.mp h1').resolve_left (sub_ne_zero.mpr hab)
  change (∫ x in (0 : ℝ)..1,P x)=0
  linear_combination (hdiff+h2')/2

theorem classicalHillFlow_wronskian (q : Curve ℂ) (a : ℂ) (t : Icc (0 : ℝ) 1) :
    (classicalHillFlow q a (1,0) t).1*(classicalHillFlow q a (0,1) t).2-
      (classicalHillFlow q a (1,0) t).2*(classicalHillFlow q a (0,1) t).1=1 := by
  let C := classicalHillFlow q a (1,0)
  let S := classicalHillFlow q a (0,1)
  let W (x : ℝ) := (C x).1*(S x).2-(C x).2*(S x).1
  have hf (v : ℂ × ℂ) (r : Icc (0 : ℝ) 1) :
      HasDerivAt (fun x : ℝ => (classicalHillFlow q a v x).1) (classicalHillFlow q a v r).2 r.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q a v r).fst
  have hg (v : ℂ × ℂ) (r : Icc (0 : ℝ) 1) :
      HasDerivAt (fun x : ℝ => (classicalHillFlow q a v x).2)
        ((q r-a)*(classicalHillFlow q a v r).1) r.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q a v r).snd
  have hd (r : Icc (0 : ℝ) 1) : HasDerivAt W 0 r.val := by
    convert! ((hf (1,0) r).mul (hg (0,1) r)).sub ((hg (1,0) r).mul (hf (0,1) r)) using 1
    ring
  have hC : Continuous C := continuous_classicalHillFlow q a (1,0)
  have hS : Continuous S := continuous_classicalHillFlow q a (0,1)
  have hc : Continuous W := (hC.fst.mul hS.snd).sub (hC.snd.mul hS.fst)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1 hc.continuousOn
    (fun x (hx : x∈Ioo (0 : ℝ) t.val) => hd ⟨x,hx.1.le,le_trans hx.2.le t.property.2⟩)
    (intervalIntegrable_const (c := (0 : ℂ)))
  have he : 0=W t-1 := by simpa [W,C,S,classicalHillFlow_zero] using hi
  change W t=1
  linear_combination -he

theorem classicalHill_dirichlet_mixed_pairing_diagonal
    (q : Curve ℂ) (a : ℂ) (ha : (classicalHillFlow q a (0,1) 1).1=0) :
    (∫ x in (0 : ℝ)..1, (classicalHillFlow q a (0,1) x).1^2*
      ((classicalHillFlow q a (1,0) x).2*(classicalHillFlow q a (0,1) x).1+
        (classicalHillFlow q a (1,0) x).1*(classicalHillFlow q a (0,1) x).2))=
      -(∫ x in (0 : ℝ)..1,(classicalHillFlow q a (0,1) x).1^2)/2 := by
  let C := classicalHillFlow q a (1,0)
  let S := classicalHillFlow q a (0,1)
  let P (x : ℝ) := (S x).1^2*((C x).2*(S x).1+(C x).1*(S x).2)
  have hC : Continuous C := continuous_classicalHillFlow q a (1,0)
  have hS : Continuous S := continuous_classicalHillFlow q a (0,1)
  have hd (t : Icc (0 : ℝ) 1) : HasDerivAt (fun x : ℝ => (C x).1*(S x).1^3)
      (2*P t+(S t).1^2) t.val := by
    have hc : HasDerivAt (fun x : ℝ => (C x).1) (C t).2 t.val := by
      simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q a (1,0) t).fst
    have hs : HasDerivAt (fun x : ℝ => (S x).1) (S t).2 t.val := by
      simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q a (0,1) t).fst
    convert! hc.mul (hs.pow 3) using 1
    have hw := classicalHillFlow_wronskian q a t
    change (C t).1*(S t).2-(C t).2*(S t).1=1 at hw
    simp only [Pi.pow_apply]
    dsimp only [P]
    linear_combination -hw*(S t).1^2
  have hc : Continuous (fun x : ℝ => (C x).1*(S x).1^3) := by fun_prop
  have hP : Continuous P := by dsimp [P];fun_prop
  have hSq : Continuous (fun x : ℝ => (S x).1^2) := by fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ)≤1)
    hc.continuousOn (fun x (hx : x∈Ioo (0 : ℝ) 1) => hd ⟨x,hx.1.le,hx.2.le⟩)
    (((continuous_const.mul hP).add hSq).intervalIntegrable 0 1)
  change (∫ x in (0 : ℝ)..1,2*P x+(S x).1^2)=(C 1).1*(S 1).1^3-(C 0).1*(S 0).1^3 at hi
  rw [intervalIntegral.integral_add ((hP.const_mul 2).intervalIntegrable 0 1) (hSq.intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul] at hi
  have he : 2*(∫ x in (0 : ℝ)..1,P x)+(∫ x in (0 : ℝ)..1,(S x).1^2)=0 := by
    simpa [C,S,ha,classicalHillFlow_zero] using hi
  change (∫ x in (0 : ℝ)..1,P x)= -(∫ x in (0 : ℝ)..1,(S x).1^2)/2
  linear_combination he/2

end NLS.KdV
