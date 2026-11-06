import NLS.KdV.ClassicalHillMixedPairings

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal

namespace NLS.KdV

theorem classicalHill_dirichlet_product_pairing_zero_of_ne
    (q : Curve ℂ) (a b : ℂ) (v w : ℂ × ℂ) (hab : a≠b)
    (ha : (classicalHillFlow q a (0,1) 1).1=0)
    (hb : (classicalHillFlow q b (0,1) 1).1=0) :
    (∫ x in (0 : ℝ)..1, (classicalHillFlow q a v x).1*(classicalHillFlow q a (0,1) x).1*
      ((classicalHillFlow q b w x).2*(classicalHillFlow q b (0,1) x).1+
        (classicalHillFlow q b w x).1*(classicalHillFlow q b (0,1) x).2))=0 := by
  let A := classicalHillFlow q a v
  let B := classicalHillFlow q a (0,1)
  let C := classicalHillFlow q b w
  let S := classicalHillFlow q b (0,1)
  let Wc (x : ℝ) := (A x).1*(C x).2-(A x).2*(C x).1
  let Ws (x : ℝ) := (B x).1*(S x).2-(B x).2*(S x).1
  let P (x : ℝ) := (A x).1*(B x).1*((C x).2*(S x).1+(C x).1*(S x).2)
  let Q (x : ℝ) := ((A x).2*(B x).1+(A x).1*(B x).2)*(C x).1*(S x).1
  have hcont (e : ℂ) (v : ℂ × ℂ) : Continuous (classicalHillFlow q e v) := continuous_classicalHillFlow q e v
  have hf (e : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
      HasDerivAt (fun x : ℝ => (classicalHillFlow q e v x).1) (classicalHillFlow q e v t).2 t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q e v t).fst
  have hg (e : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
      HasDerivAt (fun x : ℝ => (classicalHillFlow q e v x).2)
        ((q t-e)*(classicalHillFlow q e v t).1) t.val := by
    simpa using! HasFDerivAt.hasDerivAt (hasDerivAt_classicalHillFlow q e v t).snd
  have hWc (t : Icc (0 : ℝ) 1) : HasDerivAt Wc ((a-b)*(A t).1*(C t).1) t.val := by
    convert! ((hf a v t).mul (hg b w t)).sub ((hg a v t).mul (hf b w t)) using 1
    ring
  have hWs (t : Icc (0 : ℝ) 1) : HasDerivAt Ws ((a-b)*(B t).1*(S t).1) t.val := by
    convert! ((hf a (0,1) t).mul (hg b (0,1) t)).sub ((hg a (0,1) t).mul (hf b (0,1) t)) using 1
    ring
  have hprodW (t : Icc (0 : ℝ) 1) : HasDerivAt (fun x : ℝ => Wc x*Ws x)
      ((a-b)*(P t-Q t)) t.val := by
    convert! (hWc t).mul (hWs t) using 1
    dsimp [Wc,Ws,P,Q]
    ring
  have hprodS (t : Icc (0 : ℝ) 1) : HasDerivAt
      (fun x : ℝ => (A x).1*(B x).1*(C x).1*(S x).1) (P t+Q t) t.val := by
    convert! (((hf a v t).mul (hf a (0,1) t)).mul (hf b w t)).mul (hf b (0,1) t) using 1
    dsimp [P,Q]
    ring
  have hP : Continuous P := by dsimp [P,A,B,C,S];fun_prop
  have hQ : Continuous Q := by dsimp [Q,A,B,C,S];fun_prop
  have hWcont : Continuous (fun x : ℝ => Wc x*Ws x) := by dsimp [Wc,Ws,A,B,C,S];fun_prop
  have hScont : Continuous (fun x : ℝ => (A x).1*(B x).1*(C x).1*(S x).1) := by dsimp [A,B,C,S];fun_prop
  have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ)≤1)
    hWcont.continuousOn (fun x (hx : x∈Ioo (0 : ℝ) 1) => hprodW ⟨x,hx.1.le,hx.2.le⟩)
    ((continuous_const.mul (hP.sub hQ)).intervalIntegrable 0 1)
  have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ)≤1)
    hScont.continuousOn (fun x (hx : x∈Ioo (0 : ℝ) 1) => hprodS ⟨x,hx.1.le,hx.2.le⟩)
    ((hP.add hQ).intervalIntegrable 0 1)
  change (∫ x in (0 : ℝ)..1,(a-b)*(P x-Q x))=Wc 1*Ws 1-Wc 0*Ws 0 at h1
  change (∫ x in (0 : ℝ)..1,P x+Q x)=(A 1).1*(B 1).1*(C 1).1*(S 1).1-(A 0).1*(B 0).1*(C 0).1*(S 0).1 at h2
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub (hP.intervalIntegrable 0 1) (hQ.intervalIntegrable 0 1)] at h1
  rw [intervalIntegral.integral_add (hP.intervalIntegrable 0 1) (hQ.intervalIntegrable 0 1)] at h2
  have h1' : (a-b)*((∫ x in (0 : ℝ)..1,P x)-(∫ x in (0 : ℝ)..1,Q x))=0 := by
    simpa [Wc,Ws,A,B,C,S,ha,hb,classicalHillFlow_zero] using h1
  have h2' : (∫ x in (0 : ℝ)..1,P x)+(∫ x in (0 : ℝ)..1,Q x)=0 := by
    simpa [A,B,C,S,ha,hb,classicalHillFlow_zero] using h2
  have hdiff : (∫ x in (0 : ℝ)..1,P x)-(∫ x in (0 : ℝ)..1,Q x)=0 :=
    (mul_eq_zero.mp h1').resolve_left (sub_ne_zero.mpr hab)
  change (∫ x in (0 : ℝ)..1,P x)=0
  linear_combination (hdiff+h2')/2

theorem classicalHillFlow_sub_smul_initial
    (q : Curve ℂ) (a : ℂ) (v w : ℂ × ℂ) (c : ℂ) (t : Icc (0 : ℝ) 1) :
    classicalHillFlow q a (v-c • w) t=classicalHillFlow q a v t-c • classicalHillFlow q a w t := by
  apply Eq.symm
  apply solution_unique (classicalHillCoefficientCurve q a) (v-c • w)
    (fun x : ℝ => classicalHillFlow q a v x-c • classicalHillFlow q a w x)
    (((continuous_classicalHillFlow q a v).sub ((continuous_classicalHillFlow q a w).const_smul c)).continuousOn)
    (by simp only [classicalHillFlow_zero]) _ t.property
  intro r _
  have hh := (hasDerivAt_classicalHillFlow q a v r).sub
    ((hasDerivAt_classicalHillFlow q a w r).const_smul c)
  change HasDerivAt (fun x : ℝ => classicalHillFlow q a v x-c • classicalHillFlow q a w x)
    ((classicalHillFlow q a v r-c • classicalHillFlow q a w r).2,
      (q r-a)*(classicalHillFlow q a v r-c • classicalHillFlow q a w r).1) r.val
  convert! hh using 1
  apply Prod.ext
  · rfl
  · simp only [Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    ring

theorem classicalHill_log_cotangent_pairing_zero_of_ne
    (q : Curve ℂ) (a b alpha beta : ℂ) (hab : a≠b)
    (ha : (classicalHillFlow q a (0,1) 1).1=0)
    (hb : (classicalHillFlow q b (0,1) 1).1=0) :
    (∫ x in (0 : ℝ)..1,
      ((classicalHillFlow q a (1,0) x).1*(classicalHillFlow q a (0,1) x).1-alpha*(classicalHillFlow q a (0,1) x).1^2)*
      ((classicalHillFlow q b (1,0) x).2*(classicalHillFlow q b (0,1) x).1+
        (classicalHillFlow q b (1,0) x).1*(classicalHillFlow q b (0,1) x).2-
        (2*beta)*((classicalHillFlow q b (0,1) x).1*(classicalHillFlow q b (0,1) x).2)))=0 := by
  have hlin (e c : ℂ) (t : Icc (0 : ℝ) 1) :
      classicalHillFlow q e (1,-c) t=classicalHillFlow q e (1,0) t-c • classicalHillFlow q e (0,1) t := by
    have hi : ((1 : ℂ),-c)=((1 : ℂ),0)-c • ((0 : ℂ),1) := by ext <;> simp [smul_eq_mul]
    rw [hi,classicalHillFlow_sub_smul_initial]
  have hp := classicalHill_dirichlet_product_pairing_zero_of_ne q a b (1,-alpha) (1,-beta) hab ha hb
  refine Eq.trans ?_ hp
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x∈Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hx
  have hla := hlin a alpha ⟨x,hx'⟩
  have hlb := hlin b beta ⟨x,hx'⟩
  change classicalHillFlow q a (1,-alpha) x=classicalHillFlow q a (1,0) x-alpha • classicalHillFlow q a (0,1) x at hla
  change classicalHillFlow q b (1,-beta) x=classicalHillFlow q b (1,0) x-beta • classicalHillFlow q b (0,1) x at hlb
  dsimp only []
  rw [hla,hlb]
  simp only [Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

end NLS.KdV
