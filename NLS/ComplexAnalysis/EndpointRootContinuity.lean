import NLS.ComplexAnalysis.AnalyticTwoZeroRoot

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



theorem continuousAt_endpointRoot_of_not_mem_segment
    {X : Type*} [TopologicalSpace X] (a b z : X → ℂ) {x : X}
    (ha : ContinuousAt a x) (hb : ContinuousAt b x) (hz : ContinuousAt z x)
    (hn : z x ∉ segment ℝ (a x) (b x)) :
    ContinuousAt (fun y => endpointRoot (a y) (b y) (z y)) x := by
  have hmid : (a x+b x)/2 ≠ z x := fun he => hn (he ▸ midpoint_mem_complex_segment (a x) (b x))
  have hlin : ContinuousAt (fun y => (a y+b y)/2-z y) x := (ha.add hb).div_const 2 |>.sub hz
  have hnum : ContinuousAt (fun y => (b y-a y)^2) x := (hb.sub ha).pow 2
  have hden : ContinuousAt (fun y => (4 : ℂ)*((a y+b y)/2-z y)^2) x := continuousAt_const.mul (hlin.pow 2)
  have hd : (4 : ℂ)*((a x+b x)/2-z x)^2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 (sub_ne_zero.mpr hmid))
  have hr : ContinuousAt (fun y => 1-(b y-a y)^2/(4*((a y+b y)/2-z y)^2)) x :=
    continuousAt_const.sub (hnum.div hden hd)
  have hs : AnalyticAt ℂ Complex.sqrt (1-(b x-a x)^2/(4*((a x+b x)/2-z x)^2)) := Complex.differentiableOn_sqrt.analyticAt
    (isOpen_slitPlane.mem_nhds (gap_radicand_mem_slitPlane (a x) (b x) (z x) hn))
  have hscomp : ContinuousAt (fun y => Complex.sqrt (1-(b y-a y)^2/(4*((a y+b y)/2-z y)^2))) x :=
    ContinuousAt.comp (f := fun y : X => 1-(b y-a y)^2/(4*((a y+b y)/2-z y)^2)) hs.continuousAt hr
  exact hlin.mul hscomp

end NLS.ComplexAnalysis
