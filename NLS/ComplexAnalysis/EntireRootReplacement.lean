import NLS.ComplexAnalysis.CauchyFiniteHoles

/-! An entire divided difference removes a prescribed zero, including
at the zero itself. A new linear factor replaces it without poles.
The resulting entire function is nonzero whenever the original is. -/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

def rootReplacement (f : ℂ → ℂ) (a b z : ℂ) : ℂ := (z-b)*dslope f a z

theorem analyticOnNhd_rootReplacement (f : ℂ → ℂ) (a b : ℂ)
    (hf : AnalyticOnNhd ℂ f univ) : AnalyticOnNhd ℂ (rootReplacement f a b) univ :=
  (analyticOnNhd_id.sub analyticOnNhd_const).mul
    (analyticOnNhd_dslope_of_analytic f univ a hf (mem_univ _))

theorem rootReplacement_mul (f : ℂ → ℂ) (a b z : ℂ) (ha : f a = 0) :
    (z-a)*rootReplacement f a b z = (z-b)*f z := by
  have h : (z-a)*dslope f a z = f z := by
    simpa only [smul_eq_mul,ha,sub_zero] using sub_smul_dslope f a z
  dsimp only [rootReplacement]
  calc
    (z-a)*((z-b)*dslope f a z) = (z-b)*((z-a)*dslope f a z) := by ring
    _ = (z-b)*f z := by rw [h]

theorem rootReplacement_eq_ratio (f : ℂ → ℂ) (a b z : ℂ) (ha : f a = 0) (hz : z ≠ a) :
    rootReplacement f a b z = ((z-b)/(z-a))*f z := by
  have h := rootReplacement_mul f a b z ha
  apply mul_left_cancel₀ (sub_ne_zero.mpr hz)
  calc
    (z-a)*rootReplacement f a b z = (z-b)*f z := h
    _ = (z-a)*(((z-b)/(z-a))*f z) := by field_simp

theorem rootReplacement_zero_new (f : ℂ → ℂ) (a b : ℂ) : rootReplacement f a b b = 0 := by
  simp only [rootReplacement,sub_self,zero_mul]

theorem rootReplacement_zero_of_ne (f : ℂ → ℂ) (a b z : ℂ)
    (ha : f a = 0) (hz : f z = 0) (hne : z ≠ a) : rootReplacement f a b z = 0 := by
  rw [rootReplacement_eq_ratio f a b z ha hne,hz,mul_zero]

theorem rootReplacement_zero_of_deriv_zero (f : ℂ → ℂ) (a b : ℂ) (hd : deriv f a = 0) :
    rootReplacement f a b a = 0 := by
  simp only [rootReplacement,dslope_same,hd,mul_zero]

theorem rootReplacement_eq_zero_implies (f : ℂ → ℂ) (a b : ℂ)
    (hf : AnalyticOnNhd ℂ f univ) (ha : f a = 0) (hzero : rootReplacement f a b = 0) : f = 0 := by
  have hprod : (fun z : ℂ => (z-b)*f z) = 0 := by
    funext z
    rw [← rootReplacement_mul f a b z ha,hzero,Pi.zero_apply,mul_zero]
  have hd : HasDerivAt (fun z : ℂ => (z-b)*f z) (f b) b := by
    simpa only [id_eq,sub_self,zero_mul,one_mul,add_zero] using!
      ((hasDerivAt_id b).sub_const b).mul (hf b (mem_univ _)).differentiableAt.hasDerivAt
  rw [hprod] at hd
  have hb : f b = 0 := hd.unique (hasDerivAt_const b (0:ℂ))
  funext z
  by_cases hz : z = b
  · simpa only [hz,Pi.zero_apply] using hb
  · have h := congrFun hprod z
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hz)

end NLS.ComplexAnalysis
