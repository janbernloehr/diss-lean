import NLS.ComplexAnalysis.HolomorphicPathPullback
import NLS.ComplexAnalysis.CosineSegmentGeometry
import Mathlib.Tactic.FieldSimp

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
namespace NLS.ComplexAnalysis

/-- A cosine resolution of a quadratic energy path proves convergence
of EACH scalar numerator integral. The terminal-prescribed root cancels
against the actual path derivative; no sum-integrability is assumed. -/
theorem curveIntegrable_of_quadratic_cosine_resolution {A B : ℂ}
    (γ : Path A B) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (a b τ δ c : ℂ) (N D R : ℂ → ℂ)
    (hquad : ∀ t∈Icc (0:ℝ) 1, (γ.extend t)^2-c=
      cosineGapPoint τ δ (AffineMap.lineMap a b t))
    (hroot : ∀ t∈Ioo (0:ℝ) 1, R (γ.extend t)=
      -I*δ*Complex.sin (AffineMap.lineMap a b t)*D (cosineGapPoint τ δ (AffineMap.lineMap a b t)))
    (hz : ∀ t∈Icc (0:ℝ) 1, γ.extend t≠0)
    (hD : ∀ t∈Icc (0:ℝ) 1, D (cosineGapPoint τ δ (AffineMap.lineMap a b t))≠0)
    (hR : ∀ t∈Ioo (0:ℝ) 1, R (γ.extend t)≠0)
    (hNc : ContinuousOn (fun t : ℝ => N (γ.extend t)) (Icc 0 1))
    (hDc : ContinuousOn (fun t : ℝ => D (cosineGapPoint τ δ (AffineMap.lineMap a b t))) (Icc 0 1)) :
    CurveIntegrable (holomorphicOneForm (fun z => N z/R z)) γ := by
  let G : ℝ → ℂ := fun t =>
    -I*N (γ.extend t)/(2*γ.extend t*D (cosineGapPoint τ δ (AffineMap.lineMap a b t)))*(b-a)
  have hGc : ContinuousOn G (Icc 0 1) :=
    ((continuousOn_const.mul hNc).div
      ((continuousOn_const.mul γ.continuous_extend.continuousOn).mul hDc)
      (fun t ht => mul_ne_zero (mul_ne_zero (by norm_num) (hz t ht)) (hD t ht))).mul continuousOn_const
  have hInt : IntervalIntegrable G volume 0 1 := hGc.intervalIntegrable_of_Icc zero_le_one
  apply (intervalIntegrable_congr_uIoo ?_).mpr hInt
  rw [uIoo_of_le zero_le_one]
  intro t ht
  have hmem : Icc (0:ℝ) 1∈𝓝 t :=
    mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Icc_self
  have hγd : HasDerivAt γ.extend (deriv γ.extend t) t :=
    ((hγ.differentiableOn (by norm_num) t (Ioo_subset_Icc_self ht)).differentiableAt hmem).hasDerivAt
  have he : HasDerivAt (fun u : ℝ => AffineMap.lineMap a b u) (b-a) t := by
    simpa only [AffineMap.lineMap_apply_module',Complex.real_smul,Complex.ofRealCLM_apply,ofReal_one,one_mul,add_comm] using
      ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (b-a)).const_add a
  have hdE := (hasDerivAt_cosineGapPoint τ δ (AffineMap.lineMap a b t)).scomp t he
  have heq : (fun u : ℝ => (γ.extend u)^2-c)=ᶠ[𝓝 t]
      (fun u => cosineGapPoint τ δ (AffineMap.lineMap a b u)) :=
    mem_of_superset hmem (fun u hu => hquad u hu)
  have hd : 2*γ.extend t*deriv γ.extend t=
      (-δ*Complex.sin (AffineMap.lineMap a b t))*(b-a) := by
    have h := ((hγd.pow 2).sub_const c).unique (hdE.congr_of_eventuallyEq heq)
    simpa only [Nat.cast_ofNat,Nat.reduceSub,pow_one,smul_eq_mul,mul_comm] using h
  have hδ : δ≠0 := by
    intro h
    apply hR t ht
    rw [hroot t ht,h]
    ring
  have hs : Complex.sin (AffineMap.lineMap a b t)≠0 := by
    intro h
    apply hR t ht
    rw [hroot t ht,h]
    ring
  have hd' : deriv γ.extend t=
      (-δ*Complex.sin (AffineMap.lineMap a b t))*(b-a)/(2*γ.extend t) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) (hz t (Ioo_subset_Icc_self ht)))).mpr
    simpa only [mul_comm (deriv γ.extend t)] using hd
  rw [curveIntegralFun_def,holomorphicOneForm_apply,derivWithin_of_mem_nhds hmem,hd',hroot t ht]
  dsimp only [G]
  field_simp [I_ne_zero,hδ,hs,hz t (Ioo_subset_Icc_self ht),hD t (Ioo_subset_Icc_self ht)]
  simp only [I_sq]
  ring

end NLS.ComplexAnalysis
