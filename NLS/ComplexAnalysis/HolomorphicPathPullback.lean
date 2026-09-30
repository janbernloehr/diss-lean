import NLS.ComplexAnalysis.CurveIntegralInteriorCongruence

/-! # Pulling holomorphic curve integrals back along mapped paths

The chain rule on the open parameter interval suffices to transport
integrability and the exact integral. Endpoint values of either scalar
differential are unrestricted, so the map may resolve endpoint zeros.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory
namespace NLS.ComplexAnalysis

theorem holomorphicPathPullback_integral_and_integrability
    (f g T dT : ℂ → ℂ) (hT : Continuous T) {a b : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hTd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt T (dT (γ.extend t)) (γ.extend t))
    (hpull : ∀ t ∈ Ioo (0 : ℝ) 1, f (T (γ.extend t)) * dT (γ.extend t) = g (γ.extend t)) :
    (CurveIntegrable (holomorphicOneForm f) (γ.map hT) ↔ CurveIntegrable (holomorphicOneForm g) γ) ∧
      (∫ᶜ z in γ.map hT, holomorphicOneForm f z) = ∫ᶜ z in γ, holomorphicOneForm g z := by
  have hmap (t : ℝ) : (γ.map hT).extend t = T (γ.extend t) := rfl
  have hder (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      deriv (γ.map hT).extend t = dT (γ.extend t) * deriv γ.extend t := by
    have hγd : HasDerivAt γ.extend (deriv γ.extend t) t :=
      ((hγ.differentiableOn (by norm_num) t (Ioo_subset_Icc_self ht)).differentiableAt
        (Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Icc_self)).hasDerivAt
    have hd : HasDerivAt (fun v => T (γ.extend v))
        (dT (γ.extend t) * deriv γ.extend t) t := by
      convert! (hTd t ht).scomp t hγd using 1
      simp only [smul_eq_mul]
      ring
    exact (hd.congr_of_eventuallyEq (Eventually.of_forall hmap)).deriv
  have heq (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      curveIntegralFun (holomorphicOneForm f) (γ.map hT) t =
        curveIntegralFun (holomorphicOneForm g) γ t := by
    have hmem : Icc (0 : ℝ) 1 ∈ 𝓝 t :=
      Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Icc_self
    rw [curveIntegralFun_def,curveIntegralFun_def,holomorphicOneForm_apply,
      holomorphicOneForm_apply,derivWithin_of_mem_nhds hmem,derivWithin_of_mem_nhds hmem,
      hmap,hder t ht,← mul_assoc,hpull t ht]
  constructor
  · apply intervalIntegrable_congr_uIoo
    rw [uIoo_of_le zero_le_one]
    exact heq
  · rw [curveIntegral_def,curveIntegral_def]
    exact intervalIntegral.integral_congr_Ioo_of_le zero_le_one heq

end NLS.ComplexAnalysis
