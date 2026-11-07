import NLS.ComplexAnalysis.HolomorphicPathPullback

/-! # Local holomorphic pullback along actual mapped path values

The chain rule on the open parameter interval suffices to transport
integrability and the exact integral. Endpoint values of either scalar
differential are unrestricted, so the map may resolve endpoint zeros.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory
namespace NLS.ComplexAnalysis

theorem holomorphicPathPullback_of_extend_eq
    (f g T dT : ℂ → ℂ) {a b c d : ℂ} (γ : Path a b) (η : Path c d)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hmap : ∀ t : ℝ, η.extend t = T (γ.extend t))
    (hTd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt T (dT (γ.extend t)) (γ.extend t))
    (hpull : ∀ t ∈ Ioo (0 : ℝ) 1, f (T (γ.extend t))*dT (γ.extend t) = g (γ.extend t)) :
    (CurveIntegrable (holomorphicOneForm f) η ↔ CurveIntegrable (holomorphicOneForm g) γ) ∧
      (∫ᶜ z in η, holomorphicOneForm f z) = ∫ᶜ z in γ, holomorphicOneForm g z := by
  have hder (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      deriv η.extend t = dT (γ.extend t) * deriv γ.extend t := by
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
      curveIntegralFun (holomorphicOneForm f) η t =
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
