import NLS.ZakharovShabat.CanonicalPeriodicProductContinuity
import NLS.ComplexAnalysis.LocalAnalyticApproximation

/-!
# Complex Fréchet smoothness of the canonical periodic product

The intrinsic polynomials converge uniformly on actual joint neighborhoods,
where they are eventually analytic. Banach-space Schwarz estimates then give
uniform operator-norm convergence of their Fréchet derivatives and joint
complex smoothness of the canonical limit.
-/

noncomputable section
open Filter Topology Metric
open scoped ContDiff
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The canonical product has uniform analytic approximation on actual joint balls. -/
theorem localUniformAnalyticApproximation_canonicalPeriodicProduct (hp : p ≠ ⊤) (hp1 : 1 < p) :
    NLS.ComplexAnalysis.HasLocalUniformAnalyticApproximation
      (fun (M : ℕ) (t : ℂ × PairSpace p) => normalizedCentralPeriodicPolynomial hp t.2 M t.1)
      (fun t => canonicalPeriodicProduct hp t.2 t.1) := by
  intro t
  obtain ⟨U,ho,_,ht,_,hU⟩ := exists_uniform_canonicalPeriodicProduct_pair hp hp1 t.2
  obtain ⟨N,V,_,hV,_,htV,_,hA⟩ := exists_uniform_analytic_normalizedCentralPolynomials hp t.2
  have hn : ball t.1 1 ×ˢ (U ∩ V) ∈ 𝓝 t :=
    prod_mem_nhds (ball_mem_nhds t.1 (by norm_num)) ((ho.inter hV).mem_nhds ⟨ht,htV⟩)
  obtain ⟨r,hr,hs⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r/2,half_pos hr,?_,?_⟩
  · rw [show 2*(r/2) = r by ring]
    apply (hU _ (isCompact_closedBall t.1 1)).mono
    exact fun x hx => ⟨ball_subset_closedBall (hs hx).1,(hs hx).2.1⟩
  · filter_upwards [eventually_ge_atTop N] with M hM
    apply (hA M hM).mono
    rw [show 2*(r/2) = r by ring]
    exact fun x hx => ⟨Set.mem_univ _,(hs hx).2.2⟩

/-- The canonical full product is jointly complex Fréchet differentiable. -/
theorem differentiable_canonicalPeriodicProduct_joint (hp : p ≠ ⊤) (hp1 : 1 < p) :
    Differentiable ℂ (fun t : ℂ × PairSpace p => canonicalPeriodicProduct hp t.2 t.1) :=
  (localUniformAnalyticApproximation_canonicalPeriodicProduct hp hp1).differentiable

/-- All joint Fréchet derivatives exist and are continuous over the complex field. -/
theorem contDiff_canonicalPeriodicProduct_joint (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ContDiff ℂ ∞ (fun t : ℂ × PairSpace p => canonicalPeriodicProduct hp t.2 t.1) :=
  (localUniformAnalyticApproximation_canonicalPeriodicProduct hp hp1).contDiff

/-- The intrinsic polynomial derivatives converge uniformly in operator norm on a joint neighborhood. -/
theorem exists_uniform_fderiv_canonicalPeriodicProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (t : ℂ × PairSpace p) :
    ∃ r : ℝ, 0 < r ∧ TendstoUniformlyOn
      (fun M => fderiv ℂ (fun t : ℂ × PairSpace p => normalizedCentralPeriodicPolynomial hp t.2 M t.1))
      (fderiv ℂ (fun t : ℂ × PairSpace p => canonicalPeriodicProduct hp t.2 t.1)) atTop (ball t r) :=
  (localUniformAnalyticApproximation_canonicalPeriodicProduct hp hp1).uniform_fderiv t

/-- Joint polynomial derivatives converge locally uniformly on the full product domain. -/
theorem tendstoLocallyUniformlyOn_fderiv_canonicalPeriodicProduct (hp : p ≠ ⊤) (hp1 : 1 < p) :
    TendstoLocallyUniformlyOn
      (fun M => fderiv ℂ (fun t : ℂ × PairSpace p => normalizedCentralPeriodicPolynomial hp t.2 M t.1))
      (fderiv ℂ (fun t : ℂ × PairSpace p => canonicalPeriodicProduct hp t.2 t.1)) atTop Set.univ := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro t _
  obtain ⟨r,hr,h⟩ := exists_uniform_fderiv_canonicalPeriodicProduct hp hp1 t
  exact ⟨ball t r,nhdsWithin_le_nhds (ball_mem_nhds t hr),h⟩

/-- Along every complex affine line, including simultaneous spectral and potential perturbations, the product is entire. -/
theorem analyticOnNhd_canonicalPeriodicProduct_line (hp : p ≠ ⊤) (hp1 : 1 < p)
    (t v : ℂ × PairSpace p) :
    AnalyticOnNhd ℂ (fun a : ℂ => canonicalPeriodicProduct hp (t+a • v).2 (t+a • v).1) Set.univ := by
  have h : Differentiable ℂ (fun a : ℂ => canonicalPeriodicProduct hp (t+a • v).2 (t+a • v).1) :=
    (differentiable_canonicalPeriodicProduct_joint hp hp1).comp (by fun_prop)
  exact h.differentiableOn.analyticOnNhd isOpen_univ

end NLS.ZakharovShabat
