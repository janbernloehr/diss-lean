import NLS.ComplexAnalysis.ContinuousSquareRootPath
import NLS.ComplexAnalysis.QuadraticRootPrimitive
import NLS.ComplexAnalysis.LogarithmicPathIntegral

/-!
# Logarithmic integrals of continuously continued quadratic roots

The square root is given only along a spectral path. Continuity and the
quadratic square identity recover its interior derivatives locally.
The logarithmic coordinate therefore evaluates the exponentiated model
integral without a single analytic root chart containing the path.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory
namespace NLS.ComplexAnalysis

theorem exp_integral_mul_eq_quadratic_root_path_endpoint
    (τ d : ℂ) (r : ℝ → ℂ) {a b : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hr : ContinuousOn r (Icc (0:ℝ) 1))
    (hsq : ∀ t ∈ Icc (0:ℝ) 1, r t^2 = quadraticRootPolynomial τ d (γ.extend t))
    (hne : ∀ t ∈ Ioo (0:ℝ) 1, r t ≠ 0)
    (hint : IntervalIntegrable (fun t : ℝ => -(r t)⁻¹*deriv γ.extend t) volume 0 1) :
    exp (∫ t in (0:ℝ)..1, -(r t)⁻¹*deriv γ.extend t)*(a-τ-r 0) = b-τ-r 1 := by
  let g : ℝ → ℂ := fun t => γ.extend t-τ-r t
  let q : ℝ → ℂ := fun t => -(r t)⁻¹*deriv γ.extend t
  have hrcont : ContinuousOn r (Ioo (0:ℝ) 1) := hr.mono Ioo_subset_Icc_self
  have hqcont : ContinuousOn q (Ioo (0:ℝ) 1) :=
    (hrcont.inv₀ hne).neg.mul
      ((hγ.mono Ioo_subset_Icc_self).continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl)
  have hgcont : ContinuousOn g (Icc (0:ℝ) 1) :=
    (γ.continuous_extend.continuousOn.sub continuousOn_const).sub hr
  have hgd (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt g (q t*g t) t := by
    have hγd : HasDerivAt γ.extend (deriv γ.extend t) t :=
      ((hγ.differentiableOn (by norm_num) t (Ioo_subset_Icc_self ht)).differentiableAt
        (Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Icc_self)).hasDerivAt
    have heq : (fun v => r v^2) =ᶠ[𝓝 t]
        (fun v => quadraticRootPolynomial τ d (γ.extend v)) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with v hv
      exact hsq v (Ioo_subset_Icc_self hv)
    have hs := ((hasDerivAt_quadraticRootPolynomial τ d (γ.extend t)).scomp t hγd).congr_of_eventuallyEq heq
    have hs' : HasDerivAt (fun v => r v^2)
        (2*(γ.extend t-τ)*deriv γ.extend t) t := by
      convert! hs using 1
      simp only [smul_eq_mul]
      ring
    have hrd := hasDerivAt_continuous_root_of_sq r (r t)
      (2*(γ.extend t-τ)*deriv γ.extend t) t
      (hrcont.continuousAt (isOpen_Ioo.mem_nhds ht)) rfl (hne t ht) hs'
    have hd := (hγd.sub_const τ).sub hrd
    convert! hd using 1
    dsimp only [q,g]
    field_simp [hne t ht]
    ring
  have h := eq_exp_integral_mul_of_hasDerivAt q g hint hqcont hgcont hgd
  simpa only [q,g,Path.extend_zero,Path.extend_one] using h.symm

end NLS.ComplexAnalysis
