import NLS.ComplexAnalysis.ContinuousSquareRootPath
import NLS.ComplexAnalysis.QuadraticRootPrimitive
import NLS.ComplexAnalysis.ImproperLogarithmicIntegral

/-!
# Improper integrals of continuously continued quadratic roots

A nonzero quadratic gap gives a nonvanishing logarithmic coordinate,
including at the endpoints. The model integral therefore converges
without requiring absolute integrability of the weighted path length.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory
namespace NLS.ComplexAnalysis

theorem exists_improper_quadratic_root_path_integral
    (τ d : ℂ) (hd : d ≠ 0) (r : ℝ → ℂ) {a b : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Ioo 0 1))
    (hr : ContinuousOn r (Icc (0:ℝ) 1))
    (hsq : ∀ t ∈ Icc (0:ℝ) 1, r t^2 = quadraticRootPolynomial τ d (γ.extend t))
    (hne : ∀ t ∈ Ioo (0:ℝ) 1, r t ≠ 0) :
    ∃ L : ℂ, Tendsto (fun u : ℝ × ℝ => ∫ t in u.1..u.2, -(r t)⁻¹*deriv γ.extend t)
      ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[<] (1:ℝ))) (𝓝 L) ∧
      exp L*(a-τ-r 0) = b-τ-r 1 := by
  let g : ℝ → ℂ := fun t => γ.extend t-τ-r t
  let q : ℝ → ℂ := fun t => -(r t)⁻¹*deriv γ.extend t
  have hrcont : ContinuousOn r (Ioo (0:ℝ) 1) := hr.mono Ioo_subset_Icc_self
  have hqcont : ContinuousOn q (Ioo (0:ℝ) 1) :=
    (hrcont.inv₀ hne).neg.mul
      (hγ.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl)
  have hgcont : ContinuousOn g (Icc (0:ℝ) 1) :=
    (γ.continuous_extend.continuousOn.sub continuousOn_const).sub hr
  have hgd (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt g (q t*g t) t := by
    have hγd : HasDerivAt γ.extend (deriv γ.extend t) t :=
      ((hγ.differentiableOn (by norm_num) t ht).differentiableAt
        (isOpen_Ioo.mem_nhds ht)).hasDerivAt
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
  have hgne (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : g t ≠ 0 := by
    have hprod : g t*(γ.extend t-τ+r t) = d := by
      dsimp only [g]
      have hs := hsq t ht
      dsimp only [quadraticRootPolynomial] at hs
      linear_combination -hs
    intro hz
    rw [hz,zero_mul] at hprod
    exact hd hprod.symm
  obtain ⟨L,hL,he⟩ := exists_improper_integral_of_logarithmic_derivative q g hqcont hgcont hgne hgd
  exact ⟨L,hL,by simpa only [g,Path.extend_zero,Path.extend_one] using he⟩

end NLS.ComplexAnalysis
