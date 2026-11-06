import NLS.ComplexAnalysis.QuadraticCircleHomotopyGeometry

noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

/-- The actual positively oriented energy path obtained by squaring a
frequency circle and subtracting the fixed real energy translation. -/
def quadraticCirclePath (b R c : ℝ) :
    Path ((circleMap (b:ℂ) R 0)^2-(c:ℂ)) ((circleMap (b:ℂ) R 0)^2-(c:ℂ)) :=
  (circlePath (b:ℂ) R).map (show Continuous (fun z : ℂ => z^2-(c:ℂ)) from by fun_prop)

theorem quadraticCirclePath_contDiffOn (b R c : ℝ) :
    ContDiffOn ℝ 2 (quadraticCirclePath b R c).extend (Icc 0 1) := by
  have hθ : ContDiff ℝ 2 (fun t : ℝ => (2*Real.pi)*t) := by fun_prop
  have hθc : ContDiff ℝ 2 (fun t : ℝ => (((2*Real.pi)*t:ℝ):ℂ)) := by
    simpa only [Function.comp_def,Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp hθ
  have hraw : ContDiff ℝ 2 (fun t : ℝ => (circleMap (b:ℂ) R ((2*Real.pi)*t))^2-(c:ℂ)) := by
    simp only [circleMap]
    fun_prop
  apply hraw.contDiffOn.congr
  intro t ht
  rw [(quadraticCirclePath b R c).extend_apply ht]
  rfl

/-- The quadratic energy contour is exactly this one smooth path. -/
theorem integral_quadraticEnergyCircle_eq_curveIntegral (b R c : ℝ) (f : ℂ → ℂ) :
    (quadraticEnergyLoop (PiecewiseC1Loop.circle (b:ℂ) R) (c:ℂ)).integral f=
      ∫ᶜ z in quadraticCirclePath b R c, holomorphicOneForm f z := by
  change (∑ _i : Fin 1, ∫ᶜ z in quadraticCirclePath b R c, holomorphicOneForm f z)=_
  rw [Fin.sum_univ_one]

/-- A genuine holomorphic contour transfer, preserving orientation, from
a quadratic frequency circle to an energy circle in the same two bands. -/
theorem integral_quadraticEnergyCircle_eq_circleIntegral
    (b R c d r a₀ a₁ b₀ b₁ : ℝ) (S : Set ℂ) (f : ℂ → ℂ)
    (hR : 0<R) (hb : R<b) (hr : 0<r)
    (hleft : (b-R)^2-c∈Ioo a₀ a₁) (hright : (b+R)^2-c∈Ioo b₀ b₁)
    (hrefleft : d-r∈Ioo a₀ a₁) (hrefright : d+r∈Ioo b₀ b₁)
    (hinclude : {z : ℂ | z.im≠0 ∨ z.re∈Ioo a₀ a₁ ∨ z.re∈Ioo b₀ b₁}⊆S)
    (hf : ∀ z∈S, DifferentiableAt ℂ f z) :
    (quadraticEnergyLoop (PiecewiseC1Loop.circle (b:ℂ) R) (c:ℂ)).integral f=
      ∮ z in C((d:ℂ),r), f z := by
  let γ := quadraticCirclePath b R c
  let δ := circlePath (d:ℂ) r
  let H := ContinuousMap.Homotopy.affine (γ : C(I,ℂ)) (δ : C(I,ℂ))
  have hγ (u : I) : γ u=(circleMap (b:ℂ) R ((2*Real.pi)*(u:ℝ)))^2-(c:ℂ) := rfl
  have hδ (u : I) : δ u=circleMap (d:ℂ) r ((2*Real.pi)*(u:ℝ)) := rfl
  have hmem (s u : I) : H (s,u)∈S := by
    dsimp only [H]
    rw [ContinuousMap.Homotopy.affine_apply]
    change AffineMap.lineMap (γ u) (δ u) (s:ℝ)∈S
    rw [hγ,hδ]
    exact hinclude (affine_quadratic_circle_mem_bands b R c d r a₀ a₁ b₀ b₁
      ((2*Real.pi)*(u:ℝ)) s hR hb hr s.property hleft hright hrefleft hrefright)
  have hclosed : IsClosed (range H) := isCompact_range H.continuous |>.isClosed
  have he := curveIntegral_eq_of_holomorphic_homotopy f H affineHomotopy_loop
    (t := range H) (fun s _ u _ => mem_range_self (s,u)) (by
      rw [hclosed.closure_eq]
      rintro z ⟨⟨s,u⟩,rfl⟩
      exact hf _ (hmem s u))
    (affineHomotopy_contDiffOn (quadraticCirclePath_contDiffOn b R c)
      (circlePath_contDiffOn (d:ℂ) r))
  rw [integral_quadraticEnergyCircle_eq_curveIntegral]
  exact he.trans (curveIntegral_circlePath f (d:ℂ) r)

end NLS.ComplexAnalysis
