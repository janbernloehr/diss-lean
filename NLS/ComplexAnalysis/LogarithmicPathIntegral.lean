import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Exponentiated logarithmic path integrals

A scalar integrating factor evaluates the exponential of a logarithmic
path integral from its endpoint values. Only interior derivatives are
needed, so integrable singular endpoints are allowed. Equal nonzero
endpoint values give periods in `2πi ℤ`, without a homotopy assumption.
-/

noncomputable section
open Set Filter Topology MeasureTheory Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

/-- Scalar variation of constants with an integrable coefficient,
continuous on the open interval, and no endpoint derivatives. -/
theorem eq_exp_integral_mul_of_hasDerivAt
    (q g : ℝ → ℂ) (hq : IntervalIntegrable q volume 0 1)
    (hqcont : ContinuousOn q (Ioo (0:ℝ) 1))
    (hgcont : ContinuousOn g (Icc (0:ℝ) 1))
    (hg : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt g (q t*g t) t) :
    g 1 = exp (∫ t in (0:ℝ)..1, q t)*g 0 := by
  let P : ℝ → ℂ := fun t => ∫ s in (0:ℝ)..t, q s
  have hPcont : ContinuousOn P (Icc (0:ℝ) 1) := by
    simpa only [P,uIcc_of_le zero_le_one] using
      intervalIntegral.continuousOn_primitive_interval' hq
        (show (0:ℝ) ∈ uIcc 0 1 from left_mem_uIcc)
  have hPd (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt P (q t) t := by
    apply intervalIntegral.integral_hasDerivAt_right
      (hq.mono_set (uIcc_subset_uIcc left_mem_uIcc
        (by simpa only [uIcc_of_le zero_le_one] using Ioo_subset_Icc_self ht)))
      (hqcont.stronglyMeasurableAtFilter isOpen_Ioo t ht)
    exact (hqcont t ht).continuousAt (isOpen_Ioo.mem_nhds ht)
  let u : ℝ → ℂ := fun t => exp (-P t)*g t
  have hucont : ContinuousOn u (Icc (0:ℝ) 1) :=
    (Complex.continuous_exp.comp_continuousOn hPcont.neg).mul hgcont
  have hud (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt u 0 t := by
    convert ((hPd t ht).neg.cexp).mul (hg t ht) using 1 <;> first | rfl | ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    zero_le_one hucont hud (by simp : IntervalIntegrable (fun _ : ℝ => (0:ℂ)) volume 0 1)
  have hu : u 1 = u 0 := sub_eq_zero.mp (by simpa using hFTC.symm)
  have h0 : u 0 = g 0 := by simp [u,P]
  rw [h0] at hu
  have he : exp (P 1)*exp (-P 1) = 1 := by rw [← exp_add,add_neg_cancel,exp_zero]
  have heq := congrArg (fun z : ℂ => exp (P 1)*z) hu
  change exp (P 1)*(exp (-P 1)*g 1) = exp (P 1)*g 0 at heq
  rw [← mul_assoc,he,one_mul] at heq
  exact heq

/-- A logarithmic derivative determines an exponentiated path integral.
Continuity of `G` along the closed path permits singular endpoints. -/
theorem exp_curveIntegral_mul_eq_endpoint
    (f G : ℂ → ℂ) (D : Set ℂ) (hf : ContinuousOn f D)
    (hG : ∀ z ∈ D, HasDerivAt G (f z*G z) z)
    {a b : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγD : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ D)
    (hint : CurveIntegrable (holomorphicOneForm f) γ)
    (hGcont : ContinuousOn (G ∘ γ.extend) (Icc (0:ℝ) 1)) :
    exp (∫ᶜ z in γ, holomorphicOneForm f z)*G a = G b := by
  let q : ℝ → ℂ := fun t => f (γ.extend t)*deriv γ.extend t
  have heq : EqOn (curveIntegralFun (holomorphicOneForm f) γ) q (Ioo (0:ℝ) 1) := by
    intro t ht
    rw [curveIntegralFun_def,derivWithin_of_mem_nhds
      (Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Icc_self)]
    rfl
  have hq : IntervalIntegrable q volume 0 1 := hint.congr_uIoo
    (by simpa only [uIoo_of_le zero_le_one] using heq)
  have hqcont : ContinuousOn q (Ioo (0:ℝ) 1) :=
    (hf.comp (γ.continuous_extend.continuousOn) hγD).mul
      ((hγ.mono Ioo_subset_Icc_self).continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl)
  have hg (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (G ∘ γ.extend) (q t*(G ∘ γ.extend) t) t := by
    have hγdiff : DifferentiableAt ℝ γ.extend t :=
      (hγ.differentiableOn (by norm_num) t (Ioo_subset_Icc_self ht)).differentiableAt
        (Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Icc_self)
    convert (hG (γ.extend t) (hγD t ht)).scomp t hγdiff.hasDerivAt using 1 <;>
      first | rfl | simp only [q,Function.comp_def,smul_eq_mul]; ring
  have h := eq_exp_integral_mul_of_hasDerivAt q (G ∘ γ.extend) hq hqcont hGcont hg
  rw [curveIntegral_eq_intervalIntegral_deriv]
  simpa only [q,Function.comp_def,Path.extend_zero,Path.extend_one,holomorphicOneForm_apply] using h.symm

/-- Any two integrable paths with the same nonzero logarithmic
endpoint data have integrals differing by an integer multiple of `2πi`. -/
theorem curveIntegral_sub_eq_int_two_pi_I_of_logarithmic_derivative
    (f G : ℂ → ℂ) (D : Set ℂ) (hf : ContinuousOn f D)
    (hG : ∀ z ∈ D, HasDerivAt G (f z*G z) z)
    {a b : ℂ} (ha : G a ≠ 0) (γ₁ γ₂ : Path a b)
    (hγ₁ : ContDiffOn ℝ 1 γ₁.extend (Icc 0 1))
    (hγ₂ : ContDiffOn ℝ 1 γ₂.extend (Icc 0 1))
    (hγ₁D : ∀ t ∈ Ioo (0:ℝ) 1, γ₁.extend t ∈ D)
    (hγ₂D : ∀ t ∈ Ioo (0:ℝ) 1, γ₂.extend t ∈ D)
    (hint₁ : CurveIntegrable (holomorphicOneForm f) γ₁)
    (hint₂ : CurveIntegrable (holomorphicOneForm f) γ₂)
    (hGcont₁ : ContinuousOn (G ∘ γ₁.extend) (Icc (0:ℝ) 1))
    (hGcont₂ : ContinuousOn (G ∘ γ₂.extend) (Icc (0:ℝ) 1)) :
    ∃ k : ℤ, (∫ᶜ z in γ₁, holomorphicOneForm f z) -
      (∫ᶜ z in γ₂, holomorphicOneForm f z) = k*(2*Real.pi*Complex.I) := by
  have heq : exp (∫ᶜ z in γ₁, holomorphicOneForm f z) =
      exp (∫ᶜ z in γ₂, holomorphicOneForm f z) :=
    mul_right_cancel₀ ha ((exp_curveIntegral_mul_eq_endpoint f G D hf hG γ₁ hγ₁ hγ₁D hint₁ hGcont₁).trans
      (exp_curveIntegral_mul_eq_endpoint f G D hf hG γ₂ hγ₂ hγ₂D hint₂ hGcont₂).symm)
  obtain ⟨k,hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq
  exact ⟨k,by rw [hk]; ring⟩

end NLS.ComplexAnalysis
