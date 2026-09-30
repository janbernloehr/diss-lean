import NLS.ComplexAnalysis.SlitPrimitiveBoundary

/-!
# Primitive limits at complex segment endpoints

Translate and rescale a nondegenerate complex segment to `[0,1]`.
Near its left endpoint its complement agrees with the positive-ray
complement. The slit boundary theorem therefore gives a common
limit in any open neighborhood of the endpoint. Reversing the
segment treats the right endpoint.
-/

noncomputable section
open Set Filter Topology Complex Metric
namespace NLS.ComplexAnalysis

theorem affine_positiveSlit_avoids_segment
    (l r z : ℂ) (hlr : l ≠ r) (hz : z ∈ positiveSlitPlane) :
    l+(r-l)*z ∉ segment ℝ l r := by
  intro hs
  obtain ⟨t,ht,heq⟩ := by
    rw [segment_eq_image_lineMap] at hs
    exact hs
  have hd : r-l ≠ 0 := sub_ne_zero.mpr hlr.symm
  have hmul : (r-l)*z = (r-l)*(t:ℂ) := by
    rw [AffineMap.lineMap_apply_module] at heq
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one] at heq
    linear_combination -heq
  have hzreal : z = (t:ℂ) := mul_left_cancel₀ hd hmul
  rw [hzreal] at hz
  rcases hz with hr | hi
  · exact (not_lt_of_ge ht.1) hr
  · exact hi (by simp)

theorem positiveSlit_of_affine_not_mem_segment
    (l r z : ℂ) (hz : ‖z‖ < 1)
    (hs : l+(r-l)*z ∉ segment ℝ l r) : z ∈ positiveSlitPlane := by
  by_contra h
  have hri : 0 ≤ z.re ∧ z.im = 0 := by
    simpa [positiveSlitPlane,not_or,not_lt] using h
  have hreal : z = (z.re:ℂ) := by apply Complex.ext <;> simp [hri.2]
  have hle : z.re ≤ 1 := ((Complex.re_le_norm z).trans hz.le)
  apply hs
  have hmem := lineMap_mem_segment ℝ l r (show z.re ∈ Icc (0:ℝ) 1 from ⟨hri.1,hle⟩)
  convert hmem using 1
  rw [AffineMap.lineMap_apply_module]
  simp only [Complex.real_smul,Complex.ofReal_sub,Complex.ofReal_one]
  conv_lhs => rw [hreal]
  ring

/-- A primitive with the simple-branch-point derivative bound has one
limit at the left endpoint of any complex segment, in the full local
cut complement. -/
theorem exists_primitive_segment_left_boundary_limit
    (f F : ℂ → ℂ) (Ω : Set ℂ) (l r : ℂ) (δ M ε : ℝ)
    (hΩ : IsOpen Ω) (hl : l ∈ Ω) (hlr : l ≠ r)
    (hδ : 0 < δ) (hM : 0 ≤ M) (hε : 0 < ε)
    (hf : ContinuousOn f (Ω \ segment ℝ l r))
    (hF : ∀ z ∈ Ω \ segment ℝ l r, HasDerivAt F (f z) z)
    (hbound : ∀ z ∈ Ω \ segment ℝ l r, ‖z-l‖ ≤ ε →
      ‖f z * (Real.sqrt (δ*‖z-l‖) : ℂ)‖ ≤ M) :
    ∃ A : ℂ, Tendsto F (𝓝[Ω \ segment ℝ l r] l) (𝓝 A) := by
  obtain ⟨α,hα,hball⟩ := Metric.isOpen_iff.mp hΩ l hl
  let d := r-l
  have hd : d ≠ 0 := sub_ne_zero.mpr hlr.symm
  have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd
  let η := min (α/‖d‖) (ε/‖d‖)
  have hη : 0 < η := lt_min (div_pos hα hdn) (div_pos hε hdn)
  let T : ℂ → ℂ := fun z => l+d*z
  let f' : ℂ → ℂ := fun z => f (T z)*d
  let F' : ℂ → ℂ := fun z => F (T z)
  have hdist (z : ℂ) : ‖T z-l‖ = ‖d‖*‖z‖ := by
    dsimp [T]
    rw [add_sub_cancel_left,norm_mul]
  have hsmall (z : ℂ) (hz : z ∈ ball 0 η) :
      ‖T z-l‖ < α ∧ ‖T z-l‖ ≤ ε := by
    have hn : ‖z‖ < η := by simpa [mem_ball,dist_eq_norm] using hz
    have h₁ : ‖z‖ < α/‖d‖ := hn.trans_le (min_le_left _ _)
    have h₂ : ‖z‖ < ε/‖d‖ := hn.trans_le (min_le_right _ _)
    rw [hdist]
    constructor
    · nlinarith [(lt_div_iff₀ hdn).mp h₁]
    · nlinarith [(lt_div_iff₀ hdn).mp h₂]
  have hT (z : ℂ) (hz : z ∈ ball 0 η ∩ positiveSlitPlane) :
      T z ∈ Ω \ segment ℝ l r := by
    refine ⟨hball ?_,affine_positiveSlit_avoids_segment l r z hlr hz.2⟩
    simpa only [mem_ball,dist_eq_norm] using (hsmall z hz.1).1
  have hf' : ContinuousOn f' (ball 0 η ∩ positiveSlitPlane) :=
    (hf.comp (by fun_prop) hT).mul continuousOn_const
  have hF' (z : ℂ) (hz : z ∈ ball 0 η ∩ positiveSlitPlane) :
      HasDerivAt F' (f' z) z := by
    have hTderiv : HasDerivAt T d z := by
      simpa only [T,id_eq,mul_one,mul_comm] using ((hasDerivAt_id z).mul_const d).const_add l
    exact (hF _ (hT z hz)).comp z hTderiv
  have hb' (z : ℂ) (hz : z ∈ ball 0 η ∩ positiveSlitPlane) :
      ‖f' z * (Real.sqrt ((δ*‖d‖)*‖z‖) : ℂ)‖ ≤ ‖d‖*M := by
    have hb := hbound _ (hT z hz) (hsmall z hz.1).2
    rw [hdist,← mul_assoc] at hb
    simpa only [f',norm_mul,mul_comm,mul_left_comm,mul_assoc] using
      mul_le_mul_of_nonneg_left hb hdn.le
  obtain ⟨A,hA⟩ := exists_primitive_positiveSlit_boundary_limit f' F'
    (δ*‖d‖) (‖d‖*M) η (mul_pos hδ hdn) (mul_nonneg hdn.le hM) hη hf' hF' hb'
  let H : ℂ → ℂ := fun z => (z-l)/d
  have hTH (z : ℂ) : T (H z) = z := by
    dsimp [T,H]
    rw [mul_div_cancel₀ _ hd]
    ring
  have hHlim : Tendsto H (𝓝[Ω \ segment ℝ l r] l) (𝓝 (0:ℂ)) := by
    have hcont : ContinuousAt H l := by fun_prop
    simpa [H] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hHslit : Tendsto H (𝓝[Ω \ segment ℝ l r] l) (𝓝[positiveSlitPlane] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hHlim,?_⟩
    have hnorm : Tendsto (fun z => ‖H z‖)
        (𝓝[Ω \ segment ℝ l r] l) (𝓝 (0:ℝ)) := by simpa using hHlim.norm
    filter_upwards [self_mem_nhdsWithin,hnorm.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))]
      with z hz hn
    apply positiveSlit_of_affine_not_mem_segment l r (H z) hn
    change T (H z) ∉ segment ℝ l r
    rw [hTH]
    exact hz.2
  refine ⟨A,?_⟩
  convert hA.comp hHslit using 1
  funext z
  exact (congrArg F (hTH z)).symm

/-- The common boundary limit also holds at the right endpoint. -/
theorem exists_primitive_segment_right_boundary_limit
    (f F : ℂ → ℂ) (Ω : Set ℂ) (l r : ℂ) (δ M ε : ℝ)
    (hΩ : IsOpen Ω) (hr : r ∈ Ω) (hlr : l ≠ r)
    (hδ : 0 < δ) (hM : 0 ≤ M) (hε : 0 < ε)
    (hf : ContinuousOn f (Ω \ segment ℝ l r))
    (hF : ∀ z ∈ Ω \ segment ℝ l r, HasDerivAt F (f z) z)
    (hbound : ∀ z ∈ Ω \ segment ℝ l r, ‖z-r‖ ≤ ε →
      ‖f z * (Real.sqrt (δ*‖z-r‖) : ℂ)‖ ≤ M) :
    ∃ A : ℂ, Tendsto F (𝓝[Ω \ segment ℝ l r] r) (𝓝 A) := by
  rw [segment_symm ℝ l r] at hf hF hbound ⊢
  exact exists_primitive_segment_left_boundary_limit f F Ω r l δ M ε
    hΩ hr hlr.symm hδ hM hε hf hF hbound

end NLS.ComplexAnalysis
