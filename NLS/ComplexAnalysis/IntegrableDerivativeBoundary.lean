import NLS.ComplexAnalysis.InverseSqrtIntegral

/-!
# Boundary limit from an integrable derivative

A complex-valued function with an integrable derivative on a
punctured right neighborhood has a finite one-sided limit. The
result will be used for primitives along rays ending at a spectral
branch point.
-/

noncomputable section
open Set Filter Topology MeasureTheory
namespace NLS.ComplexAnalysis

/-- An integrable derivative on `(0, ε)` gives a finite limit from
the right, even if the original function is not defined continuously
at zero. -/
theorem exists_tendsto_zero_of_integrable_derivative
    (g q : ℝ → ℂ) (ε : ℝ) (hε : 0 < ε)
    (hq : IntegrableOn q (Ioo (0:ℝ) ε))
    (hg : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt g (q t) t) :
    ∃ A : ℂ, Tendsto g (𝓝[>] (0:ℝ)) (𝓝 A) ∧
      ∀ t ∈ Ioo (0:ℝ) (ε/2),
        g t = A + ∫ v in Ioc (0:ℝ) t, q v := by
  let t₀ := ε/2
  have ht₀ : t₀ ∈ Ioo (0:ℝ) ε := by
    dsimp [t₀]
    constructor <;> linarith
  let A := g t₀ - ∫ v in (0:ℝ)..t₀, q v
  have hlim : Tendsto (fun t : ℝ => ∫ v in Ioc (0:ℝ) t, q v)
      (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)) :=
    tendsto_integral_Ioc_zero_of_integrableOn_Ioo hε hq
  have hformula (t : ℝ) (ht : t ∈ Ioo (0:ℝ) t₀) :
      g t = A + ∫ v in Ioc (0:ℝ) t, q v := by
    have htt₀ : t < t₀ := ht.2
    have htε : t ∈ Ioo (0:ℝ) ε := ⟨ht.1,htt₀.trans ht₀.2⟩
    have hq0t : IntervalIntegrable q volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1.le).2
        (hq.mono_set (Ioo_subset_Ioo le_rfl htε.2.le))
    have hq_t_t₀ : IntervalIntegrable q volume t t₀ :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le htt₀.le).2
        (hq.mono_set (by
          intro v hv
          exact ⟨ht.1.trans hv.1,hv.2.trans ht₀.2⟩))
    have hcont : ContinuousOn g (Icc t t₀) := by
      intro v hv
      exact (hg v ⟨ht.1.trans_le hv.1,hv.2.trans_lt ht₀.2⟩).continuousAt.continuousWithinAt
    have hderiv (v : ℝ) (hv : v ∈ Ioo t t₀) : HasDerivAt g (q v) v :=
      hg v ⟨ht.1.trans hv.1,hv.2.trans ht₀.2⟩
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      htt₀.le hcont hderiv hq_t_t₀
    have hadd := intervalIntegral.integral_add_adjacent_intervals hq0t hq_t_t₀
    have hJ : (∫ v in t..t₀, q v) =
        (∫ v in (0:ℝ)..t₀, q v) - (∫ v in (0:ℝ)..t, q v) := by
      rw [eq_sub_iff_add_eq]
      simpa only [add_comm] using hadd
    have hcalc : g t = (g t₀ - (∫ v in (0:ℝ)..t₀, q v)) +
        (∫ v in (0:ℝ)..t, q v) := by
      calc
        g t = g t₀ - (∫ v in t..t₀, q v) := by rw [hFTC]; ring
        _ = (g t₀ - (∫ v in (0:ℝ)..t₀, q v)) +
            (∫ v in (0:ℝ)..t, q v) := by
              rw [hJ]
              ring
    rw [intervalIntegral.integral_of_le ht.1.le] at hcalc
    dsimp only [A]
    exact hcalc
  have heq : g =ᶠ[𝓝[>] (0:ℝ)]
      (fun t => A + ∫ v in Ioc (0:ℝ) t, q v) := by
    filter_upwards [Ioo_mem_nhdsGT ht₀.1] with t ht
    exact hformula t ht
  refine ⟨A,?_,?_⟩
  have hsum : Tendsto (fun t => A + ∫ v in Ioc (0:ℝ) t, q v)
      (𝓝[>] (0:ℝ)) (𝓝 A) := by
    simpa using (tendsto_const_nhds.add hlim :
      Tendsto (fun t => A + ∫ v in Ioc (0:ℝ) t, q v)
        (𝓝[>] (0:ℝ)) (𝓝 (A+0)))
  · exact hsum.congr' heq.symm
  · intro t ht
    exact hformula t (by simpa only [t₀] using ht)

/-- A primitive whose derivative is integrable along a short vertical
ray has a finite limit at the ray's boundary endpoint. -/
theorem exists_primitive_vertical_ray_limit
    (f F : ℂ → ℂ) (c : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hF : ∀ y ∈ Ioo (0:ℝ) ε,
      HasDerivAt F (f (c+(y:ℂ)*Complex.I)) (c+(y:ℂ)*Complex.I))
    (hint : IntegrableOn
      (fun y : ℝ => f (c+(y:ℂ)*Complex.I)) (Ioo (0:ℝ) ε)) :
    ∃ A : ℂ, Tendsto
      (fun y : ℝ => F (c+(y:ℂ)*Complex.I))
      (𝓝[>] (0:ℝ)) (𝓝 A) ∧
      ∀ y ∈ Ioo (0:ℝ) (ε/2),
        F (c+(y:ℂ)*Complex.I) = A +
          ∫ v in Ioc (0:ℝ) y, f (c+(v:ℂ)*Complex.I)*Complex.I := by
  let z (y : ℝ) : ℂ := c+(y:ℂ)*Complex.I
  let g (y : ℝ) : ℂ := F (z y)
  let q (y : ℝ) : ℂ := f (z y)*Complex.I
  have hq : IntegrableOn q (Ioo (0:ℝ) ε) := hint.mul_const Complex.I
  have hg (y : ℝ) (hy : y ∈ Ioo (0:ℝ) ε) :
      HasDerivAt g (q y) y := by
    have hzC : HasDerivAt (fun w : ℂ => c+w*Complex.I) Complex.I (y:ℂ) := by
      simpa using ((hasDerivAt_id (y:ℂ)).mul_const Complex.I).const_add c
    have hz : HasDerivAt z Complex.I y := by
      simpa only [z] using hzC.comp_ofReal
    simpa only [g,q,z,Function.comp_def,smul_eq_mul,mul_comm] using
      (hF y hy).scomp y hz
  obtain ⟨A,hA,hformula⟩ := exists_tendsto_zero_of_integrable_derivative
    g q ε hε hq hg
  exact ⟨A,hA,fun y hy => hformula y hy⟩

/-- A primitive whose derivative is integrable along a short downward vertical
ray has a finite limit at the ray's boundary endpoint. -/
theorem exists_primitive_downward_ray_limit
    (f F : ℂ → ℂ) (c : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hF : ∀ y ∈ Ioo (0:ℝ) ε,
      HasDerivAt F (f (c+((-y:ℝ):ℂ)*Complex.I)) (c+((-y:ℝ):ℂ)*Complex.I))
    (hint : IntegrableOn
      (fun y : ℝ => f (c+((-y:ℝ):ℂ)*Complex.I)) (Ioo (0:ℝ) ε)) :
    ∃ A : ℂ, Tendsto
      (fun y : ℝ => F (c+((-y:ℝ):ℂ)*Complex.I))
      (𝓝[>] (0:ℝ)) (𝓝 A) ∧
      ∀ y ∈ Ioo (0:ℝ) (ε/2),
        F (c+((-y:ℝ):ℂ)*Complex.I) = A +
          ∫ v in Ioc (0:ℝ) y,
            f (c+((-v:ℝ):ℂ)*Complex.I)*(-Complex.I) := by
  let z (y : ℝ) : ℂ := c+((-y:ℝ):ℂ)*Complex.I
  let g (y : ℝ) : ℂ := F (z y)
  let q (y : ℝ) : ℂ := f (z y)*(-Complex.I)
  have hq : IntegrableOn q (Ioo (0:ℝ) ε) := hint.mul_const (-Complex.I)
  have hg (y : ℝ) (hy : y ∈ Ioo (0:ℝ) ε) :
      HasDerivAt g (q y) y := by
    have hzC : HasDerivAt (fun w : ℂ => c+w*(-Complex.I)) (-Complex.I) (y:ℂ) := by
      simpa using ((hasDerivAt_id (y:ℂ)).mul_const (-Complex.I)).const_add c
    have hz : HasDerivAt z (-Complex.I) y := by
      simpa [z, mul_neg, neg_mul, sub_eq_add_neg] using hzC.comp_ofReal
    simpa only [g,q,z,Function.comp_def,smul_eq_mul,mul_comm] using
      (hF y hy).scomp y hz
  obtain ⟨A,hA,hformula⟩ := exists_tendsto_zero_of_integrable_derivative
    g q ε hε hq hg
  exact ⟨A,hA,fun y hy => hformula y hy⟩

end NLS.ComplexAnalysis
