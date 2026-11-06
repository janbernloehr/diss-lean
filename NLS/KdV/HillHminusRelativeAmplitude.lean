import NLS.KdV.HillHminusIsospectralActionGerms

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

/-- The positive physical amplitude, expressed through the relative action. -/
def hillHminusRelativeAmplitude (q : RealPeriodOneHillPotential) (n : ℕ)
    (a : PeriodOneHminusOne) : ℂ :=
  Complex.sqrt (2 * hillHminusRelativeAction q.val q.property.1 q.property.2 n a)

/-- At every open selected gap there is an analytic H-minus-one amplitude
whose L2 germ is the ORIGINAL positive action amplitude at EVERY original
isospectral point. The square-root sign follows from real positivity. -/
theorem exists_hillHminusRelativeAmplitude_isospectral_physical_germs
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ hillOriginalHminusSource q.val ∈ U ∧
      AnalyticOnNhd ℂ (hillHminusRelativeAmplitude q n) U ∧
      ∀ p : RealPeriodOneHillPotential,
        (∀ E : ℂ, hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E =
          hillL2Discriminant (SpectralWeight.one.toCoeff p.val) E) →
        ∃ V : Set RealPeriodOneHillPotential, IsOpen V ∧ p ∈ V ∧
          ∀ r ∈ V, hillHminusRelativeAmplitude q n (hillOriginalHminusSource r.val) =
            (Real.sqrt (2 * hillRealGapIntegral r.val r.property.1 r.property.2 n 0) : ℂ) := by
  obtain ⟨U,hU,hqU,hA,hmatch⟩ :=
    exists_hillHminusRelativeAction_isospectral_physical_germs q n hn
  let B : PeriodOneHminusOne → ℂ := fun a =>
    2 * hillHminusRelativeAction q.val q.property.1 q.property.2 n a
  have hB : AnalyticOnNhd ℂ B U := analyticOnNhd_const.mul hA
  let W := U ∩ B ⁻¹' slitPlane
  have hW : IsOpen W := hB.continuousOn.isOpen_inter_preimage hU Complex.isOpen_slitPlane
  have hpos : 0 < hillRealGapIntegral q.val q.property.1 q.property.2 n 0 := by
    apply (hillRealGapIntegral_pos_iff q.val q.property.1 q.property.2 n hn).mpr
    have hle := monotone_hillRealLabels q.val q.property.1 q.property.2
      (show 2*n-1 ≤ 2*n by omega)
    apply lt_of_le_of_ne hle
    intro he
    apply hgap
    simp only [hillRealGapHalfLength,he,sub_self,zero_div]
  have hqW : hillOriginalHminusSource q.val ∈ W := by
    refine ⟨hqU,?_⟩
    change 2 * hillHminusRelativeAction q.val q.property.1 q.property.2 n
      (hillOriginalHminusSource q.val) ∈ slitPlane
    rw [hillHminusRelativeAction_base q n hn]
    apply Or.inl
    simpa using
      (mul_pos (by norm_num : (0:ℝ)<2) hpos)
  refine ⟨W,hW,hqW,?_,?_⟩
  · intro a ha
    exact (Complex.differentiableOn_sqrt.analyticAt
      (Complex.isOpen_slitPlane.mem_nhds ha.2)).comp (hB a ha.1)
  · intro p hΔ
    obtain ⟨V,hV,hp,hmatch⟩ := hmatch p hΔ
    refine ⟨V,hV,hp,?_⟩
    intro r hr
    unfold hillHminusRelativeAmplitude
    rw [hmatch r hr]
    have hnonneg : 0 ≤ hillRealGapIntegral r.val r.property.1 r.property.2 n 0 := by
      simpa only [mul_zero] using hillRealGapIntegral_nonneg_even r.val r.property.1 r.property.2 n hn 0
    rw [show (2:ℂ) * (hillRealGapIntegral r.val r.property.1 r.property.2 n 0 : ℂ) =
        ((2 * hillRealGapIntegral r.val r.property.1 r.property.2 n 0 : ℝ) : ℂ) by push_cast; rfl]
    rw [Complex.sqrt_of_nonneg (by exact_mod_cast (mul_nonneg (by norm_num : (0:ℝ)≤2) hnonneg)),ofReal_re]

end NLS.KdV
