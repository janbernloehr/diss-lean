import NLS.ComplexAnalysis.DenseAnalyticExtension
import NLS.ComplexAnalysis.CosinePrimitiveSheetContinuation
import NLS.ComplexAnalysis.LocalAnalyticSquareRoot

/-! # Squared gap primitives extend across the whole cut

Local regular root sheets differ by a sign, which disappears after
squaring the endpoint-normalized primitive. The endpoint limits remove
the last two singularities. Collapsed segments are included.
-/
noncomputable section
open Set Filter Topology Complex
namespace NLS.ComplexAnalysis

def gapPrimitiveSquareExtension (F : ℂ → ℂ) (l r : ℂ) : ℂ → ℂ :=
  denseLimitExtension (fun z => F z^2) (segment ℝ l r)ᶜ

/-- Squaring removes the sheet sign at every interior cut point; zero
endpoint limits give analytic continuation through both endpoints. -/
theorem gapPrimitiveSquareExtension_spec
    (g Q F : ℂ → ℂ) (Ω : Set ℂ) (l r : ℂ)
    (hΩ : IsOpen Ω) (hgap : segment ℝ l r ⊆ Ω)
    (hg : AnalyticOnNhd ℂ g Ω)
    (hQ : ContinuousOn Q (Ω \ segment ℝ l r))
    (hsq : ∀ z ∈ Ω \ segment ℝ l r, Q z^2 = (l-z)*(r-z))
    (hF : ∀ z ∈ Ω \ segment ℝ l r, HasDerivAt F (g z/Q z) z)
    (hl : Tendsto F (𝓝[Ω \ segment ℝ l r] l) (𝓝 0))
    (hr : Tendsto F (𝓝[Ω \ segment ℝ l r] r) (𝓝 0)) :
    AnalyticOnNhd ℂ (gapPrimitiveSquareExtension F l r) Ω ∧
      EqOn (gapPrimitiveSquareExtension F l r) (fun z => F z^2) (Ω \ segment ℝ l r) ∧
      gapPrimitiveSquareExtension F l r l = 0 ∧ gapPrimitiveSquareExtension F l r r = 0 := by
  let K := segment ℝ l r
  have hK : IsClosed K := by
    apply IsCompact.isClosed
    change IsCompact (segment ℝ l r)
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hDense : Dense Kᶜ := dense_complex_segment_complement l r
  have hFa : AnalyticOnNhd ℂ F (Ω \ K) :=
    (show DifferentiableOn ℂ F (Ω \ K) from fun z hz =>
      (hF z hz).differentiableAt.differentiableWithinAt).analyticOnNhd (hΩ.sdiff hK)
  have hmatch : EqOn (gapPrimitiveSquareExtension F l r) (fun z => F z^2) (Ω \ K) := by
    apply denseLimitExtension_eqOn_local _ _ Kᶜ (Ω \ K) hDense (hΩ.sdiff hK) (hFa.pow 2).continuousOn
    intro z _
    rfl
  have hlim (a : ℂ) (ha : a ∈ ({l,r} : Set ℂ)) :
      Tendsto (fun z => F z^2) (𝓝[Kᶜ] a) (𝓝 0) := by
    have haΩ : a ∈ Ω := by
      rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using ha : a=l ∨ a=r) with rfl | rfl
      · exact hgap (left_mem_segment ℝ _ _)
      · exact hgap (right_mem_segment ℝ _ _)
    have ht : Tendsto F (𝓝[Ω \ K] a) (𝓝 0) := by
      rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using ha : a=l ∨ a=r) with rfl | rfl
      · exact hl
      · exact hr
    rw [Set.sdiff_eq,nhdsWithin_inter_of_mem (nhdsWithin_le_nhds (hΩ.mem_nhds haΩ))] at ht
    simpa only [zero_pow (by norm_num : 2 ≠ 0)] using ht.pow 2
  have ha : AnalyticOnNhd ℂ (gapPrimitiveSquareExtension F l r) (Ω \ {l,r}) := by
    apply denseLimitExtension_analyticOnNhd _ Kᶜ _ hDense
    intro b hb
    have hbl : b ≠ l := by intro h; apply hb.2; simp [h]
    have hbr : b ≠ r := by intro h; apply hb.2; simp [h]
    by_cases hbK : b ∈ K
    · have hlr : l ≠ r := by
        intro h
        have hbk : b = l := by simpa only [K,h,segment_same,mem_singleton_iff] using hbK
        exact hbl hbk
      let τ := (l+r)/2
      let δ := (r-l)/2
      have hτl : τ-δ = l := by dsimp [τ,δ]; ring
      have hτr : τ+δ = r := by dsimp [τ,δ]; ring
      have hδ : δ ≠ 0 := div_ne_zero (sub_ne_zero.mpr hlr.symm) (by norm_num)
      let f : ℂ → ℂ := fun z => (l-z)*(r-z)
      have hfb : f b ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hbl.symm) (sub_ne_zero.mpr hbr.symm)
      let w := prescribedSquareRoot f 1 b
      have hwsq : w^2 = f b := prescribedSquareRoot_sq f 1 one_ne_zero b
      have hw : w ≠ 0 := by
        intro he
        rw [he,zero_pow (by norm_num : 2 ≠ 0)] at hwsq
        exact hfb hwsq.symm
      obtain ⟨V,hV,hbV,R,hRa,_,hR⟩ := exists_local_analytic_squareRoot f b w
        ((analyticAt_const.sub analyticAt_id).mul (analyticAt_const.sub analyticAt_id)) hw hwsq.symm
      obtain ⟨B,P,hB,hbB,hBsub,hPa,_,hPm⟩ := exists_gap_interior_regular_sheet_primitive
        g Q F R Ω V τ δ 0 b hΩ hδ (by rw [hτl,hτr]; exact hgap) hg
        (by rw [hτl,hτr]; exact hQ) (by rw [hτl,hτr]; exact hsq)
        (by rw [hτl,hτr]; exact hF) (by rw [hτl,hτr]; exact hl)
        (by rw [hτl,hτr]; exact hbK) (by rwa [hτl]) (by rwa [hτr])
        hV hbV hRa (by rw [hτl,hτr]; exact fun z hz => (hR z hz).2)
      refine ⟨B,fun z => P z^2,hB,hbB,hPa.pow 2,?_⟩
      intro z hz
      change P z^2 = F z^2
      rw [hPm z hz.1 (by rw [hτl,hτr]; exact hz.2),sub_zero,mul_pow,div_pow,
        hsq z ⟨(hBsub hz.1).1,hz.2⟩,← (show R z^2 = (l-z)*(r-z) from (hR z (hBsub hz.1).2).2),
        div_self (pow_ne_zero 2 (hR z (hBsub hz.1).2).1),one_mul]
    · exact ⟨Ω \ K,fun z => F z^2,hΩ.sdiff hK,⟨hb.1,hbK⟩,hFa.pow 2,fun _ _ => rfl⟩
  refine ⟨?_,hmatch,?_,?_⟩
  · exact denseLimitExtension_analyticOnNhd_of_finite_boundary (fun z => F z^2) Kᶜ Ω {l,r} 0
      hDense hΩ (by simp) ha (fun z hz => hmatch ⟨hz.1.1,hz.2⟩)
      (fun a ha => hlim a ha.2)
  · exact denseLimitExtension_eq_of_tendsto _ Kᶜ hDense l 0 (hlim l (by simp))
  · exact denseLimitExtension_eq_of_tendsto _ Kᶜ hDense r 0 (hlim r (by simp))

end NLS.ComplexAnalysis
