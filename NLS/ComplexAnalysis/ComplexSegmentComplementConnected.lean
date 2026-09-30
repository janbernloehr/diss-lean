import NLS.ComplexAnalysis.DenseSegmentComplement
import Mathlib.Analysis.Convex.PathConnected

/-!
# Connecting an open convex domain around a complex segment cut

Points on either side of the cut join a small upper or lower anchor near
its left endpoint. The anchors join around that endpoint through a point
outside the segment. This gives paths throughout the cut complement.
-/

noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

def complexSegmentCoordinate (l r z : ℂ) : ℂ := (z-l)/(r-l)

theorem complexSegmentCoordinate_lineMap (l r z a : ℂ) (t : ℝ) :
    complexSegmentCoordinate l r (AffineMap.lineMap z a t) =
      (1-(t:ℂ))*complexSegmentCoordinate l r z+(t:ℂ)*complexSegmentCoordinate l r a := by
  simp only [complexSegmentCoordinate,AffineMap.lineMap_apply_module,Complex.real_smul,
    Complex.ofReal_sub,Complex.ofReal_one]
  ring

theorem complexSegmentCoordinate_affine (l r u : ℂ) (hlr : l ≠ r) :
    complexSegmentCoordinate l r (l+(r-l)*u) = u := by
  dsimp only [complexSegmentCoordinate]
  rw [add_sub_cancel_left,mul_div_cancel_left₀ _ (sub_ne_zero.mpr hlr.symm)]

theorem complexSegmentCoordinate_im_eq_zero (l r z : ℂ) (hlr : l ≠ r)
    (hz : z ∈ segment ℝ l r) : (complexSegmentCoordinate l r z).im = 0 := by
  obtain ⟨t,ht,rfl⟩ := by rw [segment_eq_image_lineMap] at hz; exact hz
  have he : AffineMap.lineMap l r t = l+(r-l)*(t:ℂ) := by
    simp only [AffineMap.lineMap_apply_module,Complex.real_smul,
      Complex.ofReal_sub,Complex.ofReal_one]
    ring
  rw [he,complexSegmentCoordinate_affine l r _ hlr]
  simp

/-- A segment to a strictly signed-imaginary point avoids the cut if
its starting point is outside the cut and on the same closed side. -/
theorem segment_avoids_complex_cut_of_signed_im
    (l r z a : ℂ) (σ : ℝ) (hlr : l ≠ r) (hz : z ∉ segment ℝ l r)
    (hzi : 0 ≤ σ*(complexSegmentCoordinate l r z).im)
    (hai : 0 < σ*(complexSegmentCoordinate l r a).im) :
    segment ℝ z a ⊆ (segment ℝ l r)ᶜ := by
  intro q hq hcut
  obtain ⟨t,ht,rfl⟩ := by rw [segment_eq_image_lineMap] at hq; exact hq
  by_cases ht0 : t = 0
  · subst t
    exact hz (by simpa using hcut)
  have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hi := complexSegmentCoordinate_im_eq_zero l r _ hlr hcut
  rw [complexSegmentCoordinate_lineMap] at hi
  have hpos : 0 < σ*((1-(t:ℂ))*complexSegmentCoordinate l r z+
      (t:ℂ)*complexSegmentCoordinate l r a).im := by
    simp only [Complex.add_im,Complex.mul_im,Complex.sub_re,Complex.one_re,
      Complex.ofReal_re,Complex.sub_im,Complex.one_im,Complex.ofReal_im,sub_zero,
      zero_mul,add_zero]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) hzi,mul_pos htp hai]
  rw [hi,mul_zero] at hpos
  exact lt_irrefl 0 hpos

/-- Removing a nondegenerate complex segment from an open convex domain
containing its left endpoint leaves a path-connected set. -/
theorem isPathConnected_convex_complex_segment_complement
    (Ω : Set ℂ) (l r : ℂ) (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω)
    (hl : l ∈ Ω) (hlr : l ≠ r) : IsPathConnected (Ω \ segment ℝ l r) := by
  let T : ℂ → ℂ := fun u => l+(r-l)*u
  have hT : Continuous T := by dsimp [T]; fun_prop
  have h0 : (0:ℂ) ∈ T ⁻¹' Ω := by simpa [T] using hl
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (hΩ.preimage hT) 0 h0
  let η := ε/2
  have hη : 0 < η := by dsimp [η]; linarith
  let a := T ((η:ℂ)*I)
  let b := T (-((η:ℂ)*I))
  let c := T (-((η:ℂ)))
  have haΩ : a ∈ Ω := hball (by
    simp only [mem_ball,dist_zero_right,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      norm_I,mul_one,abs_of_pos hη]
    dsimp [η]; linarith)
  have hbΩ : b ∈ Ω := hball (by
    simp only [mem_ball,dist_zero_right,norm_neg,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      norm_I,mul_one,abs_of_pos hη]
    dsimp [η]; linarith)
  have hcΩ : c ∈ Ω := hball (by
    simp only [mem_ball,dist_zero_right,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hη]
    dsimp [η]; linarith)
  have hai : (complexSegmentCoordinate l r a).im = η := by
    rw [complexSegmentCoordinate_affine l r _ hlr]
    simp
  have hbi : (complexSegmentCoordinate l r b).im = -η := by
    rw [complexSegmentCoordinate_affine l r _ hlr]
    simp
  have hci : (complexSegmentCoordinate l r c).im = 0 := by
    rw [complexSegmentCoordinate_affine l r _ hlr]
    simp
  have hcK : c ∉ segment ℝ l r := affine_positiveSlit_avoids_segment l r _ hlr
    (Or.inl (by simpa using neg_neg_of_pos hη))
  have hseg (z : ℂ) (hz : z ∈ Ω \ segment ℝ l r) (v : ℂ) (hv : v ∈ Ω) (σ : ℝ)
      (hzi : 0 ≤ σ*(complexSegmentCoordinate l r z).im)
      (hvi : 0 < σ*(complexSegmentCoordinate l r v).im) :
      segment ℝ z v ⊆ Ω \ segment ℝ l r := fun q hq =>
    ⟨hconv.segment_subset hz.1 hv hq,
      segment_avoids_complex_cut_of_signed_im l r z v σ hlr hz.2 hzi hvi hq⟩
  have hca := hseg c ⟨hcΩ,hcK⟩ a haΩ 1 (by simp [hci]) (by simpa [hai] using hη)
  have hcb := hseg c ⟨hcΩ,hcK⟩ b hbΩ (-1) (by simp [hci]) (by simpa [hbi] using hη)
  refine ⟨a,(hca (right_mem_segment ℝ _ _)),?_⟩
  intro z hz
  by_cases hi : 0 ≤ (complexSegmentCoordinate l r z).im
  · exact (JoinedIn.of_segment_subset (hseg z hz a haΩ 1 (by simpa using hi)
      (by simpa [hai] using hη))).symm
  · have hzb := hseg z hz b hbΩ (-1) (by simpa using (neg_pos.mpr (lt_of_not_ge hi)).le)
      (by simpa [hbi] using hη)
    exact (JoinedIn.of_segment_subset hca).symm.trans
      ((JoinedIn.of_segment_subset hcb).trans (JoinedIn.of_segment_subset hzb).symm)

end NLS.ComplexAnalysis
