import NLS.ComplexAnalysis.NormalizedSquareRootBounds
import NLS.ComplexAnalysis.EntireEvenSquareDescent
import NLS.ZakharovShabat.SourceGapInterpolationOuterCircles

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

/-- A square-root frequency after a fixed energy shift, chosen close to
the original frequency even on the imaginary axis and across the slit. -/
def closeShiftedFrequency (z c : ℂ) : ℂ := z*Complex.sqrt (1+c/z^2)

theorem closeShiftedFrequency_sq (z c : ℂ) (hz : z≠0) :
    closeShiftedFrequency z c^2=z^2+c := by
  rw [closeShiftedFrequency,mul_pow,complex_sqrt_sq]
  field_simp

theorem norm_closeShiftedFrequency_sub_le (z c : ℂ) (hz : z≠0) :
    ‖closeShiftedFrequency z c-z‖≤‖c‖/‖z‖ := by
  have he : closeShiftedFrequency z c-z=z*(Complex.sqrt (1+c/z^2)-1) := by
    unfold closeShiftedFrequency
    ring
  rw [he,norm_mul]
  calc
    _ ≤ ‖z‖*‖c/z^2‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
      have hh := norm_sqrt_sub_one_le (1+c/z^2)
      rw [show (1+c/z^2)-1=c/z^2 by ring] at hh
      exact hh
    _ = ‖c‖/‖z‖ := by rw [norm_div,norm_pow]; field_simp

/-- On every sufficiently large central circle, one shifted frequency
is arbitrarily close, remains large, and avoids every free spectral disc. -/
theorem exists_closeShiftedFrequency_central_bounds (c : ℂ) (T : ℝ) :
    ∃ K : ℕ, ∀ k : ℕ, K≤k → ∀ z∈sphere (0:ℂ) (NLS.ZakharovShabat.centralCircleRadius k),
      closeShiftedFrequency z c^2=z^2+c ∧
      ‖closeShiftedFrequency z c-z‖≤min 1 (Real.pi/4) ∧
      T≤‖z‖ ∧ T≤‖closeShiftedFrequency z c‖ ∧
      ‖z‖≤2*‖closeShiftedFrequency z c‖ ∧
      ∀ m : ℤ, Real.pi/4≤‖closeShiftedFrequency z c-(Real.pi:ℂ)*m‖ := by
  let δ : ℝ := min 1 (Real.pi/4)
  have hδ : 0<δ := lt_min (by norm_num) (by positivity)
  obtain ⟨K,hK⟩ := exists_nat_gt ((max (T+1) (‖c‖/δ+2))/Real.pi)
  refine ⟨K,?_⟩
  intro k hk z hz
  have hnorm : ‖z‖=NLS.ZakharovShabat.centralCircleRadius k := by simpa only [mem_sphere,dist_zero_right] using hz
  have hlarge : max (T+1) (‖c‖/δ+2)<‖z‖ := by
    have hK' := (div_lt_iff₀ Real.pi_pos).mp hK
    have hkk : (K:ℝ)≤k := by exact_mod_cast hk
    rw [hnorm]
    unfold NLS.ZakharovShabat.centralCircleRadius
    nlinarith [Real.pi_pos]
  have h2 : 2<‖z‖ := by
    have hb := (le_max_right (T+1) (‖c‖/δ+2)).trans_lt hlarge
    linarith [div_nonneg (norm_nonneg c) hδ.le]
  have hz0 : z≠0 := norm_pos_iff.mp (by linarith)
  have hclose : ‖closeShiftedFrequency z c-z‖≤δ := by
    apply (norm_closeShiftedFrequency_sub_le z c hz0).trans
    apply (div_le_iff₀ (by linarith : 0<‖z‖)).mpr
    have hb := (le_max_right (T+1) (‖c‖/δ+2)).trans_lt hlarge
    have hh := (div_lt_iff₀ hδ).mp (show ‖c‖/δ<‖z‖ by linarith)
    nlinarith
  have hnormcomp := norm_sub_norm_le z (closeShiftedFrequency z c)
  rw [norm_sub_rev] at hnormcomp
  have hclose1 := hclose.trans (min_le_left 1 (Real.pi/4))
  refine ⟨closeShiftedFrequency_sq z c hz0,hclose,?_,?_,?_,?_⟩
  · have hb := (le_max_left (T+1) (‖c‖/δ+2)).trans_lt hlarge
    linarith
  · have hb := (le_max_left (T+1) (‖c‖/δ+2)).trans_lt hlarge
    linarith
  · linarith
  · intro m
    have hsep := NLS.ZakharovShabat.centralCircle_lattice_gap k hz m
    have htri := norm_sub_le_norm_sub_add_norm_sub z (closeShiftedFrequency z c) ((Real.pi:ℂ)*m)
    rw [norm_sub_rev z (closeShiftedFrequency z c)] at htri
    have hc := hclose.trans (min_le_right 1 (Real.pi/4))
    linarith

end NLS.ComplexAnalysis
