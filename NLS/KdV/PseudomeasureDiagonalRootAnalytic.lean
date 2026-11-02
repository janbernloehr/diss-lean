import NLS.KdV.PseudomeasureDiagonalRoot
import NLS.KdV.PseudomeasureReconstructionAnalytic
import NLS.ComplexAnalysis.AnalyticImplicitRoot

/-! Norm continuity and complex analyticity of the actual original diagonal-root selection. -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.KdV
open NLS.ComplexAnalysis

/-- The actual root selection is continuous wherever the explicit contraction criterion is strict. -/
theorem continuousAt_endpointHillDiagonalRoot (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ < 1/2) :
    ContinuousAt (endpointHillDiagonalRoot r hr hr1 n hn) q := by
  let a := endpointHillDiagonalRoot r hr hr1 n hn
  let F := fun p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ =>
    fun z : ℂ => (freeHillValue n:ℂ)+endpointDiagonal r hr hr1 n (p,z)
  have hx := endpointHillDiagonalRoot_spec r hr hr1 n hn q hs.le
  have hc : Continuous (fun p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ =>
      endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p‖) := continuous_const.mul continuous_norm
  have hnear : ∀ᶠ p in 𝓝 q, endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p‖ ≤ 1/2 :=
    ((hc.tendsto q).eventually (gt_mem_nhds hs)).mono fun _ hp => hp.le
  apply NLS.FunctionalAnalysis.continuousAt_of_contracting_fixedPoints F a q (1/8:ℝ) (by norm_num)
  · exact hx.2.1.symm
  · filter_upwards [hnear] with p hp
    have hy := endpointHillDiagonalRoot_spec r hr hr1 n hn p hp
    refine ⟨hy.2.1.symm, ?_⟩
    simpa only [F, add_sub_add_left_eq_sub] using
      endpointDiagonal_sub_le_eighth r hr hr1 n hn (a p) (a q) hy.1 hx.1 p hp
  · have ha : AnalyticAt ℂ (endpointDiagonal r hr hr1 n) (q,a q) :=
      (analyticAt_endpointCoefficients r hr hr1 n hn (q,a q) hx.1 hs.le).1
    have hi : ContinuousAt (fun p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ => (p,a q)) q :=
      continuousAt_id.prodMk continuousAt_const
    have hd : ContinuousAt (fun p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ =>
        endpointDiagonal r hr hr1 n (p,a q)) q :=
      ha.continuousAt.comp (f := fun p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ => (p,a q)) hi
    exact continuousAt_const.add hd

/-- The derivative in the spectral direction is quantitatively small at the actual root. -/
theorem norm_deriv_endpointDiagonal_at_root_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    ‖deriv (fun z : ℂ => endpointDiagonal r hr hr1 n (q,z))
      (endpointHillDiagonalRoot r hr hr1 n hn q)‖ ≤ (1/8:ℝ) := by
  have hx := endpointHillDiagonalRoot_spec r hr hr1 n hn q hs
  apply norm_deriv_le_of_lip' (by norm_num)
  filter_upwards [eventually_mem_reducedHillStrip n _
    (endpointHillDiagonalRoot_interior r hr hr1 n hn q hs)] with z hz
  exact endpointDiagonal_sub_le_eighth r hr hr1 n hn z _ hz hx.1 q hs

/-- The intrinsic actual diagonal root is jointly a complex analytic function
of the full original endpoint potential wherever the cutoff criterion is strict. -/
theorem analyticAt_endpointHillDiagonalRoot (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ < 1/2) :
    AnalyticAt ℂ (endpointHillDiagonalRoot r hr hr1 n hn) q := by
  let a := endpointHillDiagonalRoot r hr hr1 n hn
  let F : ℂ × WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ → ℂ :=
    fun p => p.1-(freeHillValue n:ℂ)-endpointDiagonal r hr hr1 n (p.2,p.1)
  have hx := endpointHillDiagonalRoot_spec r hr hr1 n hn q hs.le
  have hdiag : AnalyticAt ℂ (endpointDiagonal r hr hr1 n) (q,a q) :=
    (analyticAt_endpointCoefficients r hr hr1 n hn (q,a q) hx.1 hs.le).1
  have hswap : AnalyticAt ℂ (fun p : ℂ × WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ =>
      endpointDiagonal r hr hr1 n (p.2,p.1)) (a q,q) := by
    have hi : AnalyticAt ℂ (fun p : ℂ × WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ =>
        (p.2,p.1)) (a q,q) := analyticAt_snd.prod analyticAt_fst
    exact hdiag.comp (x := (a q,q)) hi
  have hF : AnalyticAt ℂ F (a q,q) := (analyticAt_fst.sub analyticAt_const).sub hswap
  apply analyticAt_implicitRoot F a q hF (continuousAt_endpointHillDiagonalRoot r hr hr1 n hn q hs)
  · have hc : Continuous (fun p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ =>
        endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p‖) := continuous_const.mul continuous_norm
    filter_upwards [(hc.tendsto q).eventually (gt_mem_nhds hs)] with p hp
    have hroot := (endpointHillDiagonalRoot_spec r hr hr1 n hn p hp.le).2.1
    change a p-(freeHillValue n:ℂ)-endpointDiagonal r hr hr1 n (p,a p) = 0
    linear_combination hroot
  · rw [← deriv_spectral_section_eq_fderiv F (a q) q hF.differentiableAt]
    have hd := (hdiag.comp (f := fun z : ℂ => (q,z)) (analyticAt_const.prod analyticAt_id)).differentiableAt
    have he : deriv (fun z : ℂ => F (z,q)) (a q) =
        1-deriv (fun z : ℂ => endpointDiagonal r hr hr1 n (q,z)) (a q) :=
      (((hasDerivAt_id (a q)).sub_const (freeHillValue n:ℂ)).sub hd.hasDerivAt).deriv
    rw [he]
    intro hz
    have hder : deriv (fun z : ℂ => endpointDiagonal r hr hr1 n (q,z)) (a q) = 1 :=
      (sub_eq_zero.mp hz).symm
    have hb := norm_deriv_endpointDiagonal_at_root_le r hr hr1 n hn q hs.le
    rw [hder, norm_one] at hb
    norm_num at hb

end NLS.KdV
