import NLS.KdV.MiuraFractionalFreeComparison
import NLS.KdV.HminusOneDirichletEigenfunctionComparison
import NLS.ZakharovShabat.FreeSineDisplacementBound

/-! # Quantitative fractional comparison at actual Miura Dirichlet roots

The sine normalization is fixed before choosing the root. A root in the
usual free disc has the same fractional decay as the full solution error.
-/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.ZakharovShabat NLS.WeightedCoeff
namespace NLS.KdV

theorem norm_miuraDirichletSineCurve_sub_free_le
    (u : Coeff 2) (z : ℂ) (n : ℕ+) (hz : ‖z-(Real.pi:ℂ)*(n:ℕ)‖ ≤ 1) :
    ‖hillMiuraDirichletSineCurve u z-dirichletFreeSineCurve n‖ ≤
      ‖l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z (1,I)-
        l2SolutionCurve 0 z (1,I)‖+2*‖z-(Real.pi:ℂ)*(n:ℕ)‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have hcol := (l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z (1,I)-
    l2SolutionCurve 0 z (1,I)).norm_coe_le_norm t
  change ‖l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z (1,I) t-
    l2SolutionCurve 0 z (1,I) t‖ ≤ _ at hcol
  rw [l2SolutionCurve_free] at hcol
  have hcenter : ((Real.pi*(n:ℝ):ℝ):ℂ) = (Real.pi:ℂ)*(n:ℕ) := by simp
  have hshift := norm_classicalFreeFrequencyDifference_le z (Real.pi*(n:ℝ)) (1,I)
    (by rw [hcenter]; exact hz) t
  dsimp only [classicalFreeFrequencyDifference] at hshift
  have hv : ‖((1,I):ℂ × ℂ)‖ = 1 := by simp
  rw [hcenter,hv,mul_one] at hshift
  have ht := norm_add_le
    (l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z (1,I) t-classicalFreeVector z (1,I) t)
    (classicalFreeVector z (1,I) t-classicalFreeVector (Real.pi*(n:ℝ)) (1,I) t)
  rw [sub_add_sub_cancel] at ht
  have hp := norm_miuraDirichletSinePosition_le
    (l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z (1,I) t-
      classicalFreeVector (Real.pi*(n:ℝ)) (1,I) t)
  rw [map_sub,miuraDirichletSinePosition_free] at hp
  change ‖hillMiuraDirichletSineCurve u z t-dirichletFreeSineCurve n t‖ ≤ _
  exact hp.trans (ht.trans (add_le_add hcol hshift))

/-- One universal constant works for all fractional exponents, all complex
Sobolev sources and all actual nonzero auxiliary roots in the free discs. -/
theorem exists_miura_fractional_dirichlet_comparison_constant :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ) (hs : 0 ≤ s), s ≤ 1 → ∀
      (u : WeightedCoeff (Weight.sobolev s) 2) (R : ℝ),
      ‖sobolevToL2 hs u‖ ≤ R → ∀ (n : ℕ+) (z : ℂ),
      ‖z-(Real.pi:ℂ)*(n:ℕ)‖ ≤ Real.pi/4 →
      auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
        (hillMiuraDiagonal (sobolevToL2 hs u)) z = 0 →
      ‖hillMiuraDirichletSineCurve (sobolevToL2 hs u) z-dirichletFreeSineCurve n‖ ≤
        C*miuraFractionalFreeConstant R 1*(n:ℝ)^(-s)*‖u‖ := by
  obtain ⟨B,hB,hdisp⟩ := exists_freeDisc_sine_displacement_bound
    (r := Real.pi/4) (by nlinarith [Real.pi_pos])
  refine ⟨1+2*B,by positivity,?_⟩
  intro s hs hs1 u R hR n z hdisk hroot
  have hn : (1:ℝ) ≤ n := by exact_mod_cast n.property
  have hpi : Real.pi/4 ≤ 1 := by linarith [Real.pi_lt_four]
  have hd1 : ‖z-(Real.pi:ℂ)*(n:ℕ)‖ ≤ 1 := hdisk.trans hpi
  have him : |z.im| ≤ 1 := by
    have h := (Complex.abs_im_le_norm (z-(Real.pi:ℂ)*(n:ℕ))).trans hd1
    simpa only [sub_im,mul_im,ofReal_im,natCast_im,mul_zero,zero_mul,add_zero,sub_zero] using h
  have hzn : (n:ℝ) ≤ ‖z‖ := by
    have ht := norm_add_le (((Real.pi:ℂ)*(n:ℕ))-z) z
    have hc : ‖(Real.pi:ℂ)*(n:ℕ)‖ = Real.pi*(n:ℝ) := by simp [Real.pi_pos.le]
    rw [sub_add_cancel,hc,norm_sub_rev] at ht
    nlinarith [Real.pi_gt_three]
  have hz : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by linarith : (0:ℝ)<n) hzn)
  have herror := norm_miuraL2SolutionCurve_sub_free_fractional s hs hs1 u R 1 hR
    (n:ℕ) n.property z hzn him (1,I)
  have hv : ‖((1,I):ℂ × ℂ)‖ = 1 := by simp
  rw [hv,mul_one] at herror
  have hsine0 : hillMiuraDirichletSineCurve (sobolevToL2 hs u) z
      ⟨1,by constructor <;> norm_num⟩ = 0 := by
    rw [hillMiuraDirichletSineCurve_eq_quasiHill]
    change z*MKdV.quasiHillL2Dirichlet (sobolevToL2 hs u) (z^2) = 0
    rw [(auxiliaryDirichlet_eq_zero_iff_quasiHillL2Dirichlet _ z hz).mp hroot,mul_zero]
  have hsine : ‖sin z‖ ≤ miuraFractionalFreeConstant R 1*(n:ℝ)^(-s)*‖u‖ := by
    have hcol := (l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal (sobolevToL2 hs u))) z (1,I)-
      l2SolutionCurve 0 z (1,I)).norm_coe_le_norm ⟨1,by constructor <;> norm_num⟩
    have hp := norm_miuraDirichletSinePosition_le
      ((l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal (sobolevToL2 hs u))) z (1,I)-
        l2SolutionCurve 0 z (1,I)) ⟨1,by constructor <;> norm_num⟩)
    change ‖miuraDirichletSinePosition
      (l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal (sobolevToL2 hs u))) z (1,I)
        ⟨1,by constructor <;> norm_num⟩-
       l2SolutionCurve 0 z (1,I) ⟨1,by constructor <;> norm_num⟩)‖ ≤ _ at hp
    rw [map_sub,l2SolutionCurve_free,miuraDirichletSinePosition_free] at hp
    change ‖hillMiuraDirichletSineCurve (sobolevToL2 hs u) z
      ⟨1,by constructor <;> norm_num⟩-sin (z*1)‖ ≤ _ at hp
    rw [hsine0,mul_one,zero_sub,norm_neg] at hp
    exact hp.trans (hcol.trans herror)
  have hrootdisp : ‖z-(Real.pi:ℂ)*(n:ℕ)‖ ≤
      B*(miuraFractionalFreeConstant R 1*(n:ℝ)^(-s)*‖u‖) := by
    have hh := hdisp ((n:ℕ):ℤ) z (by simpa only [Int.cast_natCast] using hdisk)
    simp only [Int.cast_natCast] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hsine hB)
  exact (norm_miuraDirichletSineCurve_sub_free_le _ z n hd1).trans
    ((add_le_add herror (mul_le_mul_of_nonneg_left hrootdisp (by norm_num))).trans_eq (by ring))

end NLS.KdV
