import NLS.KdV.MiuraDirichletSineCurve
import NLS.KdV.HminusOneDirichletUniformControl
import NLS.KdV.SingularDirichletGeometricMultiplicity
import NLS.ZakharovShabat.CanonicalBoundarySmallDisks
import NLS.ZakharovShabat.L2UniformFreeComparison
import NLS.ZakharovShabat.ClassicalFreeFrequencyDifference

/-! Phase-fixed high native Dirichlet eigenfunctions approach the LITERAL
free sine uniformly on the closed unit interval and on a full original
complex H^-1 potential neighborhood, with one common original index cutoff. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.LinearVolterra
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.ZakharovShabat
local instance dirichletEigenfunctionComparisonH1NormedGroup : NormedAddCommGroup UnitDirichletH1 := unitDirichletSubspace.normedAddCommGroup
local instance dirichletEigenfunctionComparisonH1NormedSpace : NormedSpace ℂ UnitDirichletH1 := unitDirichletSubspace.normedSpace

/-- The literal free sine at the original positive Dirichlet index. -/
def dirichletFreeSineCurve (n : ℕ+) : C(Icc (0:ℝ) 1,ℂ) :=
  ⟨fun t => sin ((Real.pi:ℂ)*(n:ℕ)*t.val),by fun_prop⟩

/-- Every fixed local Miura chart supplies ACTUAL native high eigenfunctions
with phase fixed to the literal free sine. ONE original complex H^-1
neighborhood and cutoff give the arbitrarily small physical UNIFORM error
for ALL subsequent original indices and ALL nearby complex sources. -/
theorem HillHminusMiuraChart.exists_uniform_dirichletEigenfunction_sine_comparison
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    {epsilon : ℝ} (heps : 0 < epsilon) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < N ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ C.domain ∧
      ∀ a ∈ V, ∀ n : ℕ+, N < (n:ℕ) → ∃ g : UnitDirichletH1, g ≠ 0 ∧
        singularDirichletOperator (periodOneOriginal a) g =
          hillHminusDirichletComplexLabels a n • singularDirichletDomainInclusion g ∧
        ‖unitDirichletContinuousInclusion g-dirichletFreeSineCurve n‖ < epsilon := by
  let Taux := auxiliaryPeriodOneDirichletPotential (by simp : (2:ℝ≥0∞) ≠ ⊤) (by norm_num : 1 < (2:ℝ≥0∞))
  let Fa : PeriodOneHminusOne → dirichletSubspace (p := 2) :=
    fun a => Taux (hillMiuraDiagonal (C.lift a))
  let Fp : PeriodOneHminusOne → IntervalPairL2 :=
    fun a => sourcePhysicalL2 (hillMiuraDiagonal (C.lift a))
  have hFa : AnalyticOnNhd ℂ Fa C.domain := by
    intro a ha
    exact (Taux.analyticAt _).comp ((hillMiuraDiagonal.analyticAt _).comp (C.lift_analytic a ha))
  have hFp : AnalyticOnNhd ℂ Fp C.domain := by
    intro a ha
    exact (sourcePhysicalL2.analyticAt _).comp ((hillMiuraDiagonal.analyticAt _).comp (C.lift_analytic a ha))
  let delta := min (Real.pi/4) (min 1 (epsilon/8))
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hdpi : delta ≤ Real.pi/4 := min_le_left _ _
  have hd1 : delta ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hde : delta ≤ epsilon/8 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N₀,V₀,hN₀,hV₀,hq₀,_,hcontrol,_⟩ := C.exists_uniform_analytic_dirichletControl q hq
  obtain ⟨N₁,U₁,_,hU₁,_,hq₁,_,hsmall⟩ :=
    exists_uniform_small_canonicalBoundaryDisks (by simp) (by norm_num) (Fa q) hd hdpi
  obtain ⟨T,U₂,hT,hU₂,hq₂,hfree⟩ :=
    exists_uniform_l2SolutionCurve_sub_free_small (Fp q) 1 (half_pos heps)
  obtain ⟨M,hM⟩ := exists_nat_gt ((T+1)/Real.pi)
  let N := max N₀ (max N₁ M)
  let V := V₀ ∩ (C.domain ∩ (Fa ⁻¹' U₁ ∩ Fp ⁻¹' U₂))
  have hV : IsOpen V := by
    apply hV₀.inter
    have heq : C.domain ∩ (Fa ⁻¹' U₁ ∩ Fp ⁻¹' U₂) =
        (C.domain ∩ Fa ⁻¹' U₁) ∩ (C.domain ∩ Fp ⁻¹' U₂) := by
      ext a
      simp only [mem_inter_iff]
      tauto
    rw [heq]
    exact (hFa.continuousOn.isOpen_inter_preimage C.domain_open hU₁).inter
      (hFp.continuousOn.isOpen_inter_preimage C.domain_open hU₂)
  refine ⟨N,V,hN₀.trans_le (le_max_left _ _),hV,⟨hq₀,hq,hq₁,hq₂⟩,
    fun a ha => ha.2.1,?_⟩
  intro a ha n hn
  let z := hillMiuraDiracDirichlet (C.lift a) (n:ℕ)
  have hn₀ : N₀ < (n:ℕ) := (le_max_left _ _).trans_lt hn
  have hn₁ : N₁ < (n:ℕ) := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hn
  have hnM : M < (n:ℕ) := (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hn
  have hdisk := hsmall (Fa a) ha.2.2.1 .dirichlet ((n:ℕ):ℤ) (by simpa using hn₁)
  have hfreq : ‖z-(Real.pi:ℂ)*(n:ℕ)‖ < delta := by
    simpa only [Fa,Taux,z,hillMiuraDiracDirichlet,canonicalAuxiliaryPeriodOneRoots,
      Int.cast_natCast,mem_ball,dist_eq_norm] using hdisk
  have him : |z.im| ≤ 1 := by
    have hh := (Complex.abs_im_le_norm (z-(Real.pi:ℂ)*(n:ℕ))).trans hfreq.le
    simpa only [sub_im,mul_im,ofReal_im,natCast_im,mul_zero,zero_mul,add_zero,sub_zero] using hh.trans hd1
  have hznorm : T ≤ ‖z‖ := by
    have hMR : (M:ℝ) < (n:ℝ) := by exact_mod_cast hnM
    have hM' := (div_lt_iff₀ Real.pi_pos).mp hM
    have hcenter : ‖(Real.pi:ℂ)*(n:ℕ)‖ = Real.pi*(n:ℝ) := by simp [Real.pi_pos.le]
    have htri := norm_add_le (((Real.pi:ℂ)*(n:ℕ))-z) z
    rw [sub_add_cancel,hcenter,norm_sub_rev] at htri
    nlinarith [Real.pi_pos]
  have hz : z ≠ 0 := norm_pos_iff.mp (hT.trans_le hznorm)
  have hroot : auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
      (hillMiuraDiagonal (C.lift a)) z = 0 :=
    (auxiliaryPeriodOneCharacteristic_eq_zero_iff (by simp) (by norm_num) .dirichlet _ z).mpr
      ((canonicalAuxiliaryPeriodOneRoots_exhaustive (by simp) (by norm_num) .dirichlet _ z).mpr
        ⟨((n:ℕ):ℤ),rfl⟩)
  obtain ⟨g,hg0,hg,hpos⟩ := exists_native_Miura_eigen_with_sineCurve (C.lift a) z hz hroot
  have himage := C.image a ha.2.1
  have he : singularDirichletOperator (periodOneOriginal a) g =
      hillHminusDirichletComplexLabels a n • singularDirichletDomainInclusion g := by
    rw [hillHminusDirichletComplexLabels_eq_tail_of_control a (C.lift a) C.energyShift N₀
      (hcontrol a ha.1) n hn₀]
    apply (singularDirichlet_source_eigen_add_constant_iff a (hillMiuraDirichletEnergy (C.lift a) C.energyShift (n:ℕ))
      C.energyShift g).mp
    rw [← himage]
    simpa only [hillMiuraDirichletEnergy,sub_add_cancel] using hg
  refine ⟨g,hg0,he,?_⟩
  rw [hpos]
  have hfree' := hfree (Fp a) ha.2.2.2 z him hznorm (1,I) (by simp)
  have hunit : ‖((1,I) : ℂ × ℂ)‖ = 1 := by simp
  have hrealcenter : ((Real.pi*(n:ℝ):ℝ):ℂ) = (Real.pi:ℂ)*(n:ℕ) := by simp
  have herror : ‖hillMiuraDirichletSineCurve (C.lift a) z-dirichletFreeSineCurve n‖ ≤
      ‖l2SolutionCurve (Fp a) z (1,I)-l2SolutionCurve 0 z (1,I)‖+2*‖z-(Real.pi:ℂ)*(n:ℕ)‖ := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro t
    have hcolumn := (l2SolutionCurve (Fp a) z (1,I)-l2SolutionCurve 0 z (1,I)).norm_coe_le_norm t
    change ‖l2SolutionCurve (Fp a) z (1,I) t-l2SolutionCurve 0 z (1,I) t‖ ≤ _ at hcolumn
    rw [l2SolutionCurve_free] at hcolumn
    have hshift := norm_classicalFreeFrequencyDifference_le z (Real.pi*(n:ℝ)) (1,I)
      (by rw [hrealcenter]; exact hfreq.le.trans hd1) t
    dsimp only [classicalFreeFrequencyDifference] at hshift
    rw [hrealcenter,hunit,mul_one] at hshift
    have htri := norm_add_le
      (l2SolutionCurve (Fp a) z (1,I) t-classicalFreeVector z (1,I) t)
      (classicalFreeVector z (1,I) t-classicalFreeVector (Real.pi*(n:ℝ)) (1,I) t)
    rw [sub_add_sub_cancel] at htri
    have hscalar := norm_miuraDirichletSinePosition_le
      (l2SolutionCurve (Fp a) z (1,I) t-classicalFreeVector (Real.pi*(n:ℝ)) (1,I) t)
    rw [map_sub,miuraDirichletSinePosition_free] at hscalar
    change ‖hillMiuraDirichletSineCurve (C.lift a) z t-dirichletFreeSineCurve n t‖ ≤ _
    exact hscalar.trans (htri.trans (add_le_add hcolumn hshift))
  linarith

/-- Every original complex H^-1 source has nonzero native high Dirichlet
eigenfunctions approaching the literal free sine, UNIFORMLY on ONE original
norm neighborhood and common positive-index cutoff, without a supplied lift. -/
theorem exists_uniform_hillHminusDirichletEigenfunction_sine_comparison
    (q : PeriodOneHminusOne) {epsilon : ℝ} (heps : 0 < epsilon) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ n : ℕ+, N < (n:ℕ) → ∃ g : UnitDirichletH1, g ≠ 0 ∧
        singularDirichletOperator (periodOneOriginal a) g =
          hillHminusDirichletComplexLabels a n • singularDirichletDomainInclusion g ∧
        ‖unitDirichletContinuousInclusion g-dirichletFreeSineCurve n‖ < epsilon := by
  obtain ⟨N,V,hN,hV,hq,_,he⟩ :=
    (hillHminusMiuraChartAt q).exists_uniform_dirichletEigenfunction_sine_comparison q
      (mem_hillHminusMiuraChartAt q) heps
  exact ⟨N,V,hN,hV,hq,he⟩

end NLS.KdV
