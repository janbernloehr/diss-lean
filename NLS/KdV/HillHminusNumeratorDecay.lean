import NLS.KdV.HillHminusPhysicalNumeratorIdentification
import NLS.ZakharovShabat.SourcePsiSeparatedGrowth
import NLS.ComplexAnalysis.CloseShiftedFrequency
import NLS.ZakharovShabat.ShiftedSineExteriorBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

/-- The ACTUAL common energy numerator has full-product decay on the
ORIGINAL origin-centered energy circles. A signed shifted frequency
keeps the square root close even across the imaginary-axis branch. -/
theorem HillHminusPsiChart.numerator_full_product_decay (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (n : ℕ+) (roots : ℕ → ℝ)
    (hroots : roots∈hillGapRootBox q.val q.property.1 q.property.2)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ E∈sphere (0:ℂ) ((centralCircleRadius k)^2),
      ‖P.numerator n (E,hillOriginalHminusSource q.val)/hillAbelianNumeratorProduct roots 0 E‖≤ε := by
  let u := P.miura.lift (hillOriginalHminusSource q.val)
  let a : Coeff 2 := P.family.roots ((n:ℕ):ℤ) (hillMiuraDiagonal u)
  obtain ⟨B,hB,hBbound⟩ := exists_bound_sine_quotient_near_separated
  let δ : ℝ := ε/(4*B)
  have hδ : 0<δ := div_pos hε (by positivity)
  obtain ⟨Rs,hRs⟩ := exists_threshold_sourceOddPsiCandidate_sub_sine
    (by norm_num) (by norm_num) ((n:ℕ):ℤ) a δ hδ
  obtain ⟨Rg,hRg⟩ := exists_threshold_free_div_entireSingleSpectralProduct_le_two
    (by norm_num : (2:ℝ≥0∞)≠⊤) (hillGapSignedRootFrequency roots)
    (memℓp_hillGapSignedRootFrequency_displacement q.val q.property.1 q.property.2 roots hroots)
  let T : ℝ := max 1 (max Rs Rg)
  obtain ⟨K,hK⟩ := exists_closeShiftedFrequency_central_bounds P.miura.energyShift T
  filter_upwards [eventually_ge_atTop K] with k hk
  intro E hE
  let z := Complex.sqrt E
  have hzsq : z^2=E := complex_sqrt_sq _
  have hz : z∈sphere (0:ℂ) (centralCircleRadius k) := by
    have hn : ‖E‖=(centralCircleRadius k)^2 := by simpa only [mem_sphere,dist_zero_right] using hE
    have hs := congrArg norm hzsq
    rw [norm_pow,hn] at hs
    rw [mem_sphere,dist_zero_right]
    nlinarith [norm_nonneg z,centralCircleRadius_pos k]
  let w := closeShiftedFrequency z P.miura.energyShift
  obtain ⟨hw,hclose,hzT,hwT,hzw,hsepw⟩ := hK k hk z hz
  change w^2=z^2+P.miura.energyShift at hw
  rw [hzsq] at hw
  have hwlarge : 1≤‖w‖ := (le_max_left 1 (max Rs Rg)).trans hwT
  have hw0 : w≠0 := norm_pos_iff.mp (by linarith)
  have hz0 : z≠0 := norm_pos_iff.mp (by
    have hh : ‖z‖=centralCircleRadius k := by simpa only [mem_sphere,dist_zero_right] using hz
    rw [hh]; exact centralCircleRadius_pos k)
  have hsepz (m : ℤ) : Real.pi/4≤‖z-(Real.pi:ℂ)*m‖ := by
    have hs := centralCircle_lattice_gap k hz m
    linarith [Real.pi_pos]
  have hA := hRs w ((le_max_left Rs Rg).trans ((le_max_right 1 (max Rs Rg)).trans hwT)) hsepw
  have hsinratio := hBbound z w hsepz (hclose.trans (min_le_left 1 (Real.pi/4)))
  have hzwbound : ‖z/w‖≤2 := by
    rw [norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr hw0)).mpr hzw
  obtain ⟨hG0,hfree⟩ := hRg z
    ((le_max_right Rs Rg).trans ((le_max_right 1 (max Rs Rg)).trans hzT)) hsepz
  let G := entireSingleSpectralProduct (hillGapSignedRootFrequency roots) z
  have hG : G=-2*z*hillAbelianNumeratorProduct roots 0 E := by
    dsimp only [G]
    rw [entireSingleSpectralProduct_hillGapFullEnergyProduct q.val q.property.1 q.property.2 roots hroots,hzsq]
  have hfull : hillAbelianNumeratorProduct roots 0 E≠0 := by
    intro hh
    apply hG0
    change G=0
    rw [hG,hh,mul_zero]
  have hsinz : sin z≠0 := sin_ne_zero_of_notMem_freeLattice
    (notMem_freeLattice_of_separated (by positivity : 0<Real.pi/4) hsepz)
  have hsinw : sin w≠0 := sin_ne_zero_of_notMem_freeLattice
    (notMem_freeLattice_of_separated (by positivity : 0<Real.pi/4) hsepw)
  have hnum : 2*w*P.numerator n (E,hillOriginalHminusSource q.val)=
      sourceOddPsiCandidate ((n:ℕ):ℤ) (w,a) := by
    change 2*w*P.family.numerator n (E+P.miura.energyShift,u)=_
    rw [←hw]
    exact P.family.numerator_frequency_identity n u w
  have he : P.numerator n (E,hillOriginalHminusSource q.val)/hillAbelianNumeratorProduct roots 0 E=
      -((sourceOddPsiCandidate ((n:ℕ):ℤ) (w,a)/(-2*sin w))*(sin w/sin z)*(z/w)*((-2*sin z)/G)) := by
    rw [←hnum,hG]
    field_simp
  rw [he,norm_neg,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ δ*B*2*2 := by gcongr
    _ = ε := by dsimp only [δ]; field_simp; ring

end NLS.KdV
