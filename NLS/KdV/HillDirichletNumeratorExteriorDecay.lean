import NLS.KdV.HillDirichletCharacteristicExterior
import NLS.KdV.HillGlobalNormalizedDifferentials
import NLS.ZakharovShabat.AppendixEInterpolationDecay

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem exists_hillGapFullEnergyProduct_div_free_bound
    (roots : ℕ → ℝ) (hroots : roots∈hillGapRootBox q hq hr) :
    ∃ K : ℕ, ∀ k : ℕ, K≤k → ∀ E∈sphere (0 : ℂ) ((centralCircleRadius k)^2),
      ‖hillAbelianNumeratorProduct roots 0 E/(sin (Complex.sqrt E)/Complex.sqrt E)‖≤2 := by
  obtain ⟨K,hK⟩ := eventually_centralCircle_entireSingleSpectralProduct_div_free_close
    (by simp : (2 : ℝ≥0∞)≠⊤) (hillGapSignedRootFrequency roots)
    (memℓp_hillGapSignedRootFrequency_displacement q hq hr roots hroots) (by norm_num : (0 : ℝ)<1)
  refine ⟨K,?_⟩
  intro k hk E hE
  have hnorm : ‖E‖=(centralCircleRadius k)^2 := by simpa only [mem_sphere,dist_zero_right] using hE
  have hz : Complex.sqrt E∈sphere (0 : ℂ) (centralCircleRadius k) := by
    have hh := congrArg norm (complex_sqrt_sq E)
    rw [norm_pow,hnorm] at hh
    rw [mem_sphere,dist_zero_right]
    nlinarith [norm_nonneg (Complex.sqrt E),centralCircleRadius_pos k]
  have hsin : sin (Complex.sqrt E)≠0 := sin_ne_zero_on_centralCircle k _ hz
  have hz0 : Complex.sqrt E≠0 := by
    intro hh
    have ht : ‖Complex.sqrt E‖=centralCircleRadius k := by simpa only [mem_sphere,dist_zero_right] using hz
    rw [hh,norm_zero] at ht
    linarith [centralCircleRadius_pos k]
  have hb := hK k hk (Complex.sqrt E) hz
  rw [entireSingleSpectralProduct_hillGapFullEnergyProduct q hq hr roots hroots,complex_sqrt_sq] at hb
  have he : (-2*Complex.sqrt E*hillAbelianNumeratorProduct roots 0 E)/(-2*sin (Complex.sqrt E))=
      hillAbelianNumeratorProduct roots 0 E/(sin (Complex.sqrt E)/Complex.sqrt E) := by
    field_simp
  rw [he] at hb
  have hh := norm_le_norm_sub_add (hillAbelianNumeratorProduct roots 0 E/(sin (Complex.sqrt E)/Complex.sqrt E)) 1
  rw [norm_one] at hh
  linarith

/-- The actual numerator/Dirichlet quotient tends uniformly to zero
on expanding energy circles; its denominator is the original characteristic. -/
theorem eventually_hillAbelianPsiCandidate_div_dirichlet_small
    (roots : ℕ → ℝ) (hroots : roots∈hillGapRootBox q hq hr) (n : ℕ) (hn : 1≤n)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ E∈sphere (0 : ℂ) ((centralCircleRadius k)^2),
      ‖hillAbelianPsiCandidate roots n E/hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E‖≤ε := by
  obtain ⟨Kp,hKp⟩ := exists_hillGapFullEnergyProduct_div_free_bound q hq hr roots hroots
  obtain ⟨Kd,hKd⟩ := exists_hillDirichletCharacteristic_energy_central_bounds ‖SpectralWeight.one.toCoeff q‖
  obtain ⟨Kz,hKz⟩ := exists_hillGapFullEnergyProduct_ratio_bound q hq hr roots roots hroots hroots
  let C : ℝ := ‖2/((n : ℂ)*Real.pi)*(freeHillValue n : ℂ)‖
  have hC : 0≤C := norm_nonneg _
  filter_upwards [eventually_ge_atTop Kp,eventually_ge_atTop Kd,eventually_ge_atTop Kz,
    tendsto_hillEnergyCircleRadius.eventually_ge_atTop (‖(roots (n-1) : ℂ)‖+4*C/ε+1)] with k hkp hkd hkz hbig
  intro E hE
  have hnorm : ‖E‖=(centralCircleRadius k)^2 := by simpa only [mem_sphere,dist_zero_right] using hE
  have hdist : 4*C/ε+1≤‖(roots (n-1) : ℂ)-E‖ := by
    have hh := norm_sub_norm_le E (roots (n-1) : ℂ)
    rw [norm_sub_rev E] at hh
    linarith
  have hdpos : 0<‖(roots (n-1) : ℂ)-E‖ := by
    have hh : 0≤4*C/ε := by positivity
    linarith
  have hne : (roots (n-1) : ℂ)≠E := sub_ne_zero.mp (norm_pos_iff.mp hdpos)
  have hfull := (hKz k hkz E hE).1
  have hD := (hKd k hkd (SpectralWeight.one.toCoeff q) le_rfl E hE).1
  have hfree : sin (Complex.sqrt E)/Complex.sqrt E≠0 := by
    have hz : Complex.sqrt E∈sphere (0 : ℂ) (centralCircleRadius k) := by
      have he := congrArg norm (complex_sqrt_sq E)
      rw [norm_pow,hnorm] at he
      rw [mem_sphere,dist_zero_right]
      nlinarith [norm_nonneg (Complex.sqrt E),centralCircleRadius_pos k]
    have hsin := sin_ne_zero_on_centralCircle k _ hz
    exact div_ne_zero hsin (by
      intro he
      apply hsin
      rw [he,sin_zero])
  have he : hillAbelianPsiCandidate roots n E/hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E=
      (2/((n : ℂ)*Real.pi)*(freeHillValue n : ℂ))/((roots (n-1) : ℂ)-E)*
        (hillAbelianNumeratorProduct roots 0 E/(sin (Complex.sqrt E)/Complex.sqrt E))*
        ((sin (Complex.sqrt E)/Complex.sqrt E)/hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E) := by
    have hp := hillAbelianPsiCandidate_div_full_product q hq hr roots roots hroots n hn E hne
    rw [div_self hfull,mul_one] at hp
    calc
      _ = (hillAbelianPsiCandidate roots n E/hillAbelianNumeratorProduct roots 0 E)*
          (hillAbelianNumeratorProduct roots 0 E/(sin (Complex.sqrt E)/Complex.sqrt E))*
          ((sin (Complex.sqrt E)/Complex.sqrt E)/hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E) := by
        have hs : sin (Complex.sqrt E)≠0 := fun hh => hfree (by rw [hh,zero_div])
        have hz : Complex.sqrt E≠0 := fun hh => hfree (by rw [hh,div_zero])
        field_simp [hfull,hfree,hD,hs,hz]
      _ = _ := by rw [hp]
  rw [he,norm_mul,norm_mul,norm_div]
  have hp := hKp k hkp E hE
  have hd := (hKd k hkd (SpectralWeight.one.toCoeff q) le_rfl E hE).2
  apply (mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hd (norm_nonneg _)
    (by positivity : 0≤C/‖(roots (n-1) : ℂ)-E‖*2)).trans
  change C/‖(roots (n-1) : ℂ)-E‖*2*2≤ε
  rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
  apply (div_le_iff₀ hdpos).mpr
  have hh := (div_le_iff₀ hε).mp (show 4*C/ε≤‖(roots (n-1) : ℂ)-E‖ by linarith)
  nlinarith

theorem eventually_hillAbelianSelectedGlobalPsi_div_dirichlet_small
    (n : ℕ) (hn : 1≤n) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ E∈sphere (0 : ℂ) ((centralCircleRadius k)^2),
      ‖hillAbelianSelectedGlobalPsi q hq hr n hn E/
        hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E‖≤ε := by
  let roots := (hillAbelianSelectedGlobalRoots q hq hr n hn).val
  let d := hillAbelianCandidatePeriod q hq hr roots n n
  by_cases hd : d=0
  · exact Eventually.of_forall (fun k E hE => by
      change ‖(hillAbelianPsiCandidate roots n E/d)/_‖≤ε
      rw [hd,div_zero,zero_div,norm_zero]
      exact hε.le)
  · have hdn : 0<‖d‖ := norm_pos_iff.mpr hd
    filter_upwards [eventually_hillAbelianPsiCandidate_div_dirichlet_small q hq hr roots
      (hillAbelianSelectedGlobalRoots q hq hr n hn).property n hn (ε*‖d‖) (mul_pos hε hdn)] with k hk
    intro E hE
    change ‖(hillAbelianPsiCandidate roots n E/d)/_‖≤ε
    rw [div_right_comm,norm_div]
    exact (div_le_iff₀ hdn).mpr (hk E hE)

end NLS.KdV
