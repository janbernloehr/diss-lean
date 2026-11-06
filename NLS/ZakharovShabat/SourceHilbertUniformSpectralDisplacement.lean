import NLS.ZakharovShabat.SourceHilbertCentralEndpointBound
import NLS.ZakharovShabat.SourceSpectralModulation
import NLS.ZakharovShabat.SourceCentralSpectralPath

/-! # Global real Hilbert spectral displacement bounds

Norm-preserving Fourier modulation moves any indexed actual endpoint to
a continuous central spectral selection. Actual band separation retains
that pair, and bounded-coefficient compactness bounds the central pair on
an entire real L2 norm ball. No H1 bound or source-tail cutoff is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

private theorem norm_displacement_le_central_bound
    (R C : ℝ)
    (hC : ∀ ψ : realTypeSourceSubmodule 2, ‖ψ.val‖≤R →
      ‖canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential ψ.val) (periodOnePotential_mem _) 0‖+
      ‖canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential ψ.val) (periodOnePotential_mem _) 0‖≤C)
    (φ : realTypeSourceSubmodule 2) (hφ : ‖φ.val‖≤R) (n : ℤ)
    (f : realTypeSourceSubmodule 2 → ℂ) (hf : Continuous f) (hf0 : f 0=(Real.pi : ℂ)*n)
    (hspec : ∀ ψ, f ψ∈periodicSpectrum (by simp) (periodOnePotential ψ.val)) :
    ‖f φ-(Real.pi : ℂ)*n‖≤C := by
  let a : ℝ → CoeffPair 2 := fun t => (t • φ).val
  let ψ : ℝ → CoeffPair 2 := fun t => sourceSpectralModulation (-n) (a t)
  let z : ℝ → ℂ := fun t => f (t • φ)-(Real.pi : ℂ)*n
  have ha : Continuous a := continuous_subtype_val.comp (continuous_id.smul continuous_const)
  have hψ : Continuous ψ := (sourceSpectralModulation (-n)).continuous.comp ha
  have hψr (t : ℝ) : IsRealType (CoeffPair.toMax 2 (ψ t)) :=
    isRealType_sourceSpectralModulation (-n) _ (t • φ).property
  have hψ0 : ψ 0=0 := by simp only [ψ,a,zero_smul,Submodule.coe_zero,map_zero]
  have hz : Continuous z := (hf.comp (continuous_id.smul continuous_const)).sub continuous_const
  have hz0 : z 0=0 := by simp only [z,zero_smul,hf0,sub_self]
  have hzs (t : ℝ) : z t∈periodicSpectrum (by simp) (periodOnePotential (ψ t)) := by
    have h := mem_source_periodicSpectrum_spectralModulation (by simp : (2 : ℝ≥0∞)≠⊤)
      (-n) (a t) (f (t • φ)) (hspec (t • φ))
    simpa only [z,ψ,Int.cast_neg,mul_neg,sub_eq_add_neg] using h
  have hp := continuous_source_spectral_path_mem_central_pair (by simp : (2 : ℝ≥0∞)≠⊤)
    (by norm_num : 1<(2 : ℝ≥0∞)) ψ hψ hψr hψ0 z hz hz0 hzs 1
  let χ : realTypeSourceSubmodule 2 := ⟨ψ 1,hψr 1⟩
  have hχ : ‖χ.val‖≤R := by
    change ‖sourceSpectralModulation (-n) ((1 : ℝ) • φ).val‖≤R
    simpa only [one_smul,LinearIsometryEquiv.norm_map] using hφ
  have hb := hC χ hχ
  have hzt : z 1=f φ-(Real.pi : ℂ)*n := by simp only [z,one_smul]
  rw [hzt] at hp
  rcases hp with hp|hp
  · rw [hp]
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans hb
  · rw [hp]
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans hb

/-- EVERY actual signed canonical endpoint has a uniformly bounded
absolute displacement on EACH real L2 norm ball. The bound is independent
of the index, source tails and any stronger Sobolev source norm. -/
theorem exists_uniform_real_hilbert_periodic_displacement_bound (R : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ φ : realTypeSourceSubmodule 2, ‖φ.val‖≤R → ∀ n : ℤ,
      ‖canonicalPeriodicLeft (by simp) (by norm_num)
        (periodOnePotential φ.val) (periodOnePotential_mem _) n-(Real.pi : ℂ)*n‖≤C ∧
      ‖canonicalPeriodicRight (by simp) (by norm_num)
        (periodOnePotential φ.val) (periodOnePotential_mem _) n-(Real.pi : ℂ)*n‖≤C := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_real_hilbert_central_endpoint_bound R
  refine ⟨C,hC,?_⟩
  intro φ hφ n
  constructor
  · apply norm_displacement_le_central_bound R C hbound φ hφ n
      (fun ψ => canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential ψ.val) (periodOnePotential_mem _) n)
    · apply continuous_iff_continuousAt.mpr
      intro ψ
      exact (continuousAt_canonicalPeriodicLeft_periodOne_of_realType (by simp) (by norm_num)
        ψ.val ψ.property n).comp continuous_subtype_val.continuousAt
    · simpa only [Submodule.coe_zero,map_zero] using canonicalPeriodicLeft_zero
        (by simp : (2 : ℝ≥0∞)≠⊤) (by norm_num : 1<(2 : ℝ≥0∞)) n
    · intro ψ
      exact (canonicalPeriodicEndpoints_mem_spectrum (by simp) (by norm_num)
        (periodOnePotential ψ.val) (periodOnePotential_mem _) n).1
  · apply norm_displacement_le_central_bound R C hbound φ hφ n
      (fun ψ => canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential ψ.val) (periodOnePotential_mem _) n)
    · apply continuous_iff_continuousAt.mpr
      intro ψ
      exact (continuousAt_canonicalPeriodicRight_periodOne_of_realType (by simp) (by norm_num)
        ψ.val ψ.property n).comp continuous_subtype_val.continuousAt
    · simpa only [Submodule.coe_zero,map_zero] using canonicalPeriodicRight_zero
        (by simp : (2 : ℝ≥0∞)≠⊤) (by norm_num : 1<(2 : ℝ≥0∞)) n
    · intro ψ
      exact (canonicalPeriodicEndpoints_mem_spectrum (by simp) (by norm_num)
        (periodOnePotential ψ.val) (periodOnePotential_mem _) n).2

/-- Uniform LINEAR positive-frequency growth on every real L2 ball.
This is an actual norm-ball theorem, not local source-tail localization. -/
theorem exists_uniform_real_hilbert_positive_endpoint_lower_bound (R : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ φ : realTypeSourceSubmodule 2, ‖φ.val‖≤R →
      ∀ n : ℕ, N≤n → (Real.pi/2)*(n : ℝ)≤
        (canonicalPeriodicLeft (by simp) (by norm_num)
          (periodOnePotential φ.val) (periodOnePotential_mem _) n).re := by
  obtain ⟨C,_hC,hbound⟩ := exists_uniform_real_hilbert_periodic_displacement_bound R
  obtain ⟨N,hN⟩ := exists_nat_gt (2*C/Real.pi+1)
  refine ⟨N+1,by omega,?_⟩
  intro φ hφ n hn
  have h := (abs_re_le_norm _).trans (hbound φ hφ n).1
  simp only [sub_re,mul_re,ofReal_re,ofReal_im,Int.cast_natCast,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] at h
  have hnR : (N : ℝ)<n := by exact_mod_cast (show N<n by omega)
  have hCn : 2*C≤(n : ℝ)*Real.pi := (div_le_iff₀ Real.pi_pos).mp (by linarith : 2*C/Real.pi≤(n : ℝ))
  have hl := (abs_le.mp h).1
  nlinarith [Real.pi_pos]

end NLS.ZakharovShabat
