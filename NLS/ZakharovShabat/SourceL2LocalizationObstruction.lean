import NLS.ZakharovShabat.SourcePlaneWaveSpectrum
import NLS.ZakharovShabat.SourcePhysicalL2Equiv
import NLS.ZakharovShabat.SourceRealTypeConvex

noncomputable section
set_option autoImplicit false
open Set Complex
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat

/-- The plane wave is the original finite Fourier source. -/
theorem sourcePlaneWave_eq_ofFinsupp (n : ℤ) (a b : ℂ) :
    sourcePlaneWave (p := 2) n a b =
      CoeffPair.ofFinsupp (Finsupp.single (-n) a,Finsupp.single n b) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext j <;>
    simp [sourcePlaneWave,CoeffPair.ofFinsupp,Coeff.ofFinsupp,lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]

/-- Its actual physical potential is the pair of opposite Fourier waves. -/
theorem sourcePlaneWave_physicalBase (n : ℤ) (a b : ℂ) :
    physicalBase (periodOnePotential (sourcePlaneWave (p := 2) n a b))
      =ᵐ[volume.restrict (Ioc 0 2)]
        (fun x : ℝ => (a*NLS.Fourier.wave (-2*n) x,b*NLS.Fourier.wave (2*n) x)) := by
  rw [sourcePlaneWave_eq_ofFinsupp]
  have h := physicalBase_periodOnePotential_finite (Finsupp.single (-n) a,Finsupp.single n b)
  filter_upwards [h] with x hx
  simpa [BoundaryCondition.periodOnePair,NLS.Fourier.polynomial,mul_neg,neg_mul] using hx

/-- Real plane waves satisfy the original reflected Fourier reality condition. -/
theorem sourcePlaneWave_real (n : ℤ) (a : ℝ) :
    sourcePlaneWave (p := 2) n a a ∈ realTypeSourceLocus 2 := by
  intro j
  change (sourcePlaneWave (p := 2) n a a).snd j =
    conj ((sourcePlaneWave (p := 2) n a a).fst (-j))
  simp only [sourcePlaneWave_fst,sourcePlaneWave_snd]
  simp only [show (-j = -n) ↔ j=n by omega]
  split_ifs <;> simp

/-- The exact component-sum source norm is independent of the carrier frequency. -/
theorem sourcePlaneWave_norm_sq (n : ℤ) (a b : ℂ) :
    ‖sourcePlaneWave (p := 2) n a b‖^2 = ‖a‖^2+‖b‖^2 := by
  have h := norm_withLp_prod_rpow (p := 2) (by simp) (sourcePlaneWave (p := 2) n a b)
  simpa [sourcePlaneWave,lp.norm_single (by norm_num : 0 < (2:ℝ≥0∞))] using h

/-- This is the actual physical unit-interval L2 norm, not an equivalent auxiliary norm. -/
theorem sourcePlaneWave_physical_norm_sq (n : ℤ) (a : ℝ) :
    ‖sourcePhysicalL2 (sourcePlaneWave (p := 2) n a a)‖^2 = 2*a^2 := by
  rw [norm_sourcePhysicalL2,sourcePlaneWave_norm_sq]
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]
  ring

/-- A fixed nonzero amplitude gives a displaced real spectral point at every carrier. -/
theorem sourcePlaneWave_shifted_point_mem (n : ℤ) (a : ℝ) (ha : a ≠ 0) :
    ((Real.pi*n+a:ℝ):ℂ) ∈ periodicSpectrum (by simp)
      (periodOnePotential (sourcePlaneWave (p := 2) n a a)) := by
  apply sourcePlaneWave_mem_spectrum_of_equation (by simp) n 0 a a _
    (Complex.ofReal_ne_zero.mpr ha)
  push_cast
  ring

/-- The displaced point stays away from every free lattice point. -/
theorem planeWave_point_lattice_distance (n k : ℤ) (a : ℝ)
    (ha : 0 < a) (hapi : a ≤ Real.pi/2) :
    a ≤ ‖((Real.pi*n+a:ℝ):ℂ)-(Real.pi:ℂ)*k‖ := by
  have he : ((Real.pi*n+a:ℝ):ℂ)-(Real.pi:ℂ)*k =
      ((Real.pi*n+a-Real.pi*k:ℝ):ℂ) := by push_cast; rfl
  rw [he,Complex.norm_real,Real.norm_eq_abs]
  by_cases hk : k ≤ n
  · have hk' : (k:ℝ) ≤ n := by exact_mod_cast hk
    have hm := mul_le_mul_of_nonneg_left hk' Real.pi_pos.le
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hk' : (n:ℝ)+1 ≤ k := by exact_mod_cast (show n+1 ≤ k by omega)
    have hm := mul_le_mul_of_nonneg_left hk' Real.pi_pos.le
    rw [abs_of_nonpos (by nlinarith [Real.pi_pos])]
    nlinarith

/-- At one fixed physical L2 norm, real sources have spectral points beyond any
proposed central cutoff that stay a fixed distance from the entire free lattice. -/
theorem exists_fixedNorm_source_spectral_escape (a : ℝ) (ha : 0 < a)
    (hapi : a ≤ Real.pi/2) (R : ℝ) :
    ∃ φ : CoeffPair 2, φ ∈ realTypeSourceLocus 2 ∧
      ‖sourcePhysicalL2 φ‖^2 = 2*a^2 ∧
      ∃ z : ℂ, z ∈ periodicSpectrum (by simp) (periodOnePotential φ) ∧
        R < z.re ∧ ∀ k : ℤ, a ≤ ‖z-(Real.pi:ℂ)*k‖ := by
  obtain ⟨n,hn⟩ := exists_nat_gt (R/Real.pi)
  have hn' : R < Real.pi*(n:ℝ) := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hn
    simpa only [mul_comm] using h
  refine ⟨sourcePlaneWave (n:ℤ) a a,sourcePlaneWave_real _ _,
    sourcePlaneWave_physical_norm_sq _ _,((Real.pi*n+a:ℝ):ℂ),?_,?_,?_⟩
  · simpa only [Int.cast_natCast] using sourcePlaneWave_shifted_point_mem (n:ℤ) a ha.ne'
  · simp only [Complex.ofReal_re]
    linarith
  · intro k
    simpa only [Int.cast_natCast] using planeWave_point_lattice_distance (n:ℤ) k a ha hapi

/-- Section 25's opening obstruction: a fixed physical L2 sphere has no uniform
tail localization in free-lattice discs of radius smaller than its amplitude. -/
theorem not_uniform_L2_sphere_spectral_localization (a ε : ℝ)
    (ha : 0 < a) (hapi : a ≤ Real.pi/2) (hε : ε < a) :
    ¬ ∃ R : ℝ, ∀ φ : CoeffPair 2, φ ∈ realTypeSourceLocus 2 →
      ‖sourcePhysicalL2 φ‖^2 = 2*a^2 →
      ∀ z ∈ periodicSpectrum (by simp) (periodOnePotential φ), R ≤ |z.re| →
        ∃ k : ℤ, ‖z-(Real.pi:ℂ)*k‖ ≤ ε := by
  rintro ⟨R,hR⟩
  obtain ⟨φ,hφ,hn,z,hz,hlarge,hd⟩ := exists_fixedNorm_source_spectral_escape a ha hapi R
  obtain ⟨k,hk⟩ := hR φ hφ hn z hz (hlarge.le.trans (le_abs_self _))
  exact (not_le_of_gt hε) ((hd k).trans hk)

/-- Every positive physical L2 ball fails uniform asymptotic localization,
already on the real locus and at one fixed positive lattice-distance scale. -/
theorem not_uniform_L2_ball_spectral_localization (R : ℝ) (hR : 0 < R) :
    ∃ ε : ℝ, 0 < ε ∧ ¬ ∃ K : ℝ, ∀ φ : CoeffPair 2,
      φ ∈ realTypeSourceLocus 2 → ‖sourcePhysicalL2 φ‖ ≤ R →
      ∀ z ∈ periodicSpectrum (by simp) (periodOnePotential φ), K ≤ |z.re| →
        ∃ k : ℤ, ‖z-(Real.pi:ℂ)*k‖ ≤ ε := by
  let a := min (R/2) (Real.pi/4)
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have haR : a ≤ R/2 := min_le_left _ _
  have hapi : a ≤ Real.pi/2 := (min_le_right _ _).trans (by linarith [Real.pi_pos])
  refine ⟨a/2,by positivity,?_⟩
  rintro ⟨K,hK⟩
  apply not_uniform_L2_sphere_spectral_localization a (a/2) ha hapi (by linarith)
  refine ⟨K,fun φ hφ hn => hK φ hφ ?_⟩
  have hsq : a^2 ≤ (R/2)^2 := (sq_le_sq₀ ha.le (by positivity)).mpr haR
  have hp := norm_nonneg (sourcePhysicalL2 φ)
  nlinarith

end NLS.ZakharovShabat
