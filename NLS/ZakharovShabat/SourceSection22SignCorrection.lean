import NLS.ZakharovShabat.SourceSection22Phases
import NLS.ZakharovShabat.SourceComplexActionHamiltonian
/-! # Actual original sources witnessing the phase-sign correction

For every nonzero integer index and every finite exponent above one,
the original local Birkhoff inverse supplies a real finite-gap source
with positive phase frequency and both complex amplitudes nonzero.
Thus both literal printed phases have the wrong Hamiltonian velocity.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- A genuine finite-gap source with positive frequency and two nonzero amplitudes,
constructed in the original image without assuming global surjectivity. -/
theorem exists_finiteGap_positive_phase (n : ℤ) (hn : n ≠ 0) :
    ∃ φ : realTypeSourceSubmodule p, φ ∈ sourceFiniteGapLocus hp hp1 ∧
      0 < A.phaseFrequency φ n ∧
      (sourceComplexBirkhoffMap hp hp1 s φ.val).1 n ≠ 0 ∧
      (sourceComplexBirkhoffMap hp hp1 s φ.val).2 n ≠ 0 := by
  let z : ℝ → RealCoeff p × RealCoeff p := fun ε => (lp.single p n ε,0)
  have hz0 : z 0 = 0 := by simp [z]
  have hz : Continuous z := by
    exact (lp.singleContinuousLinearMap ℝ (fun _ : ℤ => ℝ) p n).continuous.prodMk continuous_const
  have hmem : (0 : RealCoeff p × RealCoeff p) ∈ range (sourceRealBirkhoffMap hp hp1 s) :=
    ⟨0,D.complex.real_map_zero⟩
  have hinv : D.complex.realImageInverse 0 = 0 := by
    simpa only [D.complex.real_map_zero] using D.complex.realImageInverse_real_map 0
  let f : ℝ → realTypeSourceSubmodule p := fun ε => D.complex.realImageInverse (z ε)
  have hf0 : f 0 = 0 := by simp only [f,hz0,hinv]
  have hf : ContinuousAt f 0 :=
    ((D.complex.realImageInverse_analytic _ (hz0 ▸ hmem)).continuousAt).comp hz.continuousAt
  have hw : ContinuousAt (fun ε => A.phaseFrequency (f ε) n) 0 :=
    (A.continuous_phaseFrequency Q.roots D.roots_open D.roots_real_subset n).continuousAt.comp hf
  have hw0 : 0 < A.phaseFrequency (f 0) n := by
    rw [hf0,SourceAbelianMomentAtlas.phaseFrequency]
    simp only [Submodule.coe_zero,A.renormalizedFrequency_eq_zero_at_zero,Complex.zero_re,add_zero]
    exact sq_pos_of_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (by exact_mod_cast hn))
  have hev : ∀ᶠ ε : ℝ in 𝓝 0, z ε ∈ range (sourceRealBirkhoffMap hp hp1 s) ∧
      0 < A.phaseFrequency (f ε) n := by
    filter_upwards [hz.continuousAt (hz0 ▸ D.complex.real_image_open.mem_nhds hmem),
      hw (Ioi_mem_nhds hw0)] with ε he hw
    exact ⟨he,hw⟩
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hev
  have hε : 0 < δ/2 := by positivity
  have hεball : δ/2 ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hε]
    linarith
  obtain ⟨himage,hfreq⟩ := hball hεball
  let φ := f (δ/2)
  have hcoord : sourceRealBirkhoffMap hp hp1 s φ = z (δ/2) :=
    D.complex.real_map_realImageInverse _ himage
  have hfinite : φ ∈ sourceFiniteGapLocus hp hp1 := by
    apply (D.complex.finiteGap_iff_finite_pairSupport φ).mpr
    rw [hcoord]
    apply (Set.finite_singleton n).subset
    intro k hk
    by_contra hkn
    simp only [Set.mem_singleton_iff] at hkn
    simp [RealCoeff.pairSupport,z,lp.single_apply,Pi.single_apply,hkn] at hk
  have hcoords : (sourceComplexBirkhoffMap hp hp1 s φ.val).1 n =
      Birkhoff.complexCoordinateScale*(δ/2:ℝ) ∧
      (sourceComplexBirkhoffMap hp hp1 s φ.val).2 n = Birkhoff.complexCoordinateScale*(δ/2:ℝ) := by
    rw [← D.complex.encode_real_map,hcoord]
    constructor <;> simp [Birkhoff.encodeReal,z]
  have hne : Birkhoff.complexCoordinateScale*(δ/2:ℝ) ≠ 0 := by
    apply mul_ne_zero
    · exact inv_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne')
    · exact_mod_cast hε.ne'
  exact ⟨φ,hfinite,hfreq,hcoords.1 ▸ hne,hcoords.2 ▸ hne⟩
end NLS.ZakharovShabat.SourceSection20Data

namespace NLS.Birkhoff
open Complex
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The second printed phase has negative velocity, opposite to the source Hamiltonian. -/
theorem hasDerivAt_printedPhaseFlow_snd (freq : ℤ → ℝ) (z : Coeff p × Coeff p)
    (n : ℤ) (t : ℝ) :
    HasDerivAt (fun τ => (phaseFlow freq τ z).2 n)
      (-I*(freq n : ℂ)*(phaseFlow freq t z).2 n) t := by
  have h := (NLS.ComplexAnalysis.hasDerivAt_complex_exp_mul (-I*(freq n : ℂ)) t).mul_const (z.2 n)
  have he (τ : ℝ) : -I*(freq n : ℂ)*τ = (((-τ*freq n : ℝ) : ℂ)*I) := by push_cast; ring
  simp_rw [he] at h
  simpa only [phaseFlow_snd,mul_assoc,mul_left_comm,mul_comm] using! h

/-- Nonzero second amplitude and frequency refute the printed Hamiltonian phase. -/
theorem not_hasDerivAt_printedPhaseFlow_hamiltonian_snd (freq : ℤ → ℝ)
    (z : Coeff p × Coeff p) (n : ℤ) (hf : freq n ≠ 0) (hz : z.2 n ≠ 0) :
    ¬ HasDerivAt (fun τ => (phaseFlow freq τ z).2 n) (I*(freq n : ℂ)*z.2 n) 0 := by
  intro h
  have he := (hasDerivAt_printedPhaseFlow_snd freq z n 0).unique h
  simp only [phaseFlow_zero] at he
  have hn : I*(freq n : ℂ)*z.2 n ≠ 0 :=
    mul_ne_zero (mul_ne_zero I_ne_zero (by exact_mod_cast hf)) hz
  apply hn
  linear_combination (-1/2 : ℂ)*he
end NLS.Birkhoff

namespace NLS.ZakharovShabat.SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- Equation (4.14)'s two signs fail at actual original finite-gap sources,
for every nonzero signed index and every finite exponent above one. -/
theorem equation4_14_printed_sign_counterexample (n : ℤ) (hn : n ≠ 0) :
    ∃ φ : realTypeSourceSubmodule p, φ ∈ sourceFiniteGapLocus hp hp1 ∧
      0 < A.phaseFrequency φ n ∧
      (sourceComplexBirkhoffMap hp hp1 s φ.val).1 n ≠ 0 ∧
      (sourceComplexBirkhoffMap hp hp1 s φ.val).2 n ≠ 0 ∧
      (¬ HasDerivAt (fun τ => (A.renormalizedPhaseTrajectory s φ τ).1 n)
        (-Complex.I*(A.phaseFrequency φ n : ℂ)*(sourceComplexBirkhoffMap hp hp1 s φ.val).1 n) 0) ∧
      (¬ HasDerivAt (fun τ => (A.renormalizedPhaseTrajectory s φ τ).2 n)
        (Complex.I*(A.phaseFrequency φ n : ℂ)*(sourceComplexBirkhoffMap hp hp1 s φ.val).2 n) 0) := by
  obtain ⟨φ,hf,hω,hz,hw⟩ := Q.exists_finiteGap_positive_phase n hn
  exact ⟨φ,hf,hω,hz,hw,
    Birkhoff.not_hasDerivAt_printedPhaseFlow_hamiltonian _ _ n hω.ne' hz,
    Birkhoff.not_hasDerivAt_printedPhaseFlow_hamiltonian_snd _ _ n hω.ne' hw⟩
end NLS.ZakharovShabat.SourceSection20Data
