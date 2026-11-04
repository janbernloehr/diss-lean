import NLS.KdV.HillWeightedSpectralSequence
import NLS.KdV.HillForwardSobolevBound

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillHomogeneousSpectralCoordinate (M m : ℕ)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) (k : ℕ) : ℂ :=
  (Real.sqrt ((2*Real.pi*(k+1:ℕ))^(2*m+1)):ℂ)*
    hillSpectralCartesian (hillRealWeightedEmbedding (hillIntegerWeight M) p).val
      (hillRealWeightedEmbedding (hillIntegerWeight M) p).property.1
      (hillRealWeightedEmbedding (hillIntegerWeight M) p).property.2 (k+1) (by omega)

include h0q h0r

theorem norm_hillHomogeneousSpectralCoordinate_sq (M m : ℕ)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) (k : ℕ) :
    ‖hillHomogeneousSpectralCoordinate M m p k‖^2 =
      2*hillGapActionTerm (hillPeriodOneUnitPotential (hillIntegerWeight M) p.val)
        (hillPeriodOneUnitPotential_even (hillIntegerWeight M) p.val)
        (hillPeriodOneUnitPotential_real (hillIntegerWeight M) p.val p.property) m (k+1) := by
  have hz := hillSpectralCartesian_action_identity h0q h0r
    (hillRealWeightedEmbedding (hillIntegerWeight M) p).val
    (hillRealWeightedEmbedding (hillIntegerWeight M) p).property.1
    (hillRealWeightedEmbedding (hillIntegerWeight M) p).property.2 (k+1) (by omega)
  simp only [pow_two] at hz
  rw [hillHomogeneousSpectralCoordinate,norm_mul,mul_pow,norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (by positivity),
    Complex.sq_norm,Complex.normSq_apply,hz]
  dsimp only [hillGapActionTerm,hillRealWeightedEmbedding]
  ring

theorem memℓp_hillHomogeneousSpectralCoordinate (M m : ℕ) (hm : m≤M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) :
    Memℓp (hillHomogeneousSpectralCoordinate M m p) 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat,Real.rpow_two]
  simp_rw [norm_hillHomogeneousSpectralCoordinate_sq h0q h0r]
  exact (((summable_nat_add_iff 1).mpr (summable_hillNativeGapActions M m hm p)).mul_left 2)

def hillHomogeneousSpectralSequence (M m : ℕ) (hm : m≤M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) : lp (fun _ : ℕ => ℂ) 2 :=
  ⟨hillHomogeneousSpectralCoordinate M m p,memℓp_hillHomogeneousSpectralCoordinate h0q h0r M m hm p⟩

theorem hillHomogeneousSpectralSequence_apply (M m : ℕ) (hm : m≤M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) (k : ℕ) :
    hillHomogeneousSpectralSequence h0q h0r M m hm p k=hillHomogeneousSpectralCoordinate M m p k := rfl

theorem norm_hillHomogeneousSpectralSequence_sq (M m : ℕ) (hm : m≤M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) :
    ‖hillHomogeneousSpectralSequence h0q h0r M m hm p‖^2=2*hillNativeActionMass M m p := by
  have hnorm := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal)
    (hillHomogeneousSpectralSequence h0q h0r M m hm p)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,hillHomogeneousSpectralSequence_apply,
    norm_hillHomogeneousSpectralCoordinate_sq h0q h0r] at hnorm
  rw [hnorm,tsum_mul_left]
  exact congrArg (fun t : ℝ => 2*t) (hasSum_hillNativePositiveActions M m hm p).tsum_eq

end NLS.KdV
