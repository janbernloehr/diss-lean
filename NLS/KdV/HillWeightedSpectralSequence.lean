import NLS.KdV.HillSpectralCartesian
import NLS.KdV.HillWeightedActionContinuity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillWeightedSpectralCoordinate (w : SpectralWeight) (p : RealHillWeightedPotential w) (k : ℕ) : ℂ :=
  (w (2*((k+1:ℕ):ℤ)):ℂ)*(Real.sqrt (2*Real.pi*(k+1:ℕ)):ℂ)*
    hillSpectralCartesian (hillRealWeightedEmbedding w p).val
      (hillRealWeightedEmbedding w p).property.1 (hillRealWeightedEmbedding w p).property.2 (k+1) (by omega)

include h0q h0r

theorem norm_hillWeightedSpectralCoordinate_sq
    (w : SpectralWeight) (p : RealHillWeightedPotential w) (k : ℕ) :
    ‖hillWeightedSpectralCoordinate w p k‖^2=2*hillWeightedActionTerm w p (k+1) := by
  have hI := hillPeriodOneAction_nonneg w p.val p.property (k+1) (by omega)
  have hz := norm_hillSpectralCartesian h0q h0r (hillRealWeightedEmbedding w p).val
    (hillRealWeightedEmbedding w p).property.1 (hillRealWeightedEmbedding w p).property.2 (k+1) (by omega)
  have hzsq : ‖hillSpectralCartesian (hillRealWeightedEmbedding w p).val
      (hillRealWeightedEmbedding w p).property.1 (hillRealWeightedEmbedding w p).property.2 (k+1) (by omega)‖^2 =
      2*hillPeriodOneAction w p.val p.property (k+1) := by
    rw [hz,Real.sq_sqrt (by exact mul_nonneg (by norm_num) hI)]
    rfl
  rw [hillWeightedSpectralCoordinate,norm_mul,norm_mul,mul_pow,mul_pow,hzsq,
    norm_real,Real.norm_eq_abs,sq_abs,norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (by positivity)]
  dsimp only [hillWeightedActionTerm]
  ring

theorem summable_norm_hillWeightedSpectralCoordinate_sq
    (w : SpectralWeight) (p : RealHillWeightedPotential w) :
    Summable (fun k : ℕ => ‖hillWeightedSpectralCoordinate w p k‖^2) := by
  simp_rw [norm_hillWeightedSpectralCoordinate_sq h0q h0r]
  exact ((summable_hillWeightedActionTerm w p).comp_injective Nat.succ_injective).mul_left 2

theorem memℓp_hillWeightedSpectralCoordinate
    (w : SpectralWeight) (p : RealHillWeightedPotential w) :
    Memℓp (hillWeightedSpectralCoordinate w p) 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)]
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    summable_norm_hillWeightedSpectralCoordinate_sq h0q h0r w p

def hillWeightedSpectralSequence (w : SpectralWeight) (p : RealHillWeightedPotential w) :
    lp (fun _ : ℕ => ℂ) 2 :=
  ⟨hillWeightedSpectralCoordinate w p,memℓp_hillWeightedSpectralCoordinate h0q h0r w p⟩

theorem hillWeightedSpectralSequence_apply
    (w : SpectralWeight) (p : RealHillWeightedPotential w) (k : ℕ) :
    hillWeightedSpectralSequence h0q h0r w p k=hillWeightedSpectralCoordinate w p k := rfl

theorem norm_hillWeightedSpectralSequence_sq
    (w : SpectralWeight) (p : RealHillWeightedPotential w) :
    ‖hillWeightedSpectralSequence h0q h0r w p‖^2=2*∑' n : ℕ, hillWeightedActionTerm w p n := by
  have hnorm := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal)
    (hillWeightedSpectralSequence h0q h0r w p)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,hillWeightedSpectralSequence_apply,
    norm_hillWeightedSpectralCoordinate_sq h0q h0r] at hnorm
  rw [hnorm,tsum_mul_left]
  have hsplit := (summable_hillWeightedActionTerm w p).sum_add_tsum_nat_add 1
  have hzero : hillWeightedActionTerm w p 0=0 := by simp [hillWeightedActionTerm]
  simpa only [Finset.sum_range_one,hzero,zero_add] using congrArg (fun t : ℝ => 2*t) hsplit

end NLS.KdV
