import NLS.ZakharovShabat.SourceFullAbelianFiniteGapExterior
import NLS.SequenceSpaces.ShiftedHolderDecay

/-! # Periodic endpoint normalization along the positive spectral tail -/
noncomputable section
open Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem tendsto_sourcePeriodicLeft_sub_free_atTop (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    Tendsto (fun n : ℤ => canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
      (Real.pi : ℂ)*n) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact (Coeff.tendsto_norm_apply_cofinite hp
    (canonicalPeriodicLeftDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ))).mono_left atTop_le_cofinite

theorem tendsto_sourcePeriodicLeft_norm_atTop (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    Tendsto (fun n : ℤ => ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖) atTop atTop := by
  let a := canonicalPeriodicLeftDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  have ht : Tendsto (fun n : ℤ => Real.pi*(n:ℝ)-‖a‖) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-‖a‖)
      (tendsto_intCast_atTop_atTop.const_mul_atTop Real.pi_pos)
  apply tendsto_atTop_mono _ ht
  intro n
  have hnorm := lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' a n
  have htri := norm_sub_le
    (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) (a n)
  have he : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-a n = (Real.pi : ℂ)*n := by
    dsimp [a,canonicalPeriodicLeftDisplacement]
    ring
  rw [he] at htri
  have hre := Complex.re_le_norm ((Real.pi : ℂ)*n)
  simp only [mul_re,ofReal_re,intCast_re,ofReal_im,intCast_im,mul_zero,sub_zero] at hre
  linarith

end NLS.ZakharovShabat
