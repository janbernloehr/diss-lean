import NLS.KdV.HillAuxiliaryEnergyWeightBound
import NLS.KdV.HillCanonicalCartesianWeight
import NLS.KdV.HillOnIndexUniformCartesianBound

/-! The ACTUAL diagonal Cartesian estimate in ORIGINAL Hill energy
weights, on ONE native complex neighborhood BEFORE ALL n. Every low
and complex collapsed gap, actual auxiliary divisor and sheet is retained. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_local_uniform_physicalDirichlet_original_energy_weight_bound (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.physicalDirichletSource ∧
      ∃ D : ℝ, 0 < D ∧ ∀ y ∈ U, ∀ n : ℕ+,
        ‖sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) ((n:ℕ):ℤ)‖*
          (‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi y) ((n:ℕ):ℤ)‖+
            ‖P.physicalDirichletFrequency ((n:ℕ):ℤ) y-
              sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) ((n:ℕ):ℤ)‖) ≤
          D*hillHminusCanonicalCartesianWeight n y := by
  obtain ⟨U,hU,hqU,hUP,D,hD,hweight⟩ := P.exists_local_uniform_physicalDirichlet_quadratic_energy_weight_bound q hq hr
  obtain ⟨r,hrpos,_,hperiod⟩ := P.exists_common_canonical_zero_sequence_period_ball q hq hr
  refine ⟨U ∩ ball q r,hU.inter isOpen_ball,⟨hqU,mem_ball_self hrpos⟩,(fun _ h => hUP h.1),D,hD,?_⟩
  intro y hy n
  let B := P.parent.parent.miuraBall
  have hyP := (hUP hy.1).1
  have hyB : y ∈ B.source := (P.parent.subset (P.subset hyP)).1
  let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) ((n:ℕ):ℤ)
  let γ := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi y) ((n:ℕ):ℤ)
  let μ := P.physicalDirichletFrequency ((n:ℕ):ℤ) y
  have hg : hillHminusCanonicalGapSquare n y = (2*τ*γ)^2 := by
    rw [B.canonical_gapSquare_eq n y hyB]
    dsimp only [B,HillHminusMiuraGapBall.gapSquare,HillHminusMiuraGapBall.diracSum,τ,γ,sourcePsi]
    rw [sourcePeriodicGapDisplacement_apply]
    ring
  have hgn : Real.sqrt ‖hillHminusCanonicalGapSquare n y‖ = ‖2*τ*γ‖ := by
    rw [hg,norm_pow,Real.sqrt_sq (norm_nonneg _)]
  have hper := hperiod y hy.2 n
  have hmid : hillHminusCanonicalEnergyMidpoint n y = B.energyMidpoint n y :=
    P.canonical_energyMidpoint_eq_local n y hper.1 hper.2
  have he : μ^2-τ^2-γ^2/4 = hillHminusCanonicalDirichlet n y-hillHminusCanonicalEnergyMidpoint n y := by
    rw [hmid,← P.physicalDirichletFrequency_energy n y hyP]
    dsimp only [B,HillHminusMiuraGapBall.energyMidpoint,τ,γ,μ,sourcePsi]
    rw [sourcePeriodicGapDisplacement_apply]
    ring
  have hw := hweight y hy.1 n
  change ‖τ‖*(‖γ‖+‖μ-τ‖) ≤ D*(‖2*τ*γ‖+‖μ^2-τ^2-γ^2/4‖) at hw
  simpa only [hillHminusCanonicalCartesianWeight,hgn,he] using hw

theorem exists_local_uniform_physicalOnIndexCartesian_original_energy_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.physicalDirichletSource ∧
      ∃ C : ℝ, 0 < C ∧ ∀ y ∈ U, ∀ n : ℕ+,
        ‖P.physicalOnIndexCartesianPlus n y‖ ≤ C*hillHminusCanonicalCartesianWeight n y ∧
          ‖P.physicalOnIndexCartesianMinus n y‖ ≤ C*hillHminusCanonicalCartesianWeight n y := by
  obtain ⟨Uf,hUf,hqf,hUfP,Cf,hCf,hfreq⟩ := P.exists_local_uniform_physicalOnIndexCartesian_frequency_bound H q
    (P.real_mem_physicalDirichletSource q hq hr)
  obtain ⟨Uw,hUw,hqw,_,D,hD,hweight⟩ := P.exists_local_uniform_physicalDirichlet_original_energy_weight_bound q hq hr
  refine ⟨Uf ∩ Uw,hUf.inter hUw,⟨hqf,hqw⟩,(fun _ h => hUfP h.1),Cf*D,mul_pos hCf hD,?_⟩
  intro y hy n
  have hf := hfreq y hy.1 n
  have hw := mul_le_mul_of_nonneg_left (hweight y hy.2 n) hCf.le
  constructor
  · exact hf.1.trans (by simpa only [mul_assoc] using hw)
  · exact hf.2.trans (by simpa only [mul_assoc] using hw)

end NLS.KdV.HillProductEquationPatch
