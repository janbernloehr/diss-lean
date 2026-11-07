import NLS.KdV.HillMiuraEnergyGapCoordinates
import NLS.KdV.HillHminusOneMiuraOutsideShift
import NLS.ZakharovShabat.SourceGapSampleSummability
import NLS.SequenceSpaces.SquaredLatticeDisplacement
import NLS.SequenceSpaces.PositiveBracketComparison

/-! EVERY choice of energies in the FULL ORIGINAL positive real Hill
gaps has the literal h-minus-one displacement from m^2*pi^2. No high
cutoff or missing low-gap exception is used. -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillMiura_real_gap_samples_inverseIndex_error
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (σ : ℕ+ → ℝ)
    (hσ : ∀ m : ℕ+, σ m ∈ Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ)))) :
    Memℓp (fun m : ℕ+ => ((σ m:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)) 2 := by
  let ρ : ℤ → ℂ := fun k => if hk : 0 < k then
      energyFrequency (c:ℂ) (σ ⟨k.toNat,by omega⟩:ℂ)
    else sourceStandardRootMidpoint (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) k
  have hρ (k : ℤ) : ρ k ∈ sourcePeriodicSegment (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) k := by
    by_cases hk : 0 < k
    · let m : ℕ+ := ⟨k.toNat,by omega⟩
      have hindex : ((m:ℕ):ℤ) = k := by
        change ((k.toNat:ℕ):ℤ) = k
        exact Int.toNat_of_nonneg hk.le
      have h := (hillMiura_frequency_of_original_gap q hq u c hi hc m (σ m) (hσ m)).2.1
      rw [hindex] at h
      simpa only [ρ,dif_pos hk,m] using h
    · simpa only [ρ,dif_neg hk] using sourcePeriodicMidpoint_mem_segment
        (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) k
  let d : Coeff 2 := ⟨fun k => ρ k-(Real.pi:ℂ)*k,
    memℓp_sourcePeriodicSegment_samples (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) ρ hρ⟩
  have hp := memlp_inverseBracket_squared_lattice_error (Real.pi:ℂ) (c:ℂ) d
  have hInjective : Function.Injective (fun m : ℕ+ => ((m:ℕ):ℤ)) := by
    intro i j he
    exact Subtype.ext (Int.ofNat.inj he)
  have hpos : Memℓp (fun m : ℕ+ => inverseBracketCoefficients (m:ℕ)*
      (((Real.pi:ℂ)*(m:ℕ)+d (m:ℕ))^2-(c:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)) 2 := by
    apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
    exact (hp.summable (by norm_num)).comp_injective hInjective
  have he (m : ℕ+) : ((Real.pi:ℂ)*(m:ℕ)+d (m:ℕ))^2-(c:ℂ) = (σ m:ℂ) := by
    have hm : 0 < ((m:ℕ):ℤ) := by exact_mod_cast m.pos
    have hm' : (⟨(((m:ℕ):ℤ)).toNat,by omega⟩:ℕ+) = m := by apply Subtype.ext; rfl
    have hρm : ρ (m:ℕ) = energyFrequency (c:ℂ) (σ m:ℂ) := by
      dsimp only [ρ]
      rw [dif_pos hm,hm']
    change ((Real.pi:ℂ)*(m:ℕ)+(ρ (m:ℕ)-(Real.pi:ℂ)*(m:ℕ)))^2-(c:ℂ) = _
    rw [add_sub_cancel,hρm,energyFrequency_sq]
    ring
  have hbracket : Memℓp (fun m : ℕ+ => inverseBracketCoefficients (m:ℕ)*
      ((σ m:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)) 2 := by
    simpa only [he] using hpos
  exact memlp_div_pnat_of_memlp_inverseBracket _ hbracket

theorem hillHminusOriginal_real_gap_samples_inverseIndex_error
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (σ : ℕ+ → ℝ)
    (hσ : ∀ m : ℕ+, σ m ∈ Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ)))) :
    Memℓp (fun m : ℕ+ => ((σ m:ℂ)-((Real.pi:ℂ)*(m:ℕ))^2)/(m:ℕ)) 2 := by
  obtain ⟨d,_,_,u,hi,hc⟩ := exists_real_periodOneMiura_shift_outside_spectrum q hq 0
  have hi' : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 ((d^2:ℝ):ℂ)) := by
    simpa only [Complex.ofReal_pow] using hi
  have hc' : -((d^2:ℝ):ℂ) ∉ singularHillSpectrum (periodOneOriginal q) := by
    simpa only [Complex.ofReal_pow] using hc
  exact hillMiura_real_gap_samples_inverseIndex_error q hq u (d^2) hi' hc' σ hσ

end NLS.KdV
