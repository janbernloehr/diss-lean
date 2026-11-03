import NLS.KdV.HillHminusOneRealCriticalEnergyGeometry
import NLS.KdV.HillHminusOneMiuraEnergyPeriods
import NLS.ComplexAnalysis.SimpleZeroPrincipalCoefficient

/-! # Actual critical residues of the descended entire numerator

The exact shifted-square chain rule transfers the genuine principal
coefficients at all real rough critical energies. Positive and negative
canonical NLS critical residues combine with the factor 2 beta. A filled
analytic quotient removes the apparent central-frequency singularity.
No Hilbert-sequence membership or Mittag-Leffler representation is assumed.
-/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

/-- The actual energy critical principal coefficient. At real-type chart
inputs every denominator is nonzero by the proved simplicity theorem. -/
def hillHminusMiuraEnergyCriticalResidue (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℤ)
    (q : PeriodOneHminusOne) (j : ℕ+) : ℂ :=
  hillHminusMiuraEnergyPsi C s n (C.energyCritical q j,q) /
    deriv (deriv (hillHminusDiscriminant q)) (C.energyCritical q j)

/-- The original signed canonical NLS critical principal coefficient. -/
def hillHminusMiuraSignedCriticalResidue (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℤ)
    (q : PeriodOneHminusOne) (j : ℤ) : ℂ :=
  let z := canonicalCriticalPoints (by simp) (by norm_num)
    (periodOnePotential (C.criticalSource q)) (periodOnePotential_mem _) j
  hillHminusMiuraSourcePsi C s n (z,q) /
    deriv (deriv (canonicalDiscriminant (by simp) (periodOnePotential (C.criticalSource q)))) z

theorem analyticOnNhd_hillHminusMiuraSourcePsi_spectral (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℤ) (q : PeriodOneHminusOne) :
    AnalyticOnNhd ℂ (fun z => hillHminusMiuraSourcePsi C s n (z,q)) univ := by
  intro z _
  exact (analyticOnNhd_sourcePsiCandidate (by simp) (by norm_num) n
    (z,(s n (C.criticalSource q) : Coeff 2)) (mem_univ _)).comp
      (f := fun z : ℂ => (z,(s n (C.criticalSource q) : Coeff 2)))
      (analyticAt_id.prod analyticAt_const)

theorem analyticOnNhd_hillHminusMiuraEnergyPsi_spectral (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℤ) (q : PeriodOneHminusOne) :
    AnalyticOnNhd ℂ (fun z => hillHminusMiuraEnergyPsi C s n (z,q)) univ := by
  have hφ := analyticOnNhd_hillHminusMiuraSourcePsi_spectral C s n q
  have hF : AnalyticOnNhd ℂ (fun z => hillHminusMiuraSourcePsi C s n (z,q)-
      hillHminusMiuraSourcePsi C s n (-z,q)) univ := by
    intro z _
    exact (hφ z (mem_univ _)).sub ((hφ (-z) (mem_univ _)).comp (analyticAt_id.neg))
  have hodd : ∀ z, (hillHminusMiuraSourcePsi C s n (-z,q)-hillHminusMiuraSourcePsi C s n (-(-z),q)) =
      -(hillHminusMiuraSourcePsi C s n (z,q)-hillHminusMiuraSourcePsi C s n (-z,q)) := by
    intro z
    simp only [neg_neg]
    ring
  intro energy _
  exact (analyticOnNhd_oddSquareDescent _ hF hodd (energy+C.energyShift) (mem_univ _)).comp
    (f := fun z : ℂ => z+C.energyShift) (analyticAt_id.add analyticAt_const)

theorem hillHminusMiuraEnergyPsi_central_value (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℤ) (q : PeriodOneHminusOne) :
    hillHminusMiuraEnergyPsi C s n (-C.energyShift,q) =
      deriv (fun z => hillHminusMiuraSourcePsi C s n (z,q)) 0 := by
  let φ : ℂ → ℂ := fun z => hillHminusMiuraSourcePsi C s n (z,q)
  have hφ := analyticOnNhd_hillHminusMiuraSourcePsi_spectral C s n q
  have hd : HasDerivAt φ (deriv φ 0) 0 := (hφ 0 (mem_univ _)).differentiableAt.hasDerivAt
  have hn : HasDerivAt (fun z : ℂ => φ (-z)) (-deriv φ 0) 0 := by
    have hcomp := (hφ (-(0:ℂ)) (mem_univ _)).differentiableAt.hasDerivAt.comp
      (h := fun z : ℂ => -z) 0 ((hasDerivAt_id (0:ℂ)).neg)
    simpa only [neg_zero,mul_neg_one] using! hcomp
  have he := (hd.sub hn).deriv
  change deriv (fun z => φ z-φ (-z)) 0 = deriv φ 0- -deriv φ 0 at he
  change dslope (fun z => φ z-φ (-z)) 0 (sqrt (-C.energyShift+C.energyShift))/2 = deriv φ 0
  rw [neg_add_cancel,sqrt_zero,dslope_same,he]
  ring

theorem hillHminusMiuraEnergyPsi_derivative_ratio_pullback (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℤ)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain) (z : ℂ) (hz : z ≠ 0) :
    hillHminusMiuraEnergyPsi C s n (z^2-C.energyShift,q) /
        deriv (hillHminusDiscriminant q) (z^2-C.energyShift) =
      (hillHminusMiuraSourcePsi C s n (z,q)-hillHminusMiuraSourcePsi C s n (-z,q)) /
        deriv (canonicalDiscriminant (by simp) (periodOnePotential (C.criticalSource q))) z := by
  rw [← hillHminusMiuraEnergyPsi_factor,C.frequency_derivative_eq q hq]
  exact (mul_div_mul_left _ _ (mul_ne_zero (by norm_num) hz)).symm

theorem hillHminusMiuraEnergyCriticalResidue_eq_signed (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℤ)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) (j : ℕ+) :
    hillHminusMiuraEnergyCriticalResidue C s n q j =
      (2*C.frequencyCritical q j)*
        (hillHminusMiuraSignedCriticalResidue C s n q (j:ℤ)-
          hillHminusMiuraSignedCriticalResidue C s n q (-(j:ℤ))) := by
  have hz : C.frequencyCritical q j ≠ 0 := by
    intro h
    have hp := (C.frequencyCritical_pos_real q hr j).1
    rw [h,zero_re] at hp
    exact lt_irrefl _ hp
  have hd := C.energyCritical_simple q hr hq j
  have href := canonicalCriticalPoints_neg_of_discriminant_even_of_realType
    (by simp) (by norm_num) _ (periodOnePotential_mem _) (isRealType_periodOnePotential _ hr)
    (hillMiuraFrequencyTrace_even (C.lift q)) (j:ℤ)
  have hsecond := second_deriv_neg_argument_of_even _ (hillMiuraFrequencyTrace_even (C.lift q))
    (C.frequencyCritical q j)
  change deriv (deriv (canonicalDiscriminant (by simp) (periodOnePotential (C.criticalSource q))))
    (-C.frequencyCritical q j) =
      deriv (deriv (canonicalDiscriminant (by simp) (periodOnePotential (C.criticalSource q))))
        (C.frequencyCritical q j) at hsecond
  unfold hillHminusMiuraEnergyCriticalResidue hillHminusMiuraSignedCriticalResidue
  dsimp only
  rw [href]
  change hillHminusMiuraEnergyPsi C s n (C.energyCritical q j,q) /
      deriv (deriv (hillHminusDiscriminant q)) (C.energyCritical q j) =
    (2*C.frequencyCritical q j)*(hillHminusMiuraSourcePsi C s n (C.frequencyCritical q j,q) /
      deriv (deriv (canonicalDiscriminant (by simp) (periodOnePotential (C.criticalSource q)))) (C.frequencyCritical q j)-
      hillHminusMiuraSourcePsi C s n (-C.frequencyCritical q j,q) /
        deriv (deriv (canonicalDiscriminant (by simp) (periodOnePotential (C.criticalSource q)))) (-C.frequencyCritical q j))
  rw [hsecond,← sub_div,← hillHminusMiuraEnergyPsi_factor,C.frequency_second_derivative_eq q hq]
  change _ = (2*C.frequencyCritical q j)*((2*C.frequencyCritical q j)*
    hillHminusMiuraEnergyPsi C s n (C.energyCritical q j,q) /
      (2*deriv (hillHminusDiscriminant q) (C.energyCritical q j)+
        4*C.frequencyCritical q j^2*deriv (deriv (hillHminusDiscriminant q)) (C.energyCritical q j)))
  rw [C.energyCritical_is_critical q hr hq j,mul_zero,zero_add]
  field_simp [hz,hd]
  ring

theorem hillHminusMiuraEnergyCriticalResidue_principal_limit (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℤ)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) (j : ℕ+) :
    Tendsto (fun energy => (energy-C.energyCritical q j)*
        (hillHminusMiuraEnergyPsi C s n (energy,q)/deriv (hillHminusDiscriminant q) energy))
      (𝓝[≠] C.energyCritical q j) (𝓝 (hillHminusMiuraEnergyCriticalResidue C s n q j)) := by
  have hD : AnalyticOnNhd ℂ (deriv (hillHminusDiscriminant q)) univ := by
    intro z _
    exact (analyticOnNhd_hillHminusDiscriminantDerivative (z,q) (mem_univ _)).comp
      (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)
  exact tendsto_mul_sub_div_at_simple_zero _ _ _
    (analyticOnNhd_hillHminusMiuraEnergyPsi_spectral C s n q _ (mem_univ _)) hD
    (C.energyCritical_is_critical q hr hq j) (C.energyCritical_simple q hr hq j)

theorem analyticAt_hillHminusMiuraEnergyCriticalResidue (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) {V : Set PeriodOneHminusOne}
    (hV : IsOpen V) (hs : ∀ n : ℤ, AnalyticOnNhd ℂ (fun q => s n (C.criticalSource q)) V)
    (n : ℤ) (q : PeriodOneHminusOne) (hq : q ∈ V) (hqC : q ∈ C.domain)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) (j : ℕ+) :
    AnalyticAt ℂ (fun p => hillHminusMiuraEnergyCriticalResidue C s n p j) q := by
  have hE := C.analyticAt_energyCritical_of_realType q hr hqC j
  have hmap := hE.prod (analyticAt_id : AnalyticAt ℂ (fun p : PeriodOneHminusOne => p) q)
  have hP := (analyticOnNhd_hillHminusMiuraEnergyPsi C s hV hs n (C.energyCritical q j,q)
    ⟨mem_univ _,hq⟩).comp (f := fun p => (C.energyCritical p j,p)) hmap
  have hD := (analyticOnNhd_hillHminusDiscriminantSecondDerivative (C.energyCritical q j,q)
    (mem_univ _)).comp (f := fun p => (C.energyCritical p j,p)) hmap
  exact hP.div hD (C.energyCritical_simple q hr hqC j)

theorem analyticAt_hillHminusMiuraEnergyPsi_central_ratio (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) {V : Set PeriodOneHminusOne}
    (hV : IsOpen V) (hs : ∀ n : ℤ, AnalyticOnNhd ℂ (fun q => s n (C.criticalSource q)) V)
    (n : ℤ) (q : PeriodOneHminusOne) (hq : q ∈ V) (hqC : q ∈ C.domain)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) :
    AnalyticAt ℂ (fun t : ℂ × PeriodOneHminusOne => hillHminusMiuraEnergyPsi C s n t /
      deriv (hillHminusDiscriminant t.2) t.1) (-C.energyShift,q) :=
  (analyticOnNhd_hillHminusMiuraEnergyPsi C s hV hs n _ ⟨mem_univ _,hq⟩).div
    (analyticOnNhd_hillHminusDiscriminantDerivative _ (mem_univ _))
    (C.shifted_zero_not_energy_critical q hr hqC)

/-- Constructed actual normalized NLS data precede every numerator and
critical index. The principal limits and the central filling are retained
on one common complex rough-open neighborhood of each real base input. -/
theorem exists_hillHminus_real_energy_critical_residues (q0 : PeriodOneHminusOne)
    (hq0 : periodOneHminusConjugation q0 = q0) :
    ∃ C : HillHminusMiuraChart, ∃ V : Set PeriodOneHminusOne,
      ∃ W₀ W : Set (CoeffPair 2), ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
        IsOpen V ∧ q0 ∈ V ∧ V ⊆ C.domain ∧ 0 < C.energyShift.re ∧ C.energyShift.im = 0 ∧
        SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s ∧
        (∀ q ∈ V, C.criticalSource q ∈ W) ∧
        (∀ n : ℤ, AnalyticOnNhd ℂ (hillHminusMiuraEnergyPsi C s n) (univ ×ˢ V)) ∧
        ∀ q ∈ V, periodOneHminusConjugation q = q → ∀ n : ℤ,
          AnalyticAt ℂ (fun t : ℂ × PeriodOneHminusOne => hillHminusMiuraEnergyPsi C s n t /
            deriv (hillHminusDiscriminant t.2) t.1) (-C.energyShift,q) ∧
          ∀ j : ℕ+,
            AnalyticAt ℂ (fun p => hillHminusMiuraEnergyCriticalResidue C s n p j) q ∧
            hillHminusMiuraEnergyCriticalResidue C s n q j =
              (2*C.frequencyCritical q j)*
                (hillHminusMiuraSignedCriticalResidue C s n q (j:ℤ)-
                  hillHminusMiuraSignedCriticalResidue C s n q (-(j:ℤ))) ∧
            Tendsto (fun energy => (energy-C.energyCritical q j)*
                (hillHminusMiuraEnergyPsi C s n (energy,q)/deriv (hillHminusDiscriminant q) energy))
              (𝓝[≠] C.energyCritical q j) (𝓝 (hillHminusMiuraEnergyCriticalResidue C s n q j)) := by
  obtain ⟨C,V,W₀,W,s,hV,hqV,hVC,_,hpos,hc,hr,H,hVW,_,_,_⟩ :=
    exists_hillHminus_real_normalized_energy_pullbacks q0 hq0
  have hs (n : ℤ) : AnalyticOnNhd ℂ (fun q => s n (C.criticalSource q)) V := by
    intro q hq
    exact (H.analytic n (C.criticalSource q) (hVW q hq)).comp
      (C.analyticOnNhd_criticalSource q (hVC hq))
  refine ⟨C,V,W₀,W,s,hV,hqV,hVC,hpos,hc,H,hVW,
    analyticOnNhd_hillHminusMiuraEnergyPsi C s hV hs,?_⟩
  intro q hq hreal n
  have hsource := (hr q (hVC hq) hreal).2
  exact ⟨analyticAt_hillHminusMiuraEnergyPsi_central_ratio C s hV hs n q hq (hVC hq) hsource,
    fun j => ⟨analyticAt_hillHminusMiuraEnergyCriticalResidue C s hV hs n q hq (hVC hq) hsource j,
      hillHminusMiuraEnergyCriticalResidue_eq_signed C s n q (hVC hq) hsource j,
      hillHminusMiuraEnergyCriticalResidue_principal_limit C s n q (hVC hq) hsource j⟩⟩

end NLS.KdV
