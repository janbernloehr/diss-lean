import NLS.KdV.HillHminusOneMiuraEnergyRoot
import NLS.ComplexAnalysis.ShiftedSquaredCircle

/-! # Normalized actual mapped Hill energy periods near every real rough input

The actual shifted quadratic image is a smooth closed energy contour.
It lies in the proved analytic energy-root domain and has exact raw
Kronecker periods for the constructed entire-energy numerators.
-/
noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem hillHminusMiura_energy_endpoint_zero (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain) (m : ℤ) (z : ℂ)
    (hz : z = canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential (C.criticalSource q))
        (periodOnePotential_mem _) m ∨
      z = canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential (C.criticalSource q))
        (periodOnePotential_mem _) m) :
    hillHminusDiscriminant q (z^2-C.energyShift)^2-4 = 0 := by
  rw [C.trace_shifted_square q hq,
    ← canonicalPeriodic_eq_discriminant_sq_sub_four_finite (by simp) (by norm_num) _ (periodOnePotential_mem _)]
  apply (canonicalPeriodicProduct_eq_zero_iff (by simp) (by norm_num) _ z).mpr
  have hs := canonicalPeriodicEndpoints_mem_spectrum (by simp) (by norm_num)
    (periodOnePotential (C.criticalSource q)) (periodOnePotential_mem _) m
  rcases hz with rfl | rfl
  · exact hs.1
  · exact hs.2

theorem hillHminusMappedEnergyLoop_inside (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by simp) (by norm_num) (C.criticalSource q) (m:ℤ)) :
    (shiftedSquaredCircle (D.center:ℂ) D.radius C.energyShift).Inside (C.energyRootDomain q) := by
  apply shiftedSquaredCircle_inside _ _ _ D.radius_pos.le
  intro z hz
  have hm : (0:ℤ) < m := by exact_mod_cast m.pos
  exact C.shifted_square_mem_energyRootDomain q z
    (D.re_pos_on_closedBall_of_even (by simp) (by norm_num) _
      (hillMiuraFrequencyTrace_even (C.lift q)) hm z (sphere_subset_closedBall hz))
    (D.sphere_subset_rootDomain hz)

theorem hillHminusMappedEnergyLoop_winding (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by simp) (by norm_num) (C.criticalSource q) (m:ℤ))
    (z : ℂ) (hz : z ∈ sourcePeriodicSegment (by simp) (by norm_num) (C.criticalSource q) (m:ℤ)) :
    (shiftedSquaredCircle (D.center:ℂ) D.radius C.energyShift).windingIntegral (z^2-C.energyShift) = 1 := by
  have hm : (0:ℤ) < m := by exact_mod_cast m.pos
  have hpos := D.center_sub_radius_pos_of_even (by simp) (by norm_num) _
    (hillMiuraFrequencyTrace_even (C.lift q)) hm
  exact shiftedSquaredCircle_winding D.center D.radius C.energyShift z D.radius_pos
    (by linarith) (D.gap hz)

theorem hillHminusMiuraEnergyPsi_mapped_period (C : HillHminusMiuraChart)
    {W₀ W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (H : SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s)
    (q : PeriodOneHminusOne) (hq : C.criticalSource q ∈ W) (n m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by simp) (by norm_num) (C.criticalSource q) (m:ℤ)) :
    (shiftedSquaredCircle (D.center:ℂ) D.radius C.energyShift).integral
      (fun energy => hillHminusMiuraEnergyPsi C s (n:ℤ) (energy,q)/C.energyRoot q energy) =
        (2*Real.pi:ℂ)*(if m = n then 1 else 0) := by
  rw [shiftedSquaredCircle_integral]
  have he := circleIntegral.integral_congr (c := (D.center:ℂ)) D.radius_pos.le (f := fun z =>
      (hillHminusMiuraEnergyPsi C s (n:ℤ) (z^2-C.energyShift,q)/
        C.energyRoot q (z^2-C.energyShift))*(2*z))
    (g := fun z => (2*z)*hillHminusMiuraEnergyPsi C s (n:ℤ) (z^2-C.energyShift,q)/
      sourceCanonicalRoot (by simp) (by norm_num) (C.criticalSource q) z) (by
      intro z hz
      dsimp only
      have hm : (0:ℤ) < m := by exact_mod_cast m.pos
      rw [C.energyRoot_shifted_square q z
        (D.re_pos_on_closedBall_of_even (by simp) (by norm_num) _
          (hillMiuraFrequencyTrace_even (C.lift q)) hm z (sphere_subset_closedBall hz))]
      ring)
  rw [he]
  exact hillHminusMiuraEnergyPsi_positive_pullback_period C H q hq n m D

theorem exists_hillHminus_real_normalized_mapped_energy_periods (q0 : PeriodOneHminusOne)
    (hq0 : periodOneHminusConjugation q0 = q0) :
    ∃ C : HillHminusMiuraChart, ∃ V : Set PeriodOneHminusOne,
      ∃ W₀ W : Set (CoeffPair 2), ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
        IsOpen V ∧ q0 ∈ V ∧ V ⊆ C.domain ∧
        (∀ q ∈ C.domain, periodOneHminusConjugation q = q → q ∈ V) ∧
        0 < C.energyShift.re ∧ C.energyShift.im = 0 ∧
        (∀ q ∈ C.domain, periodOneHminusConjugation q = q →
          periodOneL2Conjugation (C.lift q) = C.lift q ∧
            IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) ∧
        SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s ∧
        (∀ q ∈ V, C.criticalSource q ∈ W) ∧
        IsOpen (C.energyRootJointDomain V) ∧
        AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne => C.energyRoot t.2 t.1)
          (C.energyRootJointDomain V) ∧
        (∀ n : ℤ, AnalyticOnNhd ℂ (hillHminusMiuraEnergyPsi C s n) (univ ×ˢ V)) ∧
        (∀ q ∈ V, Nonempty ((m : ℤ) →
          SourceCriticalRootPeriodCircle (by simp) (by norm_num) (C.criticalSource q) m)) ∧
        ∀ q ∈ V, ∀ n m : ℕ+,
          ∀ D : SourceCriticalRootPeriodCircle (by simp) (by norm_num) (C.criticalSource q) (m:ℤ),
            (shiftedSquaredCircle (D.center:ℂ) D.radius C.energyShift).Inside (C.energyRootDomain q) ∧
            (∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) (C.criticalSource q) (m:ℤ),
              (shiftedSquaredCircle (D.center:ℂ) D.radius C.energyShift).windingIntegral
                (z^2-C.energyShift) = 1) ∧
            (shiftedSquaredCircle (D.center:ℂ) D.radius C.energyShift).integral
              (fun energy => hillHminusMiuraEnergyPsi C s (n:ℤ) (energy,q)/C.energyRoot q energy) =
                (2*Real.pi:ℂ)*(if m = n then 1 else 0) := by
  obtain ⟨C,V,W₀,W,s,hV,hqV,hVC,hrealV,hshift,hshiftim,hreal,H,hVW,hpsi,hcircles,_⟩ :=
    exists_hillHminus_real_normalized_energy_pullbacks q0 hq0
  obtain ⟨hrootOpen,hroot⟩ := C.energyRoot_joint H hV hVC hVW
  refine ⟨C,V,W₀,W,s,hV,hqV,hVC,hrealV,hshift,hshiftim,hreal,H,hVW,hrootOpen,hroot,
    hpsi,hcircles,?_⟩
  intro q hq n m D
  exact ⟨hillHminusMappedEnergyLoop_inside C q m D,hillHminusMappedEnergyLoop_winding C q m D,
    hillHminusMiuraEnergyPsi_mapped_period C H q (hVW q hq) n m D⟩

end NLS.KdV
