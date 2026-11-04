import NLS.ComplexAnalysis.ShiftedSquaredCircleBandHomotopy
import NLS.KdV.HillHminusOneEnergyBands
import NLS.KdV.HillHminusOneMappedEnergyPeriods

/-! # Actual normalized numerator periods on the original rough Hill contours

The matched bands give a homotopy inside the canonical root domain.
Actual normalized mapped NLS periods and boundary root agreement yield
the literal original Kronecker periods, on one constructed common ball
before all real rough inputs and positive mode pairs. No period or
Hilbert-membership uniqueness premise is assumed.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

/-- Every analytic function on the actual canonical root domain has equal integrals on the original and normalized NLS-mapped energy loops. -/
theorem hillHminus_original_mapped_energy_integral_eq (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
    (hcpos : 0 < C.energyShift.re) (hc : C.energyShift.im = 0)
    (k : ℕ+) (D : SourceCriticalRootPeriodCircle (by simp) (by norm_num) (C.criticalSource q) (k : ℤ))
    (hbands :
      (sqrt ((((Real.pi*(k : ℝ)-Real.pi/4)^2 : ℝ) : ℂ)+C.energyShift)).re ∈
        sourceRealBand (by simp) (by norm_num) (C.criticalSource q) ((k : ℤ)-1) ∧
      (sqrt ((((Real.pi*(k : ℝ)+Real.pi/4)^2 : ℝ) : ℂ)+C.energyShift)).re ∈
        sourceRealBand (by simp) (by norm_num) (C.criticalSource q) (k : ℤ))
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (C.energyRootDomain q)) :
    (shiftedSquaredCircle ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) 0).integral f =
      (shiftedSquaredCircle (D.center : ℂ) D.radius C.energyShift).integral f := by
  have hk : 0 < (k : ℤ) := by exact_mod_cast k.pos
  have hleft := hillHminus_shifted_sourceBand_mem_energyBand C q hr hcpos hc ((k : ℤ)-1) (by omega) _ hbands.1
  have hright := hillHminus_shifted_sourceBand_mem_energyBand C q hr hcpos hc (k : ℤ) hk.le _ hbands.2
  have hcross := sourcePeriodCircle_real_crossings_mem_adjacentBands (by simp) (by norm_num)
    (C.criticalSource q) hr (k : ℤ) D
  have hDleft := hillHminus_sourceBand_square_mem_energyBand C q ((k : ℤ)-1) (by omega) _ hcross.1
  have hDright := hillHminus_sourceBand_square_mem_energyBand C q (k : ℤ) hk.le _ hcross.2
  have hshift : (C.energyShift.re : ℂ) = C.energyShift := by
    apply Complex.ext
    · rfl
    · simpa only [ofReal_im] using hc.symm
  let l := fun n : ℤ => (canonicalPeriodicRight (by simp) (by norm_num)
    (periodOnePotential (C.criticalSource q)) (periodOnePotential_mem _) n).re^2-C.energyShift.re
  let u := fun n : ℤ => (canonicalPeriodicLeft (by simp) (by norm_num)
    (periodOnePotential (C.criticalSource q)) (periodOnePotential_mem _) (n+1)).re^2-C.energyShift.re
  have hOld : Real.pi/4 < Real.pi*(k : ℝ) := by
    have hn : (1 : ℝ) ≤ k := by exact_mod_cast k.pos
    nlinarith [Real.pi_pos]
  have hDpos := D.center_sub_radius_pos_of_even (by simp) (by norm_num)
    (C.criticalSource q) (hillMiuraFrequencyTrace_even (C.lift q)) hk
  have hRd : D.radius < D.center := by linarith
  have heq := NLS.ComplexAnalysis.shiftedSquaredCircle_integral_eq_of_real_bands f (C.energyRootDomain q)
    (Real.pi*(k : ℝ)) (Real.pi/4) D.center D.radius 0 C.energyShift.re
    (l ((k : ℤ)-1)) (u ((k : ℤ)-1)) (l (k : ℤ)) (u (k : ℤ))
    (by positivity) hOld
    D.radius_pos hRd
    (by simpa only [sub_zero] using! hleft) hDleft (by simpa only [sub_zero] using! hright) hDright
    (fun z hz => by
      by_cases hi : z.im ≠ 0
      · exact C.nonreal_mem_energyRootDomain q hc hr z hi
      · have hi0 : z.im = 0 := not_ne_iff.mp hi
        rcases hz with hn | hl | hu
        · exact (hi hn).elim
        · exact hillHminusCanonicalEnergyBand_mem_energyRootDomain C q hr hc ((k : ℤ)-1) (by omega) z hi0 hl
        · exact hillHminusCanonicalEnergyBand_mem_energyRootDomain C q hr hc (k : ℤ) hk.le z hi0 hu) hf
  simpa only [hshift,ofReal_mul,ofReal_natCast,ofReal_zero] using! heq

/-- The actual Miura numerator has the literal Kronecker period on an original contour, from proved geometry and canonical/original boundary-root agreement. -/
theorem hillHminusMiuraEnergyPsi_original_period (C : HillHminusMiuraChart)
    {W₀ W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (H : SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s)
    (q : PeriodOneHminusOne) (hqSource : C.criticalSource q ∈ W)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
    (hcpos : 0 < C.energyShift.re) (hc : C.energyShift.im = 0)
    (n k : ℕ+) (D : SourceCriticalRootPeriodCircle (by simp) (by norm_num) (C.criticalSource q) (k : ℤ))
    (hbands :
      (sqrt ((((Real.pi*(k : ℝ)-Real.pi/4)^2 : ℝ) : ℂ)+C.energyShift)).re ∈
        sourceRealBand (by simp) (by norm_num) (C.criticalSource q) ((k : ℤ)-1) ∧
      (sqrt ((((Real.pi*(k : ℝ)+Real.pi/4)^2 : ℝ) : ℂ)+C.energyShift)).re ∈
        sourceRealBand (by simp) (by norm_num) (C.criticalSource q) (k : ℤ))
    (hrootEq : ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
      C.energyRoot q (z^2) = hillHminusContinuedRoot (z^2,q)) :
    (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
      (hillHminusMiuraEnergyPsi C s (n : ℤ) (z^2,q)/hillHminusContinuedRoot (z^2,q))*(2*z)) =
        (2*Real.pi : ℂ)*(if k = n then 1 else 0) := by
  let f := fun energy => hillHminusMiuraEnergyPsi C s (n : ℤ) (energy,q)/C.energyRoot q energy
  have hf : AnalyticOnNhd ℂ f (C.energyRootDomain q) :=
    ((analyticOnNhd_hillHminusMiuraEnergyPsi_spectral C s (n : ℤ) q).mono (subset_univ _)).div
      (C.energyRoot_spectral_real q hr).2 (fun energy he => C.energyRoot_ne_zero q energy he)
  have heq := hillHminus_original_mapped_energy_integral_eq C q hr hcpos hc k D hbands f hf
  rw [hillHminusMiuraEnergyPsi_mapped_period C H q hqSource n k D] at heq
  rw [shiftedSquaredCircle_integral] at heq
  simp only [sub_zero] at heq
  have hi := circleIntegral.integral_congr (c := (Real.pi : ℂ)*(k : ℕ))
    (show 0 ≤ Real.pi/4 by positivity)
    (f := fun z => (hillHminusMiuraEnergyPsi C s (n : ℤ) (z^2,q)/hillHminusContinuedRoot (z^2,q))*(2*z))
    (g := fun z => f (z^2)*(2*z)) (by
      intro z hz
      dsimp only [f]
      rw [hrootEq z hz])
  exact hi.trans heq

/-- One constructed actual normalized data set and norm ball precede all real rough inputs and positive mode pairs in the original contour Kronecker identities. -/
theorem exists_hillHminus_actual_original_periods (Dold : HillHminusMiuraChart)
    {N : ℕ} {U : Set PeriodOneHminusOne} (E : HillHminusAllContourPeriodData Dold N U) :
    ∃ C : HillHminusMiuraChart, ∃ δ : ℝ, ∃ W₀ W : Set (CoeffPair 2),
      ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
        0 < δ ∧ ball (0 : PeriodOneHminusOne) δ ⊆ U ∧
        ball (0 : PeriodOneHminusOne) δ ⊆ C.domain ∧
        0 < C.energyShift.re ∧ C.energyShift.im = 0 ∧
        (∀ q ∈ C.domain, periodOneHminusConjugation q = q →
          IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) ∧
        SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s ∧
        (∀ q ∈ ball (0 : PeriodOneHminusOne) δ, C.criticalSource q ∈ W) ∧
        (∀ n : ℤ, AnalyticOnNhd ℂ (hillHminusMiuraEnergyPsi C s n)
          (univ ×ˢ ball (0 : PeriodOneHminusOne) δ)) ∧
        ∀ q ∈ ball (0 : PeriodOneHminusOne) δ, periodOneHminusConjugation q = q →
          ∀ n k : ℕ+,
            (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
              (hillHminusMiuraEnergyPsi C s (n : ℤ) (z^2,q)/hillHminusContinuedRoot (z^2,q))*(2*z)) =
                (2*Real.pi : ℂ)*(if k = n then 1 else 0) := by
  obtain ⟨C,V,W₀,W,s,hV,h0,hVC,_,hpos,hc,hr,H,hVW,hpsi,hcircles,_⟩ :=
    exists_hillHminus_real_normalized_energy_pullbacks 0 periodOneHminusConjugation_zero
  have hrAll : ∀ q ∈ C.domain, periodOneHminusConjugation q = q →
      IsRealType (CoeffPair.toMax 2 (C.criticalSource q)) := fun q hq hqr => (hr q hq hqr).2
  obtain ⟨B,hBU,hBC,hB,h0B,hbands⟩ := exists_hillHminus_original_crossing_bands C Dold E (hVC h0) hpos hc hrAll
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp (hV.inter hB) 0 ⟨h0,h0B⟩
  have hballV : ball (0 : PeriodOneHminusOne) δ ⊆ V := fun q hq => (hball hq).1
  refine ⟨C,δ,W₀,W,s,hδ,fun q hq => hBU (hball hq).2,hballV.trans hVC,hpos,hc,hrAll,H,
    fun q hq => hVW q (hballV hq),fun n => (hpsi n).mono (fun t ht => ⟨ht.1,hballV ht.2⟩),?_⟩
  intro q hq hreal n k
  have hqV := hballV hq
  have hqC := hVC hqV
  have hrs := hrAll q hqC hreal
  have hrV : ∀ p ∈ V, periodOneHminusConjugation p = p →
      IsRealType (CoeffPair.toMax 2 (C.criticalSource p)) := fun p hp hpr => hrAll p (hVC hp) hpr
  have hpath (r : ℝ) (hrange : r ∈ Icc (0 : ℝ) 1) : (r : ℂ) • q ∈ V := by
    apply hballV
    rw [mem_ball_zero_iff,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hrange.1]
    exact (mul_le_of_le_one_left (norm_nonneg q) hrange.2).trans_lt (mem_ball_zero_iff.mp hq)
  obtain ⟨circles⟩ := hcircles q hqV
  apply hillHminusMiuraEnergyPsi_original_period C H q (hVW q hqV) hrs hpos hc n k (circles (k : ℤ))
    (hbands q (hball hq).2 hreal k)
  intro z hz
  have hroot := hillHminus_original_contour_mem_energyRootDomain C Dold E q (hBU (hball hq).2)
    hqC hreal hpos hc hrs k z hz
  exact C.energyRoot_eq_continuedRoot_of_real_segment H hV hVC hVW h0 hc hrV q hreal hpath
    ⟨hroot,E.cover k q (hBU (hball hq).2) z hz⟩

end NLS.KdV
