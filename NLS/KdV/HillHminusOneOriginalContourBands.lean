import NLS.ZakharovShabat.SourceContourAdjacentBands
import NLS.KdV.HillHminusOneOriginalContourRoots
import NLS.KdV.HillHminusOneCanonicalCriticalCompatibility
import NLS.KdV.HillHminusOneCriticalControl

/-! # Original rough Hill contour crossings lie in the correct indexed bands

The actual uniform critical confinement and canonical-label compatibility
locate every original real crossing between the required critical levels.
Positive real shifted-square order and the proved canonical cut exclusion
identify the adjacent NLS bands, including the central first-mode case.
Actual normalized period transfer between loops remains open.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ComplexOrder
namespace NLS.KdV

/-- A real critical energy with the proved small free square-root displacement has exact quadratic free bounds. -/
theorem criticalEnergy_free_bracket_of_sqrt_close (j : ℕ+) (mu : ℂ) (him : mu.im = 0)
    (hclose : ‖sqrt mu-(Real.pi : ℂ)*(j : ℕ)‖ < Real.pi/8) :
    (Real.pi*(j : ℝ)-Real.pi/8)^2 < mu.re ∧
      mu.re < (Real.pi*(j : ℝ)+Real.pi/8)^2 := by
  have hb : |(sqrt mu).re-Real.pi*(j : ℝ)| < Real.pi/8 := by
    simpa using (abs_re_le_norm _).trans_lt hclose
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
  have hpi := Real.pi_pos
  have hmul : Real.pi ≤ Real.pi*(j : ℝ) := by nlinarith
  have hlo : 0 < Real.pi*(j : ℝ)-Real.pi/8 := by linarith
  have hb' := abs_lt.mp hb
  have hz : 0 < (sqrt mu).re := by linarith
  have hzi : (sqrt mu).im = 0 := by
    have he := congrArg Complex.im (sq_sqrt mu)
    simp only [pow_two,mul_im,him] at he
    nlinarith
  have he := congrArg Complex.re (sq_sqrt mu)
  simp only [pow_two,mul_re,hzi,mul_zero,sub_zero] at he
  constructor <;> nlinarith

/-- Small free displacements separate every positive critical level from the original contour crossings. -/
theorem criticalEnergy_original_contour_brackets (mu : ℕ+ → ℂ)
    (him : ∀ j, (mu j).im = 0)
    (hclose : ∀ j, ‖sqrt (mu j)-(Real.pi : ℂ)*(j : ℕ)‖ < Real.pi/8) :
    ∀ k : ℕ+, (Real.pi*(k : ℝ)-Real.pi/4)^2 < (mu k).re ∧
      (mu k).re < (Real.pi*(k : ℝ)+Real.pi/4)^2 ∧
      ∀ j : ℕ+, j < k → (mu j).re < (Real.pi*(k : ℝ)-Real.pi/4)^2 ∧
        (Real.pi*(j : ℝ)+Real.pi/4)^2 < (mu k).re := by
  have hb j := criticalEnergy_free_bracket_of_sqrt_close j (mu j) (him j) (hclose j)
  intro k
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast k.pos
  have hpk : Real.pi ≤ Real.pi*(k : ℝ) := by nlinarith [Real.pi_pos]
  have hleft : (Real.pi*(k : ℝ)-Real.pi/4)^2 < (Real.pi*(k : ℝ)-Real.pi/8)^2 := by
    apply (sq_lt_sq₀ (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).mpr
    linarith [Real.pi_pos]
  have hright : (Real.pi*(k : ℝ)+Real.pi/8)^2 < (Real.pi*(k : ℝ)+Real.pi/4)^2 := by
    apply (sq_lt_sq₀ (by positivity) (by positivity)).mpr
    linarith [Real.pi_pos]
  refine ⟨hleft.trans (hb k).1,(hb k).2.trans hright,?_⟩
  intro j hjk
  have hj : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
  have hjkR : (j : ℝ)+1 ≤ (k : ℝ) := by exact_mod_cast (show (j : ℕ)+1 ≤ (k : ℕ) by exact hjk)
  have hgap : Real.pi*(j : ℝ)+Real.pi ≤ Real.pi*(k : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hjkR Real.pi_pos.le]
  constructor
  · apply (hb j).2.trans
    apply (sq_lt_sq₀ (by positivity) (by linarith [Real.pi_pos])).mpr
    linarith [Real.pi_pos]
  · apply lt_trans _ (hb k).1
    apply (sq_lt_sq₀ (by positivity) (by linarith [Real.pi_pos])).mpr
    linarith [Real.pi_pos]

/-- One rough-open neighborhood controls every actual critical level relative to the original contour crossings. -/
theorem exists_hillHminus_critical_original_contour_brackets (D : HillHminusMiuraChart)
    {N : ℕ} {V : Set PeriodOneHminusOne} (E : HillHminusAllContourPeriodData D N V) :
    ∃ U : Set PeriodOneHminusOne, U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧
      ∀ q ∈ U, periodOneHminusConjugation q = q →
        ∀ k : ℕ+, (Real.pi*(k : ℝ)-Real.pi/4)^2 < (hillHminusUniformCriticalPoint D N k q).re ∧
          (hillHminusUniformCriticalPoint D N k q).re < (Real.pi*(k : ℝ)+Real.pi/4)^2 ∧
          ∀ j : ℕ+, j < k → (hillHminusUniformCriticalPoint D N j q).re < (Real.pi*(k : ℝ)-Real.pi/4)^2 ∧
            (Real.pi*(j : ℝ)+Real.pi/4)^2 < (hillHminusUniformCriticalPoint D N k q).re := by
  obtain ⟨U,hUV,hU,h0U,hbound⟩ := E.exists_uniform_critical_control
  refine ⟨U,hUV,hU,h0U,?_⟩
  intro q hq hreal
  exact criticalEnergy_original_contour_brackets _
    (fun j => (hillHminus_critical_real_and_simple q hreal _ (E.critical_zero j q (hUV hq))).1)
    (fun j => hbound j q hq)

/-- A positive real energy shift preserves the order between squared real crossings and actual critical energies. -/
theorem hillHminus_shifted_frequency_order (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (hr : NLS.ZakharovShabat.IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
    (hcpos : 0 < C.energyShift.re) (hc : C.energyShift.im = 0) (x : ℝ) (j : ℕ+) :
    let y := sqrt (((x^2 : ℝ) : ℂ)+C.energyShift)
    0 < y.re ∧ y.im = 0 ∧
      (x^2 < (C.energyCritical q j).re ↔ y.re < (C.frequencyCritical q j).re) ∧
      ((C.energyCritical q j).re < x^2 ↔ (C.frequencyCritical q j).re < y.re) := by
  dsimp only
  have he : (((x^2 : ℝ) : ℂ)+C.energyShift) = ((x^2+C.energyShift.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hc]
  have hy : sqrt (((x^2 : ℝ) : ℂ)+C.energyShift) = (Real.sqrt (x^2+C.energyShift.re) : ℂ) := by
    rw [he,Complex.sqrt_of_nonneg (by exact_mod_cast (show 0 ≤ x^2+C.energyShift.re by positivity))]
    rfl
  rw [hy]
  simp only [ofReal_re,ofReal_im]
  have hyp : 0 < Real.sqrt (x^2+C.energyShift.re) := Real.sqrt_pos.mpr (by positivity)
  have hys := Real.sq_sqrt (show 0 ≤ x^2+C.energyShift.re by positivity)
  have hb := C.frequencyCritical_pos_real q hr j
  have hmu : (C.energyCritical q j).re = (C.frequencyCritical q j).re^2-C.energyShift.re := by
    simp only [HillHminusMiuraChart.energyCritical,sub_re,pow_two,mul_re,hb.2,mul_zero,sub_zero]
  refine ⟨hyp,trivial,?_,?_⟩
  · rw [hmu]
    constructor <;> intro h <;> nlinarith
  · rw [hmu]
    constructor <;> intro h <;> nlinarith

/-- A canonical-domain energy crossing between consecutive positive critical levels lies in the specific intervening source band. -/
theorem hillHminus_energy_between_critical_mem_sourceBand (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (hr : NLS.ZakharovShabat.IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
    (hcpos : 0 < C.energyShift.re) (hc : C.energyShift.im = 0)
    (x : ℝ) (j : ℕ+) (hroot : ((x^2 : ℝ) : ℂ) ∈ C.energyRootDomain q)
    (hl : (C.energyCritical q j).re < x^2) (hu : x^2 < (C.energyCritical q (j+1)).re) :
    (sqrt (((x^2 : ℝ) : ℂ)+C.energyShift)).re ∈
      NLS.ZakharovShabat.sourceRealBand (by simp) (by norm_num) (C.criticalSource q) (j : ℤ) := by
  have h1 := hillHminus_shifted_frequency_order C q hr hcpos hc x j
  have h2 := hillHminus_shifted_frequency_order C q hr hcpos hc x (j+1)
  let y := sqrt (((x^2 : ℝ) : ℂ)+C.energyShift)
  have hy : (y.re : ℂ) = y := by
    apply Complex.ext
    · rfl
    · simpa only [ofReal_im] using h1.2.1.symm
  apply NLS.ZakharovShabat.sourceRealBand_of_between_canonicalCriticalPoints (by simp) (by norm_num)
    (C.criticalSource q) hr (j : ℤ) y.re
  · rw [hy]
    exact hroot.2
  · exact h1.2.2.2.mp hl
  · have hidx : ((j+1 : ℕ+) : ℤ) = (j : ℤ)+1 := by
      exact_mod_cast (show ((j+1 : ℕ+) : ℕ) = (j : ℕ)+1 by rfl)
    rw [← hidx]
    exact h2.2.2.1.mp hu

/-- A canonical-domain crossing below the first positive critical energy lies in the band following the central gap. -/
theorem hillHminus_energy_before_first_critical_mem_sourceBand (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (hr : NLS.ZakharovShabat.IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
    (hcpos : 0 < C.energyShift.re) (hc : C.energyShift.im = 0)
    (x : ℝ) (hroot : ((x^2 : ℝ) : ℂ) ∈ C.energyRootDomain q)
    (hu : x^2 < (C.energyCritical q 1).re) :
    (sqrt (((x^2 : ℝ) : ℂ)+C.energyShift)).re ∈
      NLS.ZakharovShabat.sourceRealBand (by simp) (by norm_num) (C.criticalSource q) 0 := by
  have h1 := hillHminus_shifted_frequency_order C q hr hcpos hc x 1
  let y := sqrt (((x^2 : ℝ) : ℂ)+C.energyShift)
  have hy : (y.re : ℂ) = y := by
    apply Complex.ext
    · rfl
    · simpa only [ofReal_im] using h1.2.1.symm
  apply NLS.ZakharovShabat.sourceRealBand_of_between_canonicalCriticalPoints (by simp) (by norm_num)
    (C.criticalSource q) hr 0 y.re
  · rw [hy]
    exact hroot.2
  · rw [NLS.ZakharovShabat.canonicalCriticalPoints_zero_of_discriminant_even_of_realType
      (by simp) (by norm_num) _ (NLS.ZakharovShabat.periodOnePotential_mem _)
      (NLS.ZakharovShabat.isRealType_periodOnePotential _ hr)
      (hillMiuraFrequencyTrace_even (C.lift q)),zero_re]
    exact h1.1
  · exact h1.2.2.1.mp hu

/-- All original real contour crossings map to the specific adjacent bands, including the first positive mode. -/
theorem hillHminus_original_crossing_mem_adjacentBands (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (hr : NLS.ZakharovShabat.IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
    (hcpos : 0 < C.energyShift.re) (hc : C.energyShift.im = 0)
    (hclose : ∀ j : ℕ+, ‖sqrt (C.energyCritical q j)-(Real.pi : ℂ)*(j : ℕ)‖ < Real.pi/8)
    (hroot : ∀ k : ℕ+,
      ((((Real.pi*(k : ℝ)-Real.pi/4)^2 : ℝ) : ℂ) ∈ C.energyRootDomain q) ∧
      ((((Real.pi*(k : ℝ)+Real.pi/4)^2 : ℝ) : ℂ) ∈ C.energyRootDomain q)) :
    ∀ k : ℕ+,
      (sqrt ((((Real.pi*(k : ℝ)-Real.pi/4)^2 : ℝ) : ℂ)+C.energyShift)).re ∈
        NLS.ZakharovShabat.sourceRealBand (by simp) (by norm_num) (C.criticalSource q) ((k : ℤ)-1) ∧
      (sqrt ((((Real.pi*(k : ℝ)+Real.pi/4)^2 : ℝ) : ℂ)+C.energyShift)).re ∈
        NLS.ZakharovShabat.sourceRealBand (by simp) (by norm_num) (C.criticalSource q) (k : ℤ) := by
  have hb := criticalEnergy_original_contour_brackets (C.energyCritical q)
    (fun j => C.energyCritical_im_eq_zero q hr hc j) hclose
  intro k
  constructor
  · by_cases hk : k = 1
    · subst k
      have hzero : ((1 : ℕ+) : ℤ)-1 = 0 := by norm_num
      rw [hzero]
      exact hillHminus_energy_before_first_critical_mem_sourceBand C q hr hcpos hc _ (hroot 1).1 (hb 1).1
    · have hkval : 1 < (k : ℕ) := by
        have hp := k.pos
        have hne : (k : ℕ) ≠ 1 := by
          intro he
          apply hk
          exact Subtype.ext he
        omega
      let j : ℕ+ := ⟨(k : ℕ)-1,by omega⟩
      have hs : j+1 = k := by apply Subtype.ext;change (k : ℕ)-1+1=(k : ℕ);omega
      have hjk : j < k := by change (k : ℕ)-1<(k : ℕ);omega
      have hj : (j : ℤ) = (k : ℤ)-1 := by
        have hn : (j : ℕ)+1 = (k : ℕ) := by change (k : ℕ)-1+1=(k : ℕ);omega
        have hz : (j : ℤ)+1 = (k : ℤ) := by exact_mod_cast hn
        omega
      rw [← hj]
      apply hillHminus_energy_between_critical_mem_sourceBand C q hr hcpos hc _ j (hroot k).1
      · exact ((hb k).2.2 j hjk).1
      · rw [hs]
        exact (hb k).1
  · apply hillHminus_energy_between_critical_mem_sourceBand C q hr hcpos hc _ k (hroot k).2
    · exact (hb k).2.1
    · exact ((hb (k+1)).2.2 k (by change (k : ℕ)<(k : ℕ)+1;omega)).2

/-- One common complex neighborhood precedes all real inputs and positive contour indices in the actual adjacent-band identification. -/
theorem exists_hillHminus_original_crossing_bands (C D : HillHminusMiuraChart)
    {N : ℕ} {V : Set PeriodOneHminusOne} (E : HillHminusAllContourPeriodData D N V)
    (h0C : 0 ∈ C.domain) (hcpos : 0 < C.energyShift.re) (hc : C.energyShift.im = 0)
    (hr : ∀ q ∈ C.domain, periodOneHminusConjugation q = q →
      NLS.ZakharovShabat.IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) :
    ∃ U : Set PeriodOneHminusOne, U ⊆ V ∧ U ⊆ C.domain ∧ IsOpen U ∧ 0 ∈ U ∧
      ∀ q ∈ U, periodOneHminusConjugation q = q → ∀ k : ℕ+,
        (sqrt ((((Real.pi*(k : ℝ)-Real.pi/4)^2 : ℝ) : ℂ)+C.energyShift)).re ∈
          NLS.ZakharovShabat.sourceRealBand (by simp) (by norm_num) (C.criticalSource q) ((k : ℤ)-1) ∧
        (sqrt ((((Real.pi*(k : ℝ)+Real.pi/4)^2 : ℝ) : ℂ)+C.energyShift)).re ∈
          NLS.ZakharovShabat.sourceRealBand (by simp) (by norm_num) (C.criticalSource q) (k : ℤ) := by
  obtain ⟨δ,hδ,hδV,hδC,hcompat⟩ := hillHminus_period_data_canonical_compatibility C D E h0C hc hr
  obtain ⟨W,hWV,hW,h0W,hclose⟩ := E.exists_uniform_critical_control
  refine ⟨W ∩ ball 0 δ,fun q hq => hWV hq.1,fun q hq => hδC hq.2,
    hW.inter isOpen_ball,⟨h0W,mem_ball_self hδ⟩,?_⟩
  intro q hq hreal
  have hqc := hδC hq.2
  have hrs := hr q hqc hreal
  apply hillHminus_original_crossing_mem_adjacentBands C q hrs hcpos hc
  · intro j
    rw [← (hcompat q hq.2 hreal).1 j |>.1]
    exact hclose j q hq.1
  · intro k
    have hsphere (sign : ℝ) (hsign : sign = -1 ∨ sign = 1) :
        (((Real.pi*(k : ℝ)+sign*(Real.pi/4) : ℝ) : ℂ)) ∈
          sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) := by
      rw [mem_sphere_iff_norm]
      have he : (((Real.pi*(k : ℝ)+sign*(Real.pi/4) : ℝ) : ℂ))-
          ((Real.pi : ℂ)*(k : ℕ)) = ((sign*(Real.pi/4) : ℝ) : ℂ) := by push_cast;ring
      rw [he,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos (by positivity : 0 < Real.pi/4)]
      rcases hsign with rfl | rfl <;> norm_num
    have hL := hillHminus_original_contour_mem_energyRootDomain C D E q (hWV hq.1) hqc
      hreal hcpos hc hrs k _ (hsphere (-1) (Or.inl rfl))
    have hR := hillHminus_original_contour_mem_energyRootDomain C D E q (hWV hq.1) hqc
      hreal hcpos hc hrs k _ (hsphere 1 (Or.inr rfl))
    constructor
    · simpa only [neg_one_mul,← sub_eq_add_neg,← ofReal_pow] using hL
    · simpa only [one_mul,← ofReal_pow] using hR

end NLS.KdV
