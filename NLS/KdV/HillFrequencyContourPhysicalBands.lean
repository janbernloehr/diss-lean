import NLS.KdV.HillFreeContourPhysicalBandBounds
import NLS.KdV.HillHminusOnePeriodEntries
import NLS.KdV.HillHminusOneSourcePrimitive
import NLS.ComplexAnalysis.CircleSquaredBandHomotopy

/-! # Common physical band crossings of original frequency and energy circles -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

variable (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- Both crossings of the free energy circle remain in their full indexed
physical bands under the already constructed common period control. -/
theorem hillFreeEnergyCircle_crossings_physical_bands
    (ε B : ℝ) (hc : HillComplexPeriodControl h0q h0r ε B)
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ ε) (k : ℕ) (hk : 1 ≤ k) :
    hillRealGapCenter 0 h0q h0r k-(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) ∈
      Ioo (hillRealLabels q hq hr (2*k-2)) (hillRealLabels q hq hr (2*k-1)) ∧
    hillRealGapCenter 0 h0q h0r k+(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) ∈
      Ioo (hillRealLabels q hq hr (2*k)) (hillRealLabels q hq hr (2*k+1)) := by
  have hb := hillFreeContour_physical_band_bounds_of_control h0q h0r ε B hc q hq hr hp k hk
  have hgap := hillRealGap_mem_free_contour_ball_of_control h0q h0r ε B hc q hq hr hp k hk
  have ha := re_bounds_of_mem_realCenteredBall (hgap (left_mem_segment ℝ _ _))
  have hz := re_bounds_of_mem_realCenteredBall (hgap (right_mem_segment ℝ _ _))
  simp only [ofReal_re] at ha hz
  exact ⟨⟨hb.1,ha.1⟩,⟨hz.2,hb.2⟩⟩

/-- The two original frequency-circle crossings lie in the correct free
bands, including the central first-mode band. -/
theorem hillSquaredFrequencyCircle_crossings_free_bands (k : ℕ+) :
    (Real.pi*(k : ℝ)-Real.pi/4)^2 ∈
      Ioo (hillRealLabels 0 h0q h0r (2*(k : ℕ)-2)) (hillRealLabels 0 h0q h0r (2*(k : ℕ)-1)) ∧
    (Real.pi*(k : ℝ)+Real.pi/4)^2 ∈
      Ioo (hillRealLabels 0 h0q h0r (2*(k : ℕ))) (hillRealLabels 0 h0q h0r (2*(k : ℕ)+1)) := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast k.property
  have hc : Real.pi ≤ Real.pi*(k : ℝ) := by nlinarith [Real.pi_pos]
  have hprev : hillRealLabels 0 h0q h0r (2*(k : ℕ)-2) = (Real.pi*(k : ℝ)-Real.pi)^2 := by
    rw [hillRealLabels_zero]
    have hi : (2*(k : ℕ)-2+1)/2 = (k : ℕ)-1 := by omega
    rw [hi]
    simp only [freeHillValue]
    norm_num [Nat.cast_sub k.property]
    ring
  have hnext : hillRealLabels 0 h0q h0r (2*(k : ℕ)+1) = (Real.pi*(k : ℝ)+Real.pi)^2 := by
    rw [hillRealLabels_zero]
    have hi : (2*(k : ℕ)+1+1)/2 = (k : ℕ)+1 := by omega
    rw [hi]
    simp only [freeHillValue]
    push_cast
    ring
  obtain ⟨hlo,hup⟩ := hillFreeGapEndpoints h0q h0r (k : ℕ) k.property
  have hmid : freeHillValue (k : ℕ) = (Real.pi*(k : ℝ))^2 := by
    simp only [freeHillValue,Int.cast_natCast]
    ring
  rw [hprev,hnext,hlo,hup,hmid]
  constructor <;> constructor
  · exact (sq_lt_sq₀ (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).mpr (by linarith [Real.pi_pos])
  · exact (sq_lt_sq₀ (by linarith [Real.pi_pos]) (by positivity)).mpr (by linarith [Real.pi_pos])
  · exact (sq_lt_sq₀ (by positivity) (by positivity)).mpr (by linarith [Real.pi_pos])
  · exact (sq_lt_sq₀ (by positivity) (by positivity)).mpr (by linarith [Real.pi_pos])

/-- The actual rough source-cover data preserve those two crossings in
the physical bands on the same domain before every contour index. -/
theorem hillSquaredFrequencyCircle_crossings_physical_bands
    (C : HillHminusMiuraChart) {N : ℕ} {V : Set PeriodOneHminusOne}
    (D : HillHminusAllContourPeriodData C N V)
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (u : Coeff 2) (hcoeff : SpectralWeight.one.toCoeff q = Coeff.periodDouble u)
    (hu : periodOneL2Inclusion u ∈ V) (k : ℕ+) :
    (Real.pi*(k : ℝ)-Real.pi/4)^2 ∈
      Ioo (hillRealLabels q hq hr (2*(k : ℕ)-2)) (hillRealLabels q hq hr (2*(k : ℕ)-1)) ∧
    (Real.pi*(k : ℝ)+Real.pi/4)^2 ∈
      Ioo (hillRealLabels q hq hr (2*(k : ℕ))) (hillRealLabels q hq hr (2*(k : ℕ)+1)) := by
  have hk0 : 1 ≤ (k : ℕ) := k.property
  have hsource (a : ℝ) (ha : (a : ℂ) ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
      (((a^2 : ℝ) : ℂ),SpectralWeight.one.toCoeff q) ∈ hillL2ContinuationDomain := by
    rw [hcoeff]
    have he := (hillHminusContinuationDomain_L2_iff ((a : ℂ)^2) u).mp (D.cover k _ hu _ ha)
    simpa only [ofReal_pow] using he
  have hsL : ((Real.pi*(k : ℝ)-Real.pi/4 : ℝ) : ℂ) ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) := by
    rw [mem_sphere,dist_eq_norm,← ofReal_natCast,← ofReal_mul,← ofReal_sub,norm_real,Real.norm_eq_abs]
    rw [show Real.pi*(k : ℝ)-Real.pi/4-Real.pi*(k : ℝ) = -Real.pi/4 by ring,abs_of_neg (by linarith [Real.pi_pos])]
    ring
  have hsU : ((Real.pi*(k : ℝ)+Real.pi/4 : ℝ) : ℂ) ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) := by
    rw [mem_sphere,dist_eq_norm,← ofReal_natCast,← ofReal_mul,← ofReal_sub,norm_real,Real.norm_eq_abs]
    rw [show Real.pi*(k : ℝ)+Real.pi/4-Real.pi*(k : ℝ) = Real.pi/4 by ring,abs_of_pos (by positivity)]
  have hf := hillSquaredFrequencyCircle_crossings_free_bands h0q h0r k
  have hl := mem_same_hillRealBand_of_free_and_source h0q h0r q hq hr ((k : ℕ)-1)
    _ (by simpa only [show 2*((k : ℕ)-1)=2*(k : ℕ)-2 by omega,
      show 2*(k : ℕ)-2+1=2*(k : ℕ)-1 by omega] using hf.1) (hsource _ hsL)
  have hu' := mem_same_hillRealBand_of_free_and_source h0q h0r q hq hr (k : ℕ) _ hf.2 (hsource _ hsU)
  simpa only [show 2*((k : ℕ)-1)=2*(k : ℕ)-2 by omega,
    show 2*(k : ℕ)-2+1=2*(k : ℕ)-1 by omega] using And.intro hl hu'

end NLS.KdV
