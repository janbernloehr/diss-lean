import NLS.KdV.HillSourceRealBandPreservation

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate unitInterval

namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem mem_same_hillRealBand_of_free_and_source
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (j : ℕ) (E : ℝ)
    (hband : E ∈ Ioo (hillRealLabels 0 h0q h0r (2*j)) (hillRealLabels 0 h0q h0r (2*j+1)))
    (hsource : ((E:ℂ),SpectralWeight.one.toCoeff q) ∈ hillL2ContinuationDomain) :
    E ∈ Ioo (hillRealLabels q hq hr (2*j)) (hillRealLabels q hq hr (2*j+1)) := by
  let Q : ℝ → WeightedCoeff SpectralWeight.one.toWeight 2 := fun s => (s : ℂ) • q
  have hQ : Continuous Q := by dsimp only [Q];fun_prop
  have hqp (s : ℝ) : SpectralWeight.one.toCoeff (Q s) ∈ Coeff.paritySubspace 0 := by
    dsimp only [Q]
    rw [map_smul]
    exact (Coeff.paritySubspace 0).smul_mem _ hq
  have hQr (s : ℝ) : IsRealHillPotential (SpectralWeight.one.toCoeff (Q s)) := by
    dsimp only [Q]
    rw [map_smul]
    exact hr.smul_real s
  let L : ℝ → ℝ := fun s => hillRealLabels (Q s) (hqp s) (hQr s) (2*j)
  let U : ℝ → ℝ := fun s => hillRealLabels (Q s) (hqp s) (hQr s) (2*j+1)
  have hL : Continuous L := continuous_hillRealLabels_family Q hQ hqp hQr (2*j)
  have hU : Continuous U := continuous_hillRealLabels_family Q hQ hqp hQr (2*j+1)
  have hL0 : L 0 < E := by simpa only [L,Q,ofReal_zero,zero_smul] using hband.1
  have hU0 : E < U 0 := by simpa only [U,Q,ofReal_zero,zero_smul] using hband.2
  have havoid (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (k : ℕ) :
      hillRealLabels (Q s) (hqp s) (hQr s) k ≠ E := by
    intro he
    have hrad := (mem_hillL2ContinuationDomain_iff ((E:ℂ),SpectralWeight.one.toCoeff q)).mp hsource |>.2 s hs
    have hroot := (hillRealLabels_spec (Q s) (hqp s) (hQr s)).root k
    rw [he] at hroot
    apply hrad
    simpa only [Q,map_smul] using hroot
  have hL1 : L 1 < E := by
    by_contra hle
    obtain ⟨s,hs,he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hL.continuousOn
      ⟨hL0.le,not_lt.mp hle⟩
    exact havoid s hs (2*j) he
  have hU1 : E < U 1 := by
    by_contra hle
    obtain ⟨s,hs,he⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hU.continuousOn
      ⟨not_lt.mp hle,hU0.le⟩
    exact havoid s hs (2*j+1) he
  simpa only [L,U,Q,ofReal_one,one_smul] using
    (show E ∈ Ioo (L 1) (U 1) from ⟨hL1,hU1⟩)

end NLS.KdV
