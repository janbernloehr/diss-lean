import NLS.KdV.HillLocalHilbertRepresentation
import NLS.KdV.HillHighNormalizedContourBound

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem exists_hillSelectedPsi_locally_uniform_scaled_contour_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        ∀ k : ℕ, N ≤ k → n ≠ k → ∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
          (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
          ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
            (hillAbelianSelectedGlobalPsi r.val r.property.1 r.property.2 n hn E /
              hillEnergyCanonicalRootProduct r.val r.property.1 r.property.2 E)‖ ≤ C/(k : ℝ) := by
  obtain ⟨a,P,ha,hP,hP0,hrep⟩ := exists_hillSelectedPsi_analytic_hilbert_representation q hq hr h0q h0r n hn
  let p0 := SpectralWeight.one.toCoeff q
  let B : ℝ := ‖p0‖+1
  let H : ℝ := ‖a p0‖+1
  let L : ℝ := ‖P p0‖/2
  have hB : 0 < B := by positivity
  have hL : 0 < L := half_pos (norm_pos_iff.mpr hP0)
  have hpB : ∀ᶠ p in 𝓝 p0, ‖p‖ < B :=
    continuous_norm.continuousAt.eventually (isOpen_Iio.mem_nhds (by change ‖p0‖ < ‖p0‖+1;linarith))
  have haH : ∀ᶠ p in 𝓝 p0, ‖a p‖ < H :=
    ha.continuousAt.norm.eventually (isOpen_Iio.mem_nhds (by change ‖a p0‖ < ‖a p0‖+1;linarith))
  have hPL : ∀ᶠ p in 𝓝 p0, L < ‖P p‖ :=
    hP.continuousAt.norm.eventually (isOpen_Ioi.mem_nhds (by change ‖P p0‖/2 < ‖P p0‖;linarith [norm_pos_iff.mpr hP0]))
  let Q : RealPeriodOneHillPotential → Coeff 2 := fun r => SpectralWeight.one.toCoeff r.val
  have hQ : Continuous Q := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have hT : Tendsto Q (𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)) (𝓝 p0) := hQ.tendsto _
  obtain ⟨N,hN,D,hD,hcontrol⟩ := exists_hillAbelianComplexPeriod_bounded_tail_control h0q h0r B
  obtain ⟨M,hM,A,hA,hinverse⟩ := exists_hillFreeGapContour_bounded_complex_tail_inverse_bound h0q h0r B
  refine ⟨max N M,hN.trans (le_max_left _ _),4*Real.exp ((8/Real.pi^2)*H)*(1+A*B)/L,by positivity,?_⟩
  filter_upwards [hrep,hT.eventually hpB,hT.eventually haH,hT.eventually hPL] with r hrrep hrB hrH hrL
  intro k hk hnk E hE
  have hkN : N ≤ k := (le_max_left N M).trans hk
  have hkM : M ≤ k := (le_max_right N M).trans hk
  have hk1 : 1 ≤ k := hN.trans hkN
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hmatch := (hillHighFreeGapContour_physical_root_matching h0q h0r N hN B D hcontrol
    r.val r.property.1 r.property.2 hrB.le k hkN E hE).2
  have hinv := (hinverse (Q r) hrB.le k hkM E hE).2
  rw [hmatch] at hinv
  have hratio : ‖hillEnergyCanonicalRootProduct 0 h0q h0r E /
      hillEnergyCanonicalRootProduct r.val r.property.1 r.property.2 E‖ ≤ 1+A*B := by
    have h := norm_le_norm_sub_add (hillEnergyCanonicalRootProduct 0 h0q h0r E /
      hillEnergyCanonicalRootProduct r.val r.property.1 r.property.2 E) 1
    rw [norm_one] at h
    have hd : A*‖Q r‖/(k : ℝ) ≤ A*‖Q r‖ := div_le_self (by positivity) hkreal
    have hmul : A*‖Q r‖ ≤ A*B := mul_le_mul_of_nonneg_left hrB.le hA.le
    exact h.trans (by linarith)
  have hfree := norm_scaled_hillAbelianHilbertPsi_free_root_le h0q h0r n k hn hk1 hnk E hE (a (Q r))
  have hfree' : ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      (hillAbelianHilbertPsi n (E,a (Q r))/hillEnergyCanonicalRootProduct 0 h0q h0r E)‖ ≤
      (4/(k : ℝ))*Real.exp ((8/Real.pi^2)*H) := by
    apply hfree.trans
    gcongr
  have hroot : hillEnergyCanonicalRootProduct 0 h0q h0r E ≠ 0 :=
    hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain 0 h0q h0r E
      (hillRealGapContour_sphere_subset 0 h0q h0r k hk1 hE)
  have he : (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      (hillAbelianSelectedGlobalPsi r.val r.property.1 r.property.2 n hn E /
        hillEnergyCanonicalRootProduct r.val r.property.1 r.property.2 E) =
      ((((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
        (hillAbelianHilbertPsi n (E,a (Q r))/hillEnergyCanonicalRootProduct 0 h0q h0r E))*
          (hillEnergyCanonicalRootProduct 0 h0q h0r E /
            hillEnergyCanonicalRootProduct r.val r.property.1 r.property.2 E)/P (Q r) := by
    rw [← hrrep E]
    dsimp only [Q]
    field_simp
  rw [he,norm_div,norm_mul]
  apply (div_le_div₀ (by positivity : 0 ≤ (4/(k : ℝ))*Real.exp ((8/Real.pi^2)*H)*(1+A*B))
    (mul_le_mul hfree' hratio (norm_nonneg _) (by positivity)) hL hrL.le).trans_eq
  ring

end NLS.KdV
