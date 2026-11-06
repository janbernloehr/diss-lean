import NLS.KdV.HillHighAbelianContourBounds
import NLS.KdV.HillAbelianSpectralScale

/-! # Uniform inverse-square decay of the actual deflated Abelian differential

The constants are uniform on a bounded set of real Hill potentials. The
Hilbert numerator parameter is retained explicitly for local analytic branches.
-/
noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillHighContour_deflatedHilbertPsi_sq_decay
    (B : ℝ) (hB : 0 ≤ B) (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ K : ℝ, 0 < K ∧
      ∀ q : RealPeriodOneHillPotential, ‖SpectralWeight.one.toCoeff q.val‖ ≤ B →
      ∀ a : Coeff 2, ∀ k : ℕ, N ≤ k → ∀ E ∈
        sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
          (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
        ‖hillAbelianHilbertPsi n (E,a)/
          hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k E‖ ≤
            K*(n : ℝ)*Real.exp ((8/Real.pi^2)*‖a‖)/(k : ℝ)^2 := by
  obtain ⟨N₁,hN₁,C,hC,hinv⟩ :=
    exists_hillFreeGapContour_bounded_complex_tail_inverse_bound h0q h0r B
  obtain ⟨N₂,hN₂,D,hD,hcontrol⟩ := exists_hillComplexTailPeriodControl h0q h0r B
  refine ⟨max (max N₁ N₂) (2*n),by omega,4*Real.pi^2*(1+C*B),by positivity,?_⟩
  intro q hq a k hk E hE
  have hk₁ : N₁ ≤ k := (le_max_left N₁ N₂).trans ((le_max_left _ _).trans hk)
  have hk₂ : N₂ ≤ k := (le_max_right N₁ N₂).trans ((le_max_left _ _).trans hk)
  have hk2 : 2*n ≤ k := (le_max_right _ _).trans hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm := (hillHighFreeGapContour_physical_root_matching h0q h0r N₂ hN₂ B D hcontrol
    q.val q.property.1 q.property.2 hq k hk₂ E hE).2
  have herr := (hinv (SpectralWeight.one.toCoeff q.val) hq k hk₁ E hE).2
  rw [hm] at herr
  have herr' : ‖hillEnergyCanonicalRootProduct 0 h0q h0r E/
      hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E-1‖ ≤ C*B/(k : ℝ) :=
    herr.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hq hC.le) hkpos.le)
  have hb := norm_scaled_hillHighContour_deflatedHilbertPsi_le h0q h0r N₂ hN₂ B D hB hcontrol
    q hq n k hn hk₂ (by omega) a E hE C hC.le herr'
  rw [norm_mul,norm_freeHill_Abelian_scale n k hn hk2] at hb
  let H := ‖hillAbelianHilbertPsi n (E,a)/
    hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k E‖
  have hH : 0 ≤ H := norm_nonneg _
  have hg := mul_le_mul_of_nonneg_right (sq_le_freeHillValue_sub_of_two_mul_le n k hn hk2) hH
  have hb' : (freeHillValue k-freeHillValue n)*H ≤
      (4*Real.pi^2*(1+C*B)*Real.exp ((8/Real.pi^2)*‖a‖))*(n : ℝ) := by
    apply (div_le_iff₀ hnpos).mp
    simpa only [div_mul_eq_mul_div] using hb
  apply (le_div_iff₀ (sq_pos_of_pos hkpos)).mpr
  calc
    H*(k : ℝ)^2 = (k : ℝ)^2*H := mul_comm _ _
    _ ≤ (freeHillValue k-freeHillValue n)*H := hg
    _ ≤ _ := hb'
    _ = _ := by ring

end NLS.KdV
