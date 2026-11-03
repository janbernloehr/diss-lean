import NLS.KdV.HillHighAbelianDiscGeometry
import NLS.KdV.HillBoundedComplexTailPeriodControl
import NLS.KdV.HillDeflatedCanonicalRoot

/-! # Actual high-contour bounds for deflated Hill Abelian numerators

The free-contour estimate, physical canonical root comparison and the
endpoint-root factor are combined without differentiating a potential.
-/
noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem norm_scaled_hillHighContour_deflatedHilbertPsi_le
    (N : ℕ) (hN : 1 ≤ N) (B D : ℝ) (hB : 0 ≤ B)
    (hc : HillComplexTailPeriodControl h0q h0r N B D)
    (q : RealPeriodOneHillPotential) (hq : ‖SpectralWeight.one.toCoeff q.val‖ ≤ B)
    (n k : ℕ) (hn : 1 ≤ n) (hk : N ≤ k) (hnk : n ≠ k) (a : Coeff 2) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k))
    (C : ℝ) (hC : 0 ≤ C)
    (herror : ‖hillEnergyCanonicalRootProduct 0 h0q h0r E/
      hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E-1‖ ≤ C*B/(k : ℝ)) :
    ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      (hillAbelianHilbertPsi n (E,a)/hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k E)‖ ≤
        4*Real.pi^2*(1+C*B)*Real.exp ((8/Real.pi^2)*‖a‖) := by
  have hk1 : 1 ≤ k := hN.trans hk
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hfilled := hillHighFreeContour_closedBall_subset_filledDomain h0q h0r N hN B D hc q hq k hk
    (sphere_subset_closedBall hE)
  have hcut := (hillHighFreeGapContour_physical_root_matching h0q h0r N hN B D hc
    q.val q.property.1 q.property.2 hq k hk E hE).1
  let R0 := hillEnergyCanonicalRootProduct 0 h0q h0r E
  let Rq := hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E
  let U := hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k E
  let e := endpointRoot (hillRealLabels q.val q.property.1 q.property.2 (2*k-1))
    (hillRealLabels q.val q.property.1 q.property.2 (2*k)) E
  let s : ℂ := ((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ)
  let P := hillAbelianHilbertPsi n (E,a)
  have hR0 : R0 ≠ 0 := hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain 0 h0q h0r E
    (hillRealGapContour_sphere_subset 0 h0q h0r k hk1 hE)
  have hRq : Rq ≠ 0 := hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain
    q.val q.property.1 q.property.2 E hcut
  have hU : U ≠ 0 := hillDeflatedEnergyCanonicalRoot_ne_zero q.val q.property.1 q.property.2 k hk1 E hfilled
  have hfactor : Rq = e*U :=
    hillEnergyCanonicalRootProduct_eq_endpoint_mul_deflated q.val q.property.1 q.property.2 k hk1 E
  have he : e ≠ 0 := by
    intro hz
    apply hRq
    rw [hfactor,hz,zero_mul]
  have hid : s*(P/U) = e*(s*(P/R0))*(R0/Rq) := by
    rw [hfactor]
    field_simp [hR0,hU,he]
  have hratio : ‖R0/Rq‖ ≤ 1+C*B := by
    have ht := norm_le_norm_sub_add (R0/Rq) (1 : ℂ)
    rw [norm_one] at ht
    have hd : C*B/(k : ℝ) ≤ C*B := div_le_self (mul_nonneg hC hB) hkR
    change ‖R0/Rq-1‖ ≤ C*B/(k : ℝ) at herror
    linarith
  have hend : ‖e‖ ≤ (k : ℝ)*Real.pi^2 :=
    norm_hillHighFreeContour_endpointRoot_le h0q h0r N hN B D hc q hq k hk E hE
  have hpsi : ‖s*(P/R0)‖ ≤ (4/(k : ℝ))*Real.exp ((8/Real.pi^2)*‖a‖) :=
    norm_scaled_hillAbelianHilbertPsi_free_root_le h0q h0r n k hn hk1 hnk E hE a
  change ‖s*(P/U)‖ ≤ _
  rw [hid,norm_mul,norm_mul]
  calc
    _ ≤ ((k : ℝ)*Real.pi^2)*((4/(k : ℝ))*Real.exp ((8/Real.pi^2)*‖a‖))*(1+C*B) :=
      mul_le_mul (mul_le_mul hend hpsi (norm_nonneg _) (by positivity)) hratio
        (norm_nonneg _) (by positivity)
    _ = _ := by field_simp [(by positivity : (k : ℝ) ≠ 0)]

end NLS.KdV
