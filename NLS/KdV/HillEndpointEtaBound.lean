import NLS.KdV.HillEndpointInverseResonance
import NLS.KdV.HillReducedCouplingNorm
import NLS.KdV.PseudomeasureRootSpaces

/-! Quantitative native eta estimate with the ORIGINAL source constant 16,
using actual inverse responses and the actual common-diagonal matrix. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The exact constant SIXTEEN in the source eta estimate follows from the
actual native residual equation and the proved one-half free-mode lower bound.
No coupling estimate, two-mode factorization or inverse-response bound is
supplied as a hypothesis: all are applied to the ACTUAL original operators. -/
theorem norm_endpointEta_le_sixteen
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/16)
    (f phi : FourierLebesgueSpace (2:ℝ) 1 2)
    (hfn : ‖singularHillL2DomainInclusion f‖=1) (hpn : ‖singularHillL2DomainInclusion phi‖=1)
    (hf : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f=z • singularHillDomainInclusion f)
    (hfree : (1/2:ℝ)*‖singularHillL2DomainInclusion f‖ ≤ ‖hillFreeL2ModeProjection n (singularHillL2DomainInclusion f)‖)
    (gamma eta : ℂ)
    (heta : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) phi-z • singularHillDomainInclusion phi =
      -gamma • singularHillDomainInclusion phi+eta • singularHillDomainInclusion f) :
    ‖eta‖ ≤ 16*(‖gamma‖+‖endpointUpperCoupling r hr hr1 n (q,z)‖+‖endpointLowerCoupling r hr hr1 n (q,z)‖) := by
  have hs2 : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2 := hs.trans (by norm_num)
  let B := endpointReducedFamily r hr hr1 n (q,z)
  let L := (hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n).comp
    ((endpointInverseFamily r hr hr1 n (q,z)).comp (H1EndpointInclusion r hr))
  have herror (a : FourierLebesgueSpace (2:ℝ) 1 2) (ha : ‖singularHillL2DomainInclusion a‖=1) :
      ‖L a-endpointHillH1Coordinates n a‖ ≤ 1/8 := by
    have he := norm_endpointInverseFamily_coordinates_sub_le_L2 r hr hr1 n hn z hz q hs2 a
    rw [ha,mul_one] at he
    exact he.trans (by linarith)
  have huf : (1/4:ℝ) ≤ ‖endpointHillH1Coordinates n f‖ := by
    have hp := norm_hillFreeL2ModeProjection_le_two_coordinates n f
    rw [hfn] at hfree
    linarith
  have hLf : (1/8:ℝ) ≤ ‖L f‖ := by
    have he := herror f hfn
    have ht := norm_sub_norm_le (endpointHillH1Coordinates n f) (L f)
    rw [norm_sub_rev] at ht
    linarith
  have huPhi : ‖endpointHillH1Coordinates n phi‖ ≤ 1 := by
    simpa only [hpn] using norm_endpointHillH1Coordinates_le_L2 n phi
  have hLphi : ‖L phi‖ ≤ 9/8 := by
    have he := herror phi hpn
    calc
      _ = ‖(L phi-endpointHillH1Coordinates n phi)+endpointHillH1Coordinates n phi‖ := by rw [sub_add_cancel]
      _ ≤ ‖L phi-endpointHillH1Coordinates n phi‖+‖endpointHillH1Coordinates n phi‖ := norm_add_le _ _
      _ ≤ 9/8 := by linarith
  have hf0 : f ≠ 0 := by
    intro he
    rw [he,map_zero,norm_zero] at hfn
    norm_num at hfn
  have hdet := (endpointReducedDeterminant_eq_zero_iff r hr hr1 n hn (q,z) hz hs2).mpr ⟨f,hf0,hf⟩
  have hB : ‖B (endpointHillH1Coordinates n phi)‖ ≤
      2*(‖endpointUpperCoupling r hr hr1 n (q,z)‖+‖endpointLowerCoupling r hr hr1 n (q,z)‖) :=
    (norm_endpointReducedFamily_apply_le_couplings r hr hr1 n hn z hz q hs2 hdet _).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left huPhi (by positivity :
        0 ≤ 2*(‖endpointUpperCoupling r hr hr1 n (q,z)‖+‖endpointLowerCoupling r hr hr1 n (q,z)‖)))
  let g := gamma • H1EndpointInclusion r hr phi-eta • H1EndpointInclusion r hr f
  have hforcing : endpointPhysicalPencilFamily r hr1 (q,z) phi=endpointHillHminusOne SpectralWeight.one r hr1 g := by
    dsimp only [g]
    rw [map_sub,map_smul,map_smul,endpointHillHminusOne_H1EndpointInclusion,endpointHillHminusOne_H1EndpointInclusion]
    change z • singularHillDomainInclusion phi-singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) phi = _
    rw [← neg_sub,heta]
    module
  have hred := endpointPhysicalPencil_inhomogeneous_reduced r hr hr1 n hn z hz q hs2 g phi hforcing
  dsimp only [g] at hred
  rw [map_sub,map_smul,map_smul,map_sub,map_smul,map_smul] at hred
  change B (endpointHillH1Coordinates n phi)=gamma • L phi-eta • L f at hred
  have heq : eta • L f=gamma • L phi-B (endpointHillH1Coordinates n phi) := by
    rw [hred]
    module
  have hnorm : ‖eta‖*‖L f‖ ≤ ‖gamma‖*‖L phi‖+‖B (endpointHillH1Coordinates n phi)‖ := by
    rw [← norm_smul,heq]
    exact (norm_sub_le _ _).trans_eq (by rw [norm_smul])
  have hleft := mul_le_mul_of_nonneg_left hLf (norm_nonneg eta)
  have hright := mul_le_mul_of_nonneg_left hLphi (norm_nonneg gamma)
  nlinarith [norm_nonneg gamma]

end NLS.KdV
