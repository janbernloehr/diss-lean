import NLS.KdV.HillCommonComplexActionPrefactor
import NLS.KdV.HillCommonActionPrefactorPhysical
import NLS.KdV.HillCommonComplexOwnFactors
import NLS.KdV.HillCommonOwnFactorsPhysical
import NLS.KdV.HillOwnCartesianAmplitude

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillComplexOwnCartesianAmplitude (k : ℕ) (p : Coeff 2) : ℂ :=
  hillComplexActionGapPrefactor h0q h0r k p*hillComplexOwnGapFactor h0q h0r k p

def hillComplexOwnCartesianDualAmplitude (k : ℕ) (p : Coeff 2) : ℂ :=
  hillComplexActionGapPrefactor h0q h0r k p*hillComplexOwnGapDualFactor h0q h0r k p

theorem exists_hillComplexOwnCartesianAmplitudes_common_analytic_bound :
    ∃ C : ℝ, 0<C ∧ ∀ B : ℝ, ∃ N : ℕ, 1≤N ∧ ∀ k : ℕ, N≤k →
      AnalyticOnNhd ℂ (hillComplexOwnCartesianAmplitude h0q h0r k) (ball (0 : Coeff 2) B) ∧
      AnalyticOnNhd ℂ (hillComplexOwnCartesianDualAmplitude h0q h0r k) (ball (0 : Coeff 2) B) ∧
      ∀ p∈ball (0 : Coeff 2) B,
        hillComplexOwnCartesianAmplitude h0q h0r k p*hillComplexOwnCartesianDualAmplitude h0q h0r k p=
          2*hillComplexActionGapRatio h0q h0r k p*(hillLocalGapSquare 0 h0q h0r k p/4) ∧
        ‖hillComplexOwnCartesianAmplitude h0q h0r k p‖^2≤
          C*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)^2/(16*(k:ℝ)) ∧
        ‖hillComplexOwnCartesianDualAmplitude h0q h0r k p‖^2≤
          C*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)^2/(16*(k:ℝ)) := by
  obtain ⟨C,hC,hpref⟩ := exists_hillComplexActionGapPrefactor_common_analytic_bound h0q h0r
  refine ⟨C,hC,?_⟩
  intro B
  obtain ⟨Np,hNp,hp⟩ := hpref B
  obtain ⟨Nf,hNf,hf⟩ := exists_hillComplexOwnGapFactors_common_analytic_bound h0q h0r B
  refine ⟨Np+Nf,hNp.trans (by omega),?_⟩
  intro k hk
  have hkp : Np≤k := by omega
  have hkf : Nf≤k := by omega
  have hk1 := hNp.trans hkp
  have hkpos : 0<(k:ℝ) := by exact_mod_cast (show 0<k by omega)
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  refine ⟨(hp k hkp).1.mul (hf k hkf).1,(hp k hkp).1.mul (hf k hkf).2.1,?_⟩
  intro p hBp
  obtain ⟨hsquare,hpnorm⟩ := (hp k hkp).2 p hBp
  obtain ⟨hprod,hplus,hminus⟩ := (hf k hkf).2.2 p hBp
  refine ⟨?_,?_,?_⟩
  · change (hillComplexActionGapPrefactor h0q h0r k p*hillComplexOwnGapFactor h0q h0r k p)*
        (hillComplexActionGapPrefactor h0q h0r k p*hillComplexOwnGapDualFactor h0q h0r k p)=_
    calc
      _ = hillComplexActionGapPrefactor h0q h0r k p^2*
          (hillComplexOwnGapFactor h0q h0r k p*hillComplexOwnGapDualFactor h0q h0r k p) := by ring
      _ = _ := by rw [hsquare,hprod]
  · rw [hillComplexOwnCartesianAmplitude,norm_mul,mul_pow]
    have hs := pow_le_pow_left₀ (norm_nonneg _) hplus 2
    exact (mul_le_mul hpnorm hs (sq_nonneg _) (by positivity : 0≤C/(k:ℝ))).trans_eq (by field_simp;ring)
  · rw [hillComplexOwnCartesianDualAmplitude,norm_mul,mul_pow]
    have hs := pow_le_pow_left₀ (norm_nonneg _) hminus 2
    exact (mul_le_mul hpnorm hs (sq_nonneg _) (by positivity : 0≤C/(k:ℝ))).trans_eq (by field_simp;ring)

theorem exists_hillComplexOwnCartesianAmplitudes_bounded_real_physical_matching (B : ℝ) :
    ∃ N : ℕ, ∃ hN : 1≤N, ∀ q : WeightedCoeff SpectralWeight.one.toWeight 2,
      ∀ hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0,
      ∀ hr : IsRealHillPotential (SpectralWeight.one.toCoeff q), ‖SpectralWeight.one.toCoeff q‖≤B →
        ∀ k : ℕ, ∀ hk : N≤k,
          hillComplexOwnCartesianAmplitude h0q h0r k (SpectralWeight.one.toCoeff q)=
            hillOwnCartesianAmplitude q hq hr k (hN.trans hk) ∧
          hillComplexOwnCartesianDualAmplitude h0q h0r k (SpectralWeight.one.toCoeff q)=
            (starRingEnd ℂ) (hillOwnCartesianAmplitude q hq hr k (hN.trans hk)) := by
  obtain ⟨Np,hNp,hpref⟩ := exists_hillComplexActionGapPrefactor_bounded_real_physical_matching h0q h0r B
  obtain ⟨Nf,hNf,hfactor⟩ := exists_hillComplexOwnGapFactors_bounded_real_physical_matching h0q h0r B
  refine ⟨Np+Nf,hNp.trans (by omega),?_⟩
  intro q hq hr hp k hk
  have hkp : Np≤k := by omega
  have hkf : Nf≤k := by omega
  constructor
  · rw [hillComplexOwnCartesianAmplitude,hpref q hq hr hp k hkp,(hfactor q hq hr hp k hkf).1]
    rfl
  · rw [hillComplexOwnCartesianDualAmplitude,hpref q hq hr hp k hkp,(hfactor q hq hr hp k hkf).2,
      hillOwnCartesianAmplitude,map_mul]
    simp only [hillActionGapPrefactor,Complex.conj_ofReal]

end NLS.KdV
