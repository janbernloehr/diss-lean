import NLS.KdV.PhysicalOffDiagonalFrequencyChart

/-! The actual off-diagonal physical moment correction has compact
source derivatives in the original intermediate weighted ell1 target.
The diagonal action correction and action-space descent are separate. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem PhysicalOffDiagonalFrequencyChart.exists_raw_compact_packet
    {β t ε : ℝ} {ht : 0<t} (P : PhysicalOffDiagonalFrequencyChart β t ε ht) (hε : 0<ε) :
    ∃ G : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev (-β)) 1,
      AnalyticOnNhd ℂ G P.domain ∧
      (∀ q∈P.domain, ∀ j : ℤ, j≤0 → (G q).val j=0) ∧
      (∀ q∈P.domain, ∀ n : ℕ+, (G q).val (n : ℤ)=
        P.physical.offDiagonalCorrection n (periodOneSobolevImageInclusion t ht.le q)) ∧
      ∀ q∈P.domain, IsCompactOperator (fderiv ℂ G q) := by
  let K := (WeightedCoeff.weightIsometry (Weight.sobolev (-(β-ε))) 1).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let J := WeightedCoeff.sobolevInclusion (p := 1) (by linarith : -β≤-(β-ε))
  let F := fun q => K (P.packet q)
  let G := fun q => J (F q)
  have hF : AnalyticOnNhd ℂ F P.domain := analyticOnNhd_postcompose_clm K P.packet P.domain P.analytic_packet
  have hG : AnalyticOnNhd ℂ G P.domain := analyticOnNhd_postcompose_clm J F P.domain hF
  refine ⟨G,hG,?_,?_,?_⟩
  · intro q hq j hj
    change (J (K (P.packet q))).val j=0
    rw [WeightedCoeff.sobolevInclusion_apply]
    change P.packet q j/(Weight.sobolev (-(β-ε)) j : ℂ)=0
    rw [P.nonpositive q hq j hj,zero_div]
  · intro q hq n
    change (J (K (P.packet q))).val (n : ℤ)=_
    rw [WeightedCoeff.sobolevInclusion_apply]
    change P.packet q (n : ℤ)/(Weight.sobolev (-(β-ε)) (n : ℤ) : ℂ)=_
    rw [P.positive q hq n,mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)]
  · intro q hq
    exact isCompactOperator_fderiv_compact_clm J
      (WeightedCoeff.isCompactOperator_sobolevInclusion_strict (by linarith : -β < -(β-ε)))
      F q (hF q hq).differentiableAt

theorem exists_physical_offDiagonal_raw_compact_germ
    (β t : ℝ) (hβ : 0<β) (hβ1 : β<1) (ht : 0<t) (hβt : 2*t=1-β)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hq : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht.le q)) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev (t-1)) 2),
      ∃ B : PhysicalMiuraFrequencyChart,
      ∃ G : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev (-β)) 1,
        IsOpen U ∧ q∈U ∧ U⊆periodOneSobolevImageInclusion t ht.le ⁻¹' B.domain ∧
        AnalyticOnNhd ℂ G U ∧
        (∀ p∈U, ∀ j : ℤ, j≤0 → (G p).val j=0) ∧
        (∀ p∈U, ∀ n : ℕ+, (G p).val (n : ℤ)=
          B.offDiagonalCorrection n (periodOneSobolevImageInclusion t ht.le p)) ∧
        ∀ p∈U, IsCompactOperator (fderiv ℂ G p) := by
  obtain ⟨ε,hε,_hεβ,P,hqP⟩ := exists_physicalOffDiagonalFrequencyChart β t hβ hβ1 ht hβt q hq
  obtain ⟨G,hG,hzero,hpos,hcompact⟩ := P.exists_raw_compact_packet hε
  exact ⟨P.domain,P.physical,G,P.domain_open,hqP,P.domain_subset,hG,hzero,hpos,hcompact⟩

end NLS.KdV
