import NLS.KdV.HillHminusEndpointPhaseCotangent

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- At every all-periodic original source, the COMPLETE original physical
phase germs commute for every pair of open selected gaps. Every other gap
may be collapsed. This is the genuine H-minus-one Gardner bracket. -/
theorem hillOriginalFullPhases_hminus_Gardner_endpoint_zero
    (q : RealPeriodOneHillPotential) (n m : ℕ+)
    (hgapn : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (hgapm : hillRealGapHalfLength q.val q.property.1 q.property.2 m ≠ 0)
    (hterminal : ∀ k : ℕ, ∀ hk : 1 ≤ k,
      hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk = 0)
    (F G : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hG : AnalyticAt ℂ G (hillOriginalHminusSource q.val))
    (hFM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = hillOriginalFullPhaseFactor n p)
    (hGM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (hillOriginalHminusSource p.val) = hillOriginalFullPhaseFactor m p) :
    NLS.Poisson.hminusGardnerBracket F G (hillOriginalHminusSource q.val) = 0 := by
  obtain ⟨c,a,_,_,hFa,hzero⟩ :=
    exists_hillOriginalFullPhase_hminus_endpoint_cotangent q n hgapn hterminal F hF hFM
  obtain ⟨d,b,hd,hbc,hGb,_⟩ :=
    exists_hillOriginalFullPhase_hminus_endpoint_cotangent q m hgapm hterminal G hG hGM
  have hb : b = hillInfiniteNormingUnitCotangent (by simp) (by simp [IsRealHillPotential]) q d hd := by
    apply Subtype.ext
    funext k
    exact hbc k
  unfold NLS.Poisson.hminusGardnerBracket
  rw [hFa,hGb,hb]
  simp only [map_smul,smul_apply,smul_eq_mul,hzero d hd,mul_zero]

end NLS.KdV
