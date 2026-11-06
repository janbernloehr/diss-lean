import NLS.ZakharovShabat.SourceGapWeightedEtaOriginal

/-! # The square of the actual gap-weighted eta coordinate -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

theorem gapWeightedEta_original_sq (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ∈W) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n≠0) :
    sourceGapWeightedEtaCoordinate hp hp1 n s 1 ψ^2=
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2*
        sourceAngularEtaAnalyticPhase hp hp1 n s ψ := by
  rw [H.gapWeightedEta_original_plus ψ hψ n hgap,mul_pow,← Complex.exp_nat_mul]
  have he : (2 : ℂ)*(I*sourceAngularOriginalEta hp hp1 n s ψ)=
      2*I*sourceAngularOriginalEta hp hp1 n s ψ := by ring
  simp only [Nat.cast_ofNat,he,H.eta_original_integral_phase ψ hψ n hgap]

/-- Both signs vanish at every real collapsed gap of the same original family. -/
theorem gapWeightedEta_original_closed (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ∈W) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n=0)
    (σ : ℂ) : sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ=0 := by
  obtain ⟨P,hμ⟩ := H.angular_original_circles ψ hψ
  have hτ := sourceDirichletRoot_eq_midpoint_of_real_collapsed_gap hp hp1 ψ hreal n
    (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
  change canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n =
    canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n at hτ
  have hs := sourceDirichletEtaSineNumerator_sq_add hp hp1 n ψ
    ((P n).closedBall_subset_omittedDomain (ball_subset_closedBall (hμ n)))
  rw [hτ,hgap,sub_self] at hs
  have hb : sourceDirichletEtaSineNumerator hp hp1 n ψ=0 := sq_eq_zero_iff.mp (by simpa using hs)
  simp only [sourceGapWeightedEtaCoordinate,hτ,hb,sub_self,mul_zero,add_zero,zero_mul]

end SourceLemma12_12Data
end NLS.ZakharovShabat
