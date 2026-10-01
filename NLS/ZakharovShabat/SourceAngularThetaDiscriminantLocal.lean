import NLS.ZakharovShabat.SourceAngularThetaDiscriminant
import NLS.ZakharovShabat.SourceHolomorphicRealCenteredBalls

/-! # The actual theta/discriminant identity as a complex germ

The analytic actual bracket and normalized numerator agree at every
nearby real source. The real-form identity principle gives their local
complex equality, so the full identity can be differentiated in source
directions with the spectral parameter held fixed.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}

/-- At every real open-gap source, the actual theta/discriminant
identity holds throughout a complex neighborhood. -/
theorem eventually_thetaDiscriminant_eq
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n : ℤ) (φ : realTypeSourceLocus p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (w : ℂ) :
    sourceAngularThetaFunctionalBracket hp hp1 h2p n s
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) =ᶠ[𝓝 φ.val]
      (fun ψ => -sourcePsiCandidate n (w,(s n ψ : Coeff p))/2) := by
  let F := sourceAngularThetaFunctionalBracket hp hp1 h2p n s
    (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w)
  let G := fun ψ : CoeffPair p => -sourcePsiCandidate n (w,(s n ψ : Coeff p))/2
  have hφW : φ.val ∈ W := D.real_subset φ.property
  have hs := D.psi.toSourcePsiIsolatingComplexExtension
  obtain ⟨a,ha,_,_,_,_,hball₀,_,_,_,_⟩ := hs.isolation φ
  have hφ₀ : φ.val ∈ W₀ := hball₀ (mem_ball_self ha)
  have hθ := D.analyticOnNhd_thetaDifferential n φ.val ⟨hφW,hgap⟩
  have hΔ := (analyticOnNhd_sourceDiscriminantCotangent_joint hp hp1 (w,φ.val) (mem_univ _)).comp
    (f := fun ψ : CoeffPair p => (w,ψ)) (analyticAt_const.prod analyticAt_id)
  have hF : AnalyticAt ℂ F φ.val :=
    ((sourceBivector h2p).analyticAt_bilinear _).comp₂ hθ hΔ
  have hnum := (hs.analytic_numerator_joint n (w,φ.val) ⟨mem_univ _,hφ₀⟩).comp
    (f := fun ψ : CoeffPair p => (w,ψ)) (analyticAt_const.prod analyticAt_id)
  have hG : AnalyticAt ℂ G φ.val := hnum.neg.div_const
  have hnear := (hF.eventually_analyticAt.and hG.eventually_analyticAt).and
    ((D.open_gap n).mem_nhds ⟨hφW,hgap⟩)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hFdiff : DifferentiableOn ℂ F (ball φ.val r) :=
    fun ψ hψ => (hball hψ).1.1.differentiableAt.differentiableWithinAt
  have hGdiff : DifferentiableOn ℂ G (ball φ.val r) :=
    fun ψ hψ => (hball hψ).1.2.differentiableAt.differentiableWithinAt
  have heq := eqOn_sourceRealCenteredBalls_of_real_agreement hp φ φ r r F G hFdiff hGdiff
    (fun χ hχ => D.thetaDiscriminant_eq h2p n χ (hball hχ.1).2.2 w)
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with ψ hψ
  exact heq ⟨hψ,hψ⟩

/-- Differentiating the actual local identity gives minus half the
normalized numerator's source cotangent, at any fixed parameter. -/
theorem fderiv_thetaDiscriminant_eq_numerator
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n : ℤ) (φ : realTypeSourceLocus p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (w : ℂ) :
    fderiv ℂ (sourceAngularThetaFunctionalBracket hp hp1 h2p n s
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w)) φ.val =
      -(1/2 : ℂ) • fderiv ℂ (fun ψ : CoeffPair p => sourcePsiCandidate n (w,(s n ψ : Coeff p))) φ.val := by
  rw [(D.eventually_thetaDiscriminant_eq h2p n φ hgap w).fderiv_eq]
  have hs := D.psi.toSourcePsiIsolatingComplexExtension
  obtain ⟨a,ha,_,_,_,_,hball,_,_,_,_⟩ := hs.isolation φ
  have hnum := (hs.analytic_numerator_joint n (w,φ.val) ⟨mem_univ _,hball (mem_ball_self ha)⟩).comp
    (f := fun ψ : CoeffPair p => (w,ψ)) (analyticAt_const.prod analyticAt_id)
  have heq : (fun ψ : CoeffPair p => -sourcePsiCandidate n (w,(s n ψ : Coeff p))/2) =
      (fun ψ => (-(1/2) : ℂ)*sourcePsiCandidate n (w,(s n ψ : Coeff p))) := by
    funext ψ
    ring
  rw [heq]
  exact (hnum.differentiableAt.hasFDerivAt.const_mul (-(1/2) : ℂ)).fderiv

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
