import NLS.ZakharovShabat.SourceComplexActionAnalytic
import NLS.ZakharovShabat.SourceAngularThetaPoisson
import NLS.ZakharovShabat.SourceActionPoissonGradient

/-! # Analyticity and finite-source transfer for actual action brackets

The glued indexed actions now have analytic differentials. Their
action-action brackets are analytic on the intersection of the two
indexed action domains with one common almost-real neighborhood.
The branch-independent angle-action bracket is analytic on its actual
open-gap domain. Finite real Fourier approximation transfers prescribed
identities to the entire real locus. The finite spectral computations
remain explicit hypotheses, so these are the continuity statements of
Corollary 13.2 rather than its unproved canonical values.
-/

noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAngularThetaActionBracket (hp : p ≠ ⊤) (hp1 : 1 < p)
    (h2p : (2:ℝ≥0∞) ≤ p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) : ℂ :=
  sourceAngularThetaFunctionalBracket hp hp1 h2p n s (sourceComplexAction hp hp1 m) ψ

/-- The actual mixed bracket is a contour integral of the angle's
bracket with the discriminant. Its logarithmic differential permits
this formula without choosing any representative of the angle. -/
theorem sourceAngularThetaActionBracket_eq_discriminant_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2:ℝ≥0∞) ≤ p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (ch : SourceRealActionBallChart hp hp1 m)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hφ : φ ∈ Metric.ball ch.center ch.radius) :
    sourceAngularThetaActionBracket hp hp1 h2p n m s φ =
      -(Real.pi : ℂ)⁻¹*
        (∮ z in C(ch.spectralCenter,ch.spectralRadius),
          (sourceCanonicalRoot hp hp1 φ z)⁻¹*
            sourceAngularThetaFunctionalBracket hp hp1 h2p n s
              (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z) φ) := by
  have hgeom := ch.geometry φ hφ
  have hcircle := sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ m
    ch.spectralCenter ch.spectralRadius hgeom.1 hgeom.2
  have hint := circleIntegrable_sourceActionVariationCotangent hp hp1 φ
    ch.spectralCenter ch.spectralRadius ch.spectralRadius_pos.le hcircle
  rw [sourceAngularThetaActionBracket,sourceAngularThetaFunctionalBracket,
    fderiv_sourceComplexAction_eq_cotangent_circle_on_chart hp hp1 m ch φ hreal hφ]
  simp only [map_smul,smul_eq_mul]
  rw [NLS.ComplexAnalysis.map_circleIntegral
    (sourceBivector h2p (sourceAngularThetaDifferential hp hp1 n s φ)) hint]
  congr 1
  apply circleIntegral.integral_congr ch.spectralRadius_pos.le
  intro z _
  dsimp only
  simp only [sourceActionVariationCotangent,sourceDiscriminantCotangent,
    sourceAngularThetaFunctionalBracket,map_smul,smul_eq_mul]

theorem exists_global_sourceActionActionBracket_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2:ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ n m : ℤ, AnalyticOnNhd ℂ
        (sourceBracket h2p (sourceComplexAction hp hp1 n) (sourceComplexAction hp hp1 m))
        ((W ∩ sourceComplexActionDomain hp hp1 n) ∩ sourceComplexActionDomain hp hp1 m) := by
  obtain ⟨W,hWopen,hWreal,hI⟩ := exists_global_sourceComplexAction_analyticOnNhd hp hp1
  refine ⟨W,hWopen,hWreal,?_⟩
  intro n m
  apply analyticOnNhd_sourceBracket h2p
  · intro ψ hψ
    exact hI n ψ hψ.1
  · intro ψ hψ
    exact hI m ψ ⟨hψ.1.1,hψ.2⟩

theorem sourceBracket_actions_eq_zero_of_finite_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2:ℝ≥0∞) ≤ p) (n m : ℤ)
    (hfinite : ∀ ψ : CoeffPair p, IsRealType (CoeffPair.toMax p ψ) →
      Coeff.HasFiniteSupport ψ.fst → Coeff.HasFiniteSupport ψ.snd →
        sourceBracket h2p (sourceComplexAction hp hp1 n) (sourceComplexAction hp hp1 m) ψ = 0)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    sourceBracket h2p (sourceComplexAction hp hp1 n) (sourceComplexAction hp hp1 m) φ = 0 := by
  obtain ⟨W,hWopen,hWreal,hbracket⟩ := exists_global_sourceActionActionBracket_analyticOnNhd hp hp1 h2p
  apply eq_of_continuousOn_of_finite_realType hp
    ((hWopen.inter (isOpen_sourceComplexActionDomain hp hp1 n)).inter
      (isOpen_sourceComplexActionDomain hp hp1 m)) (hbracket n m).continuousOn 0
    (fun ψ _ hreal hleft hright => hfinite ψ hreal hleft hright) φ
    ⟨⟨hWreal hreal,realTypeSourceLocus_subset_sourceComplexActionDomain hp hp1 n hreal⟩,
      realTypeSourceLocus_subset_sourceComplexActionDomain hp hp1 m hreal⟩ hreal

namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)

include D

theorem exists_actionBracket_analytic_domain (h2p : (2:ℝ≥0∞) ≤ p) :
    ∃ A : Set (CoeffPair p), IsOpen A ∧ realTypeSourceLocus p ⊆ A ∧ A ⊆ W ∧
      ∀ n m : ℤ, AnalyticOnNhd ℂ (sourceAngularThetaActionBracket hp hp1 h2p n m s)
        ({ψ : CoeffPair p | ψ ∈ A ∧ canonicalPeriodicGap hp hp1
          (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0} ∩
          sourceComplexActionDomain hp hp1 m) := by
  obtain ⟨Wa,hWaopen,hWareal,hI⟩ := exists_global_sourceComplexAction_analyticOnNhd hp hp1
  let A := Wa ∩ W
  refine ⟨A,hWaopen.inter D.source_open,fun _ hreal => ⟨hWareal hreal,D.real_subset hreal⟩,
    inter_subset_right,?_⟩
  intro n m ψ hψ
  exact ((sourceBivector h2p).analyticAt_bilinear _).comp₂
    (D.analyticOnNhd_thetaDifferential n ψ ⟨hψ.1.1.2,hψ.1.2⟩)
    ((hI m).fderiv ψ ⟨hψ.1.1.1,hψ.2⟩)

/-- In particular, choosing `c = if n = m then 1 else 0` supplies
the continuity part of the mixed canonical identity, once its finite
spectral computation has been proved. -/
theorem thetaActionBracket_eq_of_finite_realType (h2p : (2:ℝ≥0∞) ≤ p)
    (n m : ℤ) (c : ℂ)
    (hfinite : ∀ ψ ∈ W, IsRealType (CoeffPair.toMax p ψ) →
      Coeff.HasFiniteSupport ψ.fst → Coeff.HasFiniteSupport ψ.snd →
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0 →
        sourceAngularThetaActionBracket hp hp1 h2p n m s ψ = c)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0) :
    sourceAngularThetaActionBracket hp hp1 h2p n m s φ = c := by
  obtain ⟨A,hAopen,hAreal,hAW,hbracket⟩ := D.exists_actionBracket_analytic_domain h2p
  have hgapOpen : IsOpen {ψ : CoeffPair p | ψ ∈ A ∧ canonicalPeriodicGap hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0} := by
    have heq : {ψ : CoeffPair p | ψ ∈ A ∧ canonicalPeriodicGap hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0} =
        A ∩ {ψ : CoeffPair p | ψ ∈ W ∧ canonicalPeriodicGap hp hp1
          (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0} := by
      ext ψ
      constructor
      · intro hψ
        exact ⟨hψ.1,hAW hψ.1,hψ.2⟩
      · intro hψ
        exact ⟨hψ.1,hψ.2.2⟩
    rw [heq]
    exact hAopen.inter (D.open_gap n)
  apply eq_of_continuousOn_of_finite_realType hp
    (hgapOpen.inter (isOpen_sourceComplexActionDomain hp hp1 m)) (hbracket n m).continuousOn c
    (fun ψ hψ hreal hleft hright => hfinite ψ (hAW hψ.1.1) hreal hleft hright hψ.1.2)
    φ ⟨⟨hAreal hreal,hgap⟩,realTypeSourceLocus_subset_sourceComplexActionDomain hp hp1 m hreal⟩ hreal

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
