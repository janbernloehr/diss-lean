import NLS.ZakharovShabat.SourcePsiJacobianContourIndependence
import NLS.ZakharovShabat.SourcePsiGapLimitInverseBound
import NLS.SequenceSpaces.CompactEquicontinuousLimit

/-!
# Uniform Jacobian norm convergence on the full gap product

Real contour independence puts all finite Jacobians on a fixed valid
family. Their eventual local root Lipschitz estimates and the actual
pointwise norm limits therefore imply uniform convergence on the
compact full gap product at each fixed real-type potential.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Any valid fixed real-centered family inherits the eventual local
root Lipschitz estimates from the common analytic charts. -/
theorem exists_local_sourcePsiFullRootJacobian_rootLipschitz_on_family
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ c R) (a : Coeff p) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        ∀ b ∈ ball a r, ∀ d ∈ ball a r,
          ‖sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n b) φ -
              sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n d) φ‖ ≤
            L*‖b-d‖ := by
  obtain ⟨c',R',hfamily',r,L,hr,hL,hLip,_⟩ :=
    exists_common_sourcePsi_fullJacobian_rootLipschitz hp hp1 a φ hφ
  refine ⟨r,L,hr,hL,?_⟩
  filter_upwards [hLip] with n hn
  intro b hb d hd
  rw [sourcePsiFullRootJacobian_eq_of_realCentered_families hp hp1 φ hφ
      c c' R R' hfamily hfamily' n (Coeff.deleteCoordinateTo n b),
    sourcePsiFullRootJacobian_eq_of_realCentered_families hp hp1 φ hφ
      c c' R R' hfamily hfamily' n (Coeff.deleteCoordinateTo n d)]
  exact hn b hb d hd

/-- The actual full Jacobians converge in operator norm uniformly
over every full gap-contained root vector at a fixed real-type source,
as the deleted index escapes in either direction. -/
theorem tendstoUniformly_sourcePsiFullRootJacobian_on_gapProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ c R) :
    TendstoUniformly (fun (n : ℤ) (a : sourcePeriodicGapRootSet hp hp1 φ) =>
      sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a.val) φ)
      (sourcePsiGapLimitOperator hp hp1 φ hφ) (Filter.comap Int.natAbs Filter.atTop) := by
  let : CompactSpace (sourcePeriodicGapRootSet hp hp1 φ) :=
    isCompact_iff_compactSpace.mp (isCompact_sourcePeriodicGapRootSet hp hp1 φ)
  apply NLS.tendstoUniformly_of_eventual_local_lipschitz
    (Filter.comap Int.natAbs Filter.atTop)
    (fun (n : ℤ) (a : sourcePeriodicGapRootSet hp hp1 φ) =>
      sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a.val) φ)
    (sourcePsiGapLimitOperator hp hp1 φ hφ)
    (continuous_sourcePsiGapLimitOperator hp hp1 φ hφ)
    (tendsto_sourcePsiFullRootJacobian_to_gapLimit_on_realCentered_family hp hp1 φ hφ c R hfamily)
  intro a
  obtain ⟨r,L,hr,hL,hLip⟩ :=
    exists_local_sourcePsiFullRootJacobian_rootLipschitz_on_family hp hp1 φ hφ c R hfamily a.val
  refine ⟨r,L,hr,hL,?_⟩
  filter_upwards [hLip] with n hn
  intro b hb
  have hb' : b.val ∈ ball a.val r := by simpa only [mem_ball,Subtype.dist_eq] using hb
  simpa only [dist_eq_norm,Subtype.dist_eq] using hn b.val hb' a.val (mem_ball_self hr)

/-- One absolute-index cutoff makes the norm difference small for
all full gap-contained root vectors simultaneously. -/
theorem exists_threshold_sourcePsiFullRootJacobian_gapUniform_small
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ c R)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ n : ℤ, K ≤ n.natAbs → ∀ a : sourcePeriodicGapRootSet hp hp1 φ,
      ‖sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a.val) φ -
          sourcePsiGapLimitOperator hp hp1 φ hφ a‖ < ε := by
  have h := (Metric.tendstoUniformly_iff.mp
    (tendstoUniformly_sourcePsiFullRootJacobian_on_gapProduct hp hp1 φ hφ c R hfamily)) ε hε
  obtain ⟨K,hK⟩ := eventually_atTop.mp (eventually_comap.mp h)
  refine ⟨K,?_⟩
  intro n hn a
  simpa only [dist_eq_norm,norm_sub_rev] using hK n.natAbs hn n rfl a

end NLS.ZakharovShabat
