import NLS.ZakharovShabat.SourceLemma12_4
import NLS.ZakharovShabat.SourcePsiOriginalJacobian
import NLS.ZakharovShabat.SourcePsiJacobianGapInverseBound

/-!
# Original and selected root Jacobians at real sources

Every valid real-centered contour family computes the original equation,
for every complex root input. Differentiation identifies the actual
operators. The full extension uses the source convention of 2 on the
omitted diagonal. Existing compact gap-product estimates then apply to
these original operators, with their gap-product scope kept explicit.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All complex root inputs give the same equation on any valid contour family. -/
theorem SourceLemma12_4Data.originalEquation_eq_selected
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (φ : CoeffPair p) (hφW : φ ∈ W)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℤ → ℂ) (R : ℤ → ℝ) (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ c R)
    (n : ℤ) (a : DeletedCoeff p n) :
    sourcePsiOriginalEquation hp hp1 n a φ = sourcePsiSelectedEquationSequence hp hp1 n c R a φ := by
  obtain ⟨V,_,_,hφV,_,D,C,hD⟩ := H.previous.quotients.neighborhoods φ hφW
  have hcoord (m : ℤ) : (sourcePsiOriginalEquation hp hp1 n a φ:Coeff p) m =
      sourcePsiEquationCoordinate hp hp1 n m (a:Coeff p) φ (c m) (R m) := by
    obtain ⟨d,r,hr,he⟩ := hD.discs m
    let P := hD.toSourceIsolatingNeighborhoods.periodCircle φ hφV m d r hr he
    rw [H.equation φ hφW n a m P]
    exact sourcePsiEquationCoordinate_eq_of_realCentered_enclosingCircles hp hp1 n m (a:Coeff p) φ hφ
      (P.center:ℂ) (c m) P.radius (R m) (by simp) (hfamily.1 m)
      P.radius_pos (hfamily.2 m).1 P.gap (hfamily.2 m).2.1
      P.closedBall_subset_omittedDomain (hfamily.2 m).2.2.1
  apply Subtype.ext
  ext m
  rw [sourcePsiSelectedEquationSequence_apply_of_exists hp hp1 n c R a φ
    ⟨sourcePsiOriginalEquation hp hp1 n a φ,hcoord⟩]
  exact hcoord m

/-- Equality of functions identifies their actual root derivatives. -/
theorem SourceLemma12_4Data.originalRootJacobian_eq_selected
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (φ : CoeffPair p) (hφW : φ ∈ W)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℤ → ℂ) (R : ℤ → ℝ) (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ c R)
    (n : ℤ) (a : DeletedCoeff p n) :
    sourcePsiOriginalRootJacobian hp hp1 n a φ = sourcePsiSelectedRootJacobian hp hp1 n c R a φ := by
  unfold sourcePsiOriginalRootJacobian sourcePsiSelectedRootJacobian
  congr 1
  funext b
  exact H.originalEquation_eq_selected φ hφW hφ c R hfamily n b

/-- Extend the original Jacobian by 2 at the omitted coordinate. -/
def sourcePsiOriginalFullRootJacobian (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a : Coeff p) (φ : CoeffPair p) : Coeff p →L[ℂ] Coeff p :=
  Coeff.deletedJacobianExtension n (sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) φ)

/-- The full original extension agrees with each valid selected extension. -/
theorem SourceLemma12_4Data.originalFullRootJacobian_eq_selected
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (φ : CoeffPair p) (hφW : φ ∈ W)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (c : ℤ → ℂ) (R : ℤ → ℝ) (hfamily : sourcePsiRealCenteredContourFamily hp hp1 φ c R)
    (n : ℤ) (a : Coeff p) :
    sourcePsiOriginalFullRootJacobian hp hp1 n a φ =
      sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a) φ := by
  unfold sourcePsiOriginalFullRootJacobian sourcePsiFullRootJacobian
  rw [H.originalRootJacobian_eq_selected φ hφW hφ c R hfamily]

/-- On the compact gap product, the original operators converge uniformly. -/
theorem SourceLemma12_4Data.originalFullRootJacobian_gapUniform_limit
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (φ : CoeffPair p) (hφW : φ ∈ W)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    TendstoUniformly (fun (n : ℤ) (a : sourcePeriodicGapRootSet hp hp1 φ) =>
      sourcePsiOriginalFullRootJacobian hp hp1 n a.val φ)
      (sourcePsiGapLimitOperator hp hp1 φ hφ) (Filter.comap Int.natAbs atTop) := by
  obtain ⟨K,V,_,hφV,c,R,hc,_,hgeom⟩ :=
    exists_local_sourcePsi_allGap_realCenteredContourFamily hp hp1 φ hφ
  have hf : sourcePsiRealCenteredContourFamily hp hp1 φ c R := ⟨hc,hgeom φ hφV⟩
  have he : (fun (n : ℤ) (a : sourcePeriodicGapRootSet hp hp1 φ) =>
      sourcePsiOriginalFullRootJacobian hp hp1 n a.val φ) =
      (fun (n : ℤ) (a : sourcePeriodicGapRootSet hp hp1 φ) =>
        sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a.val) φ) := by
    funext n a
    exact H.originalFullRootJacobian_eq_selected φ hφW hφ c R hf n a.val
  rw [he]
  exact tendstoUniformly_sourcePsiFullRootJacobian_on_gapProduct hp hp1 φ hφ c R hf

/-- Actual deleted inverses have one bound on the entire compact gap product. -/
theorem SourceLemma12_4Data.originalRootJacobian_gapUniform_inverse
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (φ : CoeffPair p) (hφW : φ ∈ W)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℤ, ∀ a : sourcePeriodicGapRootSet hp hp1 φ,
      ∃ S : DeletedCoeff p n →L[ℂ] DeletedCoeff p n,
        (sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a.val) φ).comp S =
          ContinuousLinearMap.id ℂ (DeletedCoeff p n) ∧
        S.comp (sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a.val) φ) =
          ContinuousLinearMap.id ℂ (DeletedCoeff p n) ∧ ‖S‖ ≤ M := by
  obtain ⟨K,V,_,hφV,c,R,hc,_,hgeom⟩ :=
    exists_local_sourcePsi_allGap_realCenteredContourFamily hp hp1 φ hφ
  have hf : sourcePsiRealCenteredContourFamily hp hp1 φ c R := ⟨hc,hgeom φ hφV⟩
  obtain ⟨M,hM,hb⟩ := exists_uniform_sourcePsiSelectedRootJacobian_gapInverse_norm hp hp1 φ hφ c R hf
  refine ⟨M,hM,?_⟩
  intro n a
  rw [H.originalRootJacobian_eq_selected φ hφW hφ c R hf]
  exact hb n a

end NLS.ZakharovShabat
