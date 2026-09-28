import NLS.ZakharovShabat.SourcePsiLimitMatrixColumns
import NLS.SequenceSpaces.BoundedMatrixLimit
import NLS.SequenceSpaces.BoundedMatrixLimitPointwise

/-!
# The bounded limit psi Jacobian operator

The candidate contour entries determine a bounded operator on `ℓᵖ`:
the escaping full Jacobians have one norm bound and converge
coordinatewise on every single-frequency input. The generic dense
extension theorem assembles these entries into an operator.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The contour-limit matrix at a gap-contained root vector defines
a bounded operator on the full coefficient space. -/
theorem exists_sourcePsiLimitMatrixOperator
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      (∀ m : ℤ,
        0 < R m ∧
        sourcePeriodicSegment hp hp1 φ m ⊆ ball (c m) (R m) ∧
        closedBall (c m) (R m) ⊆
          sourceStandardRootOmittedDomain hp hp1 φ m ∧
        sphere (c m) (R m) ⊆
          sourceCanonicalRootDomain hp hp1 φ) ∧
      ∃ Qstar : Coeff p →L[ℂ] Coeff p, ∃ M : ℝ,
        0 ≤ M ∧ ‖Qstar‖ ≤ M ∧
        (∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
          ‖sourcePsiFullRootJacobian hp hp1 n c R
            (Coeff.deleteCoordinateTo n a) φ‖ ≤ M) ∧
        (∀ x : Coeff p, ∀ m : ℤ,
          Tendsto (fun n : ℤ =>
            (sourcePsiFullRootJacobian hp hp1 n c R
              (Coeff.deleteCoordinateTo n a) φ x) m)
            (Filter.comap Int.natAbs Filter.atTop)
            (𝓝 ((Qstar x) m))) ∧
        ∀ m k : ℤ,
          (Qstar (lp.single p k 1)) m =
            sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m) := by
  classical
  obtain ⟨c,R,hgeom,M,hM,hbound,hentry,hv⟩ :=
    exists_common_sourcePsi_limitMatrixColumns hp hp1 a φ hφ ha
  let v (k : ℤ) : Coeff p := Classical.choose (hv k)
  have hvapply (k m : ℤ) : v k m =
      sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m) :=
    (Classical.choose_spec (hv k)).1 m
  let T : ℤ → Coeff p →L[ℂ] Coeff p := fun n =>
    sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a) φ
  have hentry' (m k : ℤ) :
      Tendsto (fun n : ℤ => (T n (lp.single p k 1)) m)
        (Filter.comap Int.natAbs Filter.atTop) (𝓝 (v k m)) := by
    simpa only [T,hvapply] using hentry m k
  letI : NeBot (Filter.comap Int.natAbs Filter.atTop) :=
    (inferInstance : NeBot (Filter.atTop : Filter ℕ)).comap_of_surj
      Int.natAbs_surjective
  obtain ⟨Qstar,hQnorm,hQcol⟩ :=
    Coeff.exists_bounded_operator_of_entrywise_basis_limit hp
      (Filter.comap Int.natAbs Filter.atTop) T M hM hbound v hentry'
  have hentryQ (m k : ℤ) :
      Tendsto (fun n : ℤ => (T n (lp.single p k 1)) m)
        (Filter.comap Int.natAbs Filter.atTop)
        (𝓝 ((Qstar (lp.single p k 1)) m)) := by
    simpa only [hQcol k] using hentry' m k
  have hpoint (x : Coeff p) (m : ℤ) :
      Tendsto (fun n : ℤ => (T n x) m)
        (Filter.comap Int.natAbs Filter.atTop) (𝓝 ((Qstar x) m)) :=
    Coeff.tendsto_operator_coordinate_of_basis hp
      (Filter.comap Int.natAbs Filter.atTop) T Qstar M hM hQnorm
      hbound hentryQ x m
  refine ⟨c,R,hgeom,Qstar,M,hM,hQnorm,hbound,hpoint,?_⟩
  intro m k
  rw [hQcol k]
  exact hvapply k m

end NLS.ZakharovShabat
