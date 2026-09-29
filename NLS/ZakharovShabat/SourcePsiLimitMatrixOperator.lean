import NLS.ZakharovShabat.SourcePsiLimitMatrixColumns
import NLS.SequenceSpaces.BoundedMatrixLimit
import NLS.SequenceSpaces.BoundedMatrixLimitPointwise
import NLS.ZakharovShabat.SourcePsiJacobianEscapingOffDiagonalTail

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
theorem exists_sourcePsiLimitMatrixOperator_realCentered
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      (∀ m : ℤ, (c m).im = 0) ∧
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
        (∀ m k : ℤ,
          (Qstar (lp.single p k 1)) m =
            sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m)) ∧
        ∃ Kfree : ℕ,
          (∀ m : ℤ, Kfree < m.natAbs →
            c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
          (∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
            ∀ m k : ℤ, ∀ _hmn : m ≠ n, ∀ hkn : k ≠ n,
              (sourcePsiFullRootJacobian hp hp1 n c R
                (Coeff.deleteCoordinateTo n a) φ (lp.single p k 1)) m =
                deriv (fun t : ℂ =>
                  sourcePsiDeletedEquationCoordinate hp hp1 n m
                    (Coeff.deleteCoordinateTo n a +
                      Coeff.deletedSingleCLM n k hkn t) φ (c m) (R m)) 0) ∧
        ∃ Krow Kcol : ℕ, ∃ b : Coeff p,
          (∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
            ∀ m : ℤ, Krow ≤ m.natAbs → m ≠ n →
              ∀ k : ℤ, Kcol ≤ k.natAbs → k ≠ n → m ≠ k →
                ‖(sourcePsiFullRootJacobian hp hp1 n c R
                  (Coeff.deleteCoordinateTo n a) φ
                    (lp.single p k 1)) m‖ ≤
                  ‖b m‖ / ‖((m-k : ℤ) : ℂ)‖) ∧
          ∀ m k : ℤ, Krow ≤ m.natAbs → Kcol ≤ k.natAbs → m ≠ k →
            ‖(Qstar (lp.single p k 1)) m‖ ≤
              ‖b m‖ / ‖((m-k : ℤ) : ℂ)‖ := by
  classical
  obtain ⟨c,R,hcReal,hgeom,M,hM,hbound,hentry,Kfree,hfree,hmatrix,hv⟩ :=
    exists_common_sourcePsi_limitMatrixColumns_realCentered hp hp1 a φ hφ ha
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
  let : NeBot (Filter.comap Int.natAbs Filter.atTop) :=
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
  refine ⟨c,R,hcReal,hgeom,Qstar,M,hM,hQnorm,hbound,hpoint,?_,Kfree,hfree,hmatrix,?_⟩
  · intro m k
    rw [hQcol k]
    exact hvapply k m
  · obtain ⟨Kscalar,Kcol,b,hscalar⟩ :=
      exists_sourcePsi_escaping_offDiagonal_scalarEntryMajorant
        hp hp1 a φ hφ ha
    let Krow := max Kscalar (Kfree+1)
    have hoff : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        ∀ m : ℤ, Krow ≤ m.natAbs → m ≠ n →
          ∀ k : ℤ, Kcol ≤ k.natAbs → k ≠ n → m ≠ k →
            ‖(T n (lp.single p k 1)) m‖ ≤
              ‖b m‖ / ‖((m-k : ℤ) : ℂ)‖ := by
      filter_upwards [hmatrix,hscalar] with n hm hs
      intro m hmr hmn k hkc hkn hmk
      have hmScalar : Kscalar ≤ m.natAbs := by dsimp [Krow] at hmr; omega
      have hmFree : Kfree < m.natAbs := by dsimp [Krow] at hmr; omega
      rw [hm m k hmn hkn, (hfree m hmFree).1, (hfree m hmFree).2]
      exact hs m hmScalar hmn k hkc hkn hmk
    refine ⟨Krow,Kcol,b,hoff,?_⟩
    intro m k hmr hkc hmk
    have hne : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        m ≠ n ∧ k ≠ n := by
      apply eventually_comap.mpr
      apply eventually_atTop.mpr
      refine ⟨max m.natAbs k.natAbs + 1,?_⟩
      intro j hj n hn
      constructor
      · intro hmn
        subst n
        omega
      · intro hkn
        subst n
        omega
    have hboundentry : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        ‖(T n (lp.single p k 1)) m‖ ≤
          ‖b m‖ / ‖((m-k : ℤ) : ℂ)‖ := by
      filter_upwards [hoff,hne] with n hn hmn
      exact hn m hmr hmn.1 k hkc hmn.2 hmk
    exact le_of_tendsto (hpoint (lp.single p k 1) m).norm hboundentry

/-- Compatibility form of the real-centered construction, retaining
the original statement. -/
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
        (∀ m k : ℤ,
          (Qstar (lp.single p k 1)) m =
            sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m)) ∧
        ∃ Kfree : ℕ,
          (∀ m : ℤ, Kfree < m.natAbs →
            c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
          (∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
            ∀ m k : ℤ, ∀ _hmn : m ≠ n, ∀ hkn : k ≠ n,
              (sourcePsiFullRootJacobian hp hp1 n c R
                (Coeff.deleteCoordinateTo n a) φ (lp.single p k 1)) m =
                deriv (fun t : ℂ =>
                  sourcePsiDeletedEquationCoordinate hp hp1 n m
                    (Coeff.deleteCoordinateTo n a +
                      Coeff.deletedSingleCLM n k hkn t) φ (c m) (R m)) 0) ∧
        ∃ Krow Kcol : ℕ, ∃ b : Coeff p,
          (∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
            ∀ m : ℤ, Krow ≤ m.natAbs → m ≠ n →
              ∀ k : ℤ, Kcol ≤ k.natAbs → k ≠ n → m ≠ k →
                ‖(sourcePsiFullRootJacobian hp hp1 n c R
                  (Coeff.deleteCoordinateTo n a) φ
                    (lp.single p k 1)) m‖ ≤
                  ‖b m‖ / ‖((m-k : ℤ) : ℂ)‖) ∧
          ∀ m k : ℤ, Krow ≤ m.natAbs → Kcol ≤ k.natAbs → m ≠ k →
            ‖(Qstar (lp.single p k 1)) m‖ ≤
              ‖b m‖ / ‖((m-k : ℤ) : ℂ)‖ := by
  obtain ⟨c,R,_,hdata⟩ :=
    exists_sourcePsiLimitMatrixOperator_realCentered hp hp1 a φ hφ ha
  exact ⟨c,R,hdata⟩

end NLS.ZakharovShabat
