import NLS.ZakharovShabat.SourcePsiCommonJacobianCharts
import NLS.ZakharovShabat.SourcePsiGapProductCompact

/-!
# Columns of the limiting psi Jacobian matrix

The common full-Jacobian bound and coordinatewise contour limits show
that each column of the candidate `Q*` matrix belongs to `ℓᵖ`.
Semicontinuity of the `ℓᵖ` norm gives the same bound for every column.
This constructs the columns, without yet asserting operator-norm
convergence of the escaping Jacobians.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Gap-contained root data avoid all contours inside the canonical
root domain. -/
theorem sourcePeriodicGapRootSet_avoids_commonContours
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (ψ : CoeffPair p)
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 ψ)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hcircle : ∀ m : ℤ,
      sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    ∀ m k : ℤ, ∀ z ∈ sphere (c m) (R m),
      displacedRoots a k - z ≠ 0 := by
  intro m k z hz hzero
  have heq : displacedRoots a k = z := sub_eq_zero.mp hzero
  exact (hcircle m hz k) (heq ▸ ha k)

/-- At a point of the full gap product, every candidate `Q*` matrix
column is an `ℓᵖ` vector, with one norm bound for all columns. The
contours and bound also control the approximating full Jacobians. -/
theorem exists_common_sourcePsi_limitMatrixColumns_realCentered
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
      ∃ M : ℝ, 0 ≤ M ∧
        (∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
          ‖sourcePsiFullRootJacobian hp hp1 n c R
            (Coeff.deleteCoordinateTo n a) φ‖ ≤ M) ∧
        (∀ m k : ℤ,
          Tendsto (fun n : ℤ =>
            (sourcePsiFullRootJacobian hp hp1 n c R
              (Coeff.deleteCoordinateTo n a) φ (lp.single p k 1)) m)
            (Filter.comap Int.natAbs Filter.atTop)
            (𝓝 (sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m)))) ∧
        ∃ Ktail : ℕ,
          (∀ m : ℤ, Ktail < m.natAbs →
            c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
          (∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
            ∀ m k : ℤ, ∀ _hmn : m ≠ n, ∀ hkn : k ≠ n,
              (sourcePsiFullRootJacobian hp hp1 n c R
                (Coeff.deleteCoordinateTo n a) φ (lp.single p k 1)) m =
                deriv (fun t : ℂ =>
                  sourcePsiDeletedEquationCoordinate hp hp1 n m
                    (Coeff.deleteCoordinateTo n a +
                      Coeff.deletedSingleCLM n k hkn t) φ (c m) (R m)) 0) ∧
        ∀ k : ℤ, ∃ v : Coeff p,
          (∀ m : ℤ,
            v m = sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m)) ∧
          ‖v‖ ≤ M := by
  obtain ⟨c,R,hcReal,hgeom,M,hM,hbound,hentry,Ktail,hfree,hmatrix⟩ :=
    exists_common_sourcePsi_fullJacobian_uniformNorm_entryLimit_realCentered hp hp1 a φ hφ
  have havoid := sourcePeriodicGapRootSet_avoids_commonContours
    hp hp1 a φ ha c R (fun m => (hgeom m).2.2.2)
  have hentryAll (m k : ℤ) := hentry m k (havoid m k)
  refine ⟨c,R,hcReal,hgeom,M,hM,hbound,hentryAll,Ktail,hfree,hmatrix,?_⟩
  intro k
  let e : Coeff p := lp.single p k 1
  let Q : ℤ → Coeff p →L[ℂ] Coeff p := fun n =>
    sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a) φ
  let f : ℤ → ℂ := fun m =>
    sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m)
  have he : ‖e‖ = 1 := by
    dsimp [e]
    rw [lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p))]
    norm_num
  have hcolBound : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      ‖Q n e‖ ≤ M := by
    filter_upwards [hbound] with n hn
    have h := (Q n).le_of_opNorm_le hn e
    simpa only [he, mul_one] using h
  have hlim : Tendsto (fun n : ℤ => ((Q n e : Coeff p) : ℤ → ℂ))
      (Filter.comap Int.natAbs Filter.atTop) (𝓝 f) := by
    rw [tendsto_pi_nhds]
    intro m
    exact hentryAll m k
  let : NeBot (Filter.comap Int.natAbs Filter.atTop) :=
    (inferInstance : NeBot (Filter.atTop : Filter ℕ)).comap_of_surj
      Int.natAbs_surjective
  have hmem : Memℓp f p := by
    apply memℓp_gen'
    intro s
    exact lp.sum_rpow_le_of_tendsto hp hcolBound hlim s
  let v : Coeff p := ⟨f,hmem⟩
  refine ⟨v,fun m => rfl,?_⟩
  exact lp.norm_le_of_tendsto hcolBound hlim

/-- Compatibility form of the real-centered construction, retaining
the original statement. -/
theorem exists_common_sourcePsi_limitMatrixColumns
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
      ∃ M : ℝ, 0 ≤ M ∧
        (∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
          ‖sourcePsiFullRootJacobian hp hp1 n c R
            (Coeff.deleteCoordinateTo n a) φ‖ ≤ M) ∧
        (∀ m k : ℤ,
          Tendsto (fun n : ℤ =>
            (sourcePsiFullRootJacobian hp hp1 n c R
              (Coeff.deleteCoordinateTo n a) φ (lp.single p k 1)) m)
            (Filter.comap Int.natAbs Filter.atTop)
            (𝓝 (sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m)))) ∧
        ∃ Ktail : ℕ,
          (∀ m : ℤ, Ktail < m.natAbs →
            c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
          (∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
            ∀ m k : ℤ, ∀ _hmn : m ≠ n, ∀ hkn : k ≠ n,
              (sourcePsiFullRootJacobian hp hp1 n c R
                (Coeff.deleteCoordinateTo n a) φ (lp.single p k 1)) m =
                deriv (fun t : ℂ =>
                  sourcePsiDeletedEquationCoordinate hp hp1 n m
                    (Coeff.deleteCoordinateTo n a +
                      Coeff.deletedSingleCLM n k hkn t) φ (c m) (R m)) 0) ∧
        ∀ k : ℤ, ∃ v : Coeff p,
          (∀ m : ℤ,
            v m = sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m)) ∧
          ‖v‖ ≤ M := by
  obtain ⟨c,R,_,hdata⟩ :=
    exists_common_sourcePsi_limitMatrixColumns_realCentered hp hp1 a φ hφ ha
  exact ⟨c,R,hdata⟩

end NLS.ZakharovShabat
