import NLS.ZakharovShabat.SourcePsiOriginalLimitOperator

/-!
# The intrinsic original limit Jacobian

Coordinatewise convergence on every lp input determines at most one
bounded operator. The total definition below chooses that operator when
it exists. The existence theorem excludes the default branch everywhere
on the original placed-root domain at real-type sources. Its entries
therefore agree across all original isolating families and circles.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The coordinatewise limit property for the actual full original Jacobians. -/
def SourcePsiOriginalLimitProperty (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p) (Q : Coeff p →L[ℂ] Coeff p) : Prop :=
  ∀ x : Coeff p, ∀ m : ℤ,
    Tendsto (fun n : ℤ => (sourcePsiOriginalFullRootJacobian hp hp1 n a φ x) m)
      (Filter.comap Int.natAbs atTop) (𝓝 ((Q x) m))

/-- A bounded operator is determined by its coordinate limits on all inputs. -/
theorem SourcePsiOriginalLimitProperty.unique
    {hp : p ≠ ⊤} {hp1 : 1 < p} {a : Coeff p} {φ : CoeffPair p}
    {Q R : Coeff p →L[ℂ] Coeff p}
    (hQ : SourcePsiOriginalLimitProperty hp hp1 a φ Q)
    (hR : SourcePsiOriginalLimitProperty hp hp1 a φ R) : Q = R := by
  let : NeBot (Filter.comap Int.natAbs atTop) :=
    (inferInstance : NeBot (atTop : Filter ℕ)).comap_of_surj Int.natAbs_surjective
  ext x m
  exact tendsto_nhds_unique (hQ x m) (hR x m)

/-- The intrinsic Q*; the default branch is excluded on the original domain. -/
def sourcePsiOriginalLimitOperator (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p) : Coeff p →L[ℂ] Coeff p := by
  classical
  exact if h : ∃ Q, SourcePsiOriginalLimitProperty hp hp1 a φ Q then Classical.choose h else 0

/-- Any actual limit identifies the chosen operator and rules out the default branch. -/
theorem SourcePsiOriginalLimitProperty.eq_canonical
    {hp : p ≠ ⊤} {hp1 : 1 < p} {a : Coeff p} {φ : CoeffPair p}
    {Q : Coeff p →L[ℂ] Coeff p} (hQ : SourcePsiOriginalLimitProperty hp hp1 a φ Q) :
    Q = sourcePsiOriginalLimitOperator hp hp1 a φ := by
  classical
  have h : ∃ R, SourcePsiOriginalLimitProperty hp hp1 a φ R := ⟨Q,hQ⟩
  unfold sourcePsiOriginalLimitOperator
  rw [dif_pos h]
  exact hQ.unique (Classical.choose_spec h)

/-- The canonical operator has the proved limit property on the entire original domain. -/
theorem SourceLemma12_4Data.originalLimitOperator_spec
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D) :
    SourcePsiOriginalLimitProperty hp hp1 a φ (sourcePsiOriginalLimitOperator hp hp1 a φ) := by
  obtain ⟨Q,_,_,_,_,_,hQ⟩ := H.exists_originalLimitOperator hD φ hφW hφV hφ a ha
  have h : SourcePsiOriginalLimitProperty hp hp1 a φ Q := hQ
  rwa [← h.eq_canonical]

/-- Every original circle computes the same intrinsic matrix entry. -/
theorem SourceLemma12_4Data.originalLimitOperator_entry
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (m k : ℤ) (d r : ℝ) (hr : 0 < r) (he : D m = ball (d:ℂ) r) :
    (sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p k 1)) m =
      sourcePsiLimitMatrixEntry hp hp1 m k a φ (d:ℂ) r := by
  let : NeBot (Filter.comap Int.natAbs atTop) :=
    (inferInstance : NeBot (atTop : Filter ℕ)).comap_of_surj Int.natAbs_surjective
  exact tendsto_nhds_unique (H.originalLimitOperator_spec hD φ hφW hφV hφ a ha (lp.single p k 1) m)
    (H.originalFullRootJacobian_entry_tendsto hD φ hφW hφV hφ a ha m k d r hr he)

/-- On the gap product this is the previously constructed bijective limit operator. -/
theorem SourceLemma12_4Data.originalLimitOperator_eq_gapLimit
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (φ : CoeffPair p) (hφW : φ ∈ W)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (a : sourcePeriodicGapRootSet hp hp1 φ) :
    sourcePsiOriginalLimitOperator hp hp1 a.val φ = sourcePsiGapLimitOperator hp hp1 φ hφ a := by
  have hlim := (H.originalFullRootJacobian_gapUniform_limit φ hφW hφ).tendsto_at a
  have hprop : SourcePsiOriginalLimitProperty hp hp1 a.val φ (sourcePsiGapLimitOperator hp hp1 φ hφ a) := by
    intro x m
    have hc : Continuous (fun Q : Coeff p →L[ℂ] Coeff p => (Q x) m) :=
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).continuous.comp
        (ContinuousLinearMap.apply ℂ (Coeff p) x).continuous
    exact (hc.tendsto _).comp hlim
  exact hprop.eq_canonical.symm

end NLS.ZakharovShabat
