import NLS.ZakharovShabat.SourcePsiOriginalJacobianScalarLimit
import NLS.SequenceSpaces.BoundedMatrixLimitPointwise
import NLS.SequenceSpaces.OperatorBasisExt

/-!
# The bounded Q* operator on the full original domain

The original full Jacobians have an eventual common norm bound at every
real-type source and every complex root input. On the original placed-root
domain, their scalar limits therefore define a bounded operator. Its
entries agree with every supplied original circle, and convergence holds
coordinatewise on every lp input. Operator-norm convergence is a later step.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Away from the omitted output row, the full extension has the actual entry. -/
theorem sourcePsiOriginalFullRootJacobian_entry
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m k : ℤ) (hmn : m ≠ n)
    (a : Coeff p) (φ : CoeffPair p) :
    (sourcePsiOriginalFullRootJacobian hp hp1 n a φ (lp.single p k 1)) m =
      sourcePsiOriginalJacobianEntry hp hp1 n m k a φ := by
  exact Coeff.deletedOperatorExtension_apply_other n m hmn 2
    (sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) φ) (lp.single p k 1)

/-- An eventual norm bound for every full root input, without any placement premise. -/
theorem SourceLemma12_4Data.originalFullRootJacobian_eventually_bounded
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (φ : CoeffPair p) (hφW : φ ∈ W)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (a : Coeff p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n : ℤ in Filter.comap Int.natAbs atTop,
      ‖sourcePsiOriginalFullRootJacobian hp hp1 n a φ‖ ≤ M := by
  obtain ⟨c,R,hc,hgeom,M,hM,hb,_⟩ :=
    exists_common_sourcePsi_fullJacobian_uniformNorm_entryLimit_realCentered hp hp1 a φ hφ
  refine ⟨M,hM,?_⟩
  filter_upwards [hb] with n hn
  rw [H.originalFullRootJacobian_eq_selected φ hφW hφ c R ⟨hc,hgeom⟩]
  exact hn

/-- Scalar convergence also holds for the full extensions with their 2 diagonal fill. -/
theorem SourceLemma12_4Data.originalFullRootJacobian_entry_tendsto
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (m k : ℤ) (d r : ℝ) (hr : 0 < r) (he : D m = ball (d:ℂ) r) :
    Tendsto (fun n : ℤ => (sourcePsiOriginalFullRootJacobian hp hp1 n a φ (lp.single p k 1)) m)
      (Filter.comap Int.natAbs atTop)
      (𝓝 (sourcePsiLimitMatrixEntry hp hp1 m k a φ (d:ℂ) r)) := by
  apply (H.originalJacobianEntry_tendsto hD φ hφW hφV hφ a ha m k d r hr he).congr'
  have hne : ∀ᶠ n : ℤ in Filter.comap Int.natAbs atTop, m ≠ n := by
    apply eventually_comap.mpr
    apply eventually_atTop.mpr
    refine ⟨m.natAbs+1,?_⟩
    intro j hj n hn hmn
    subst n
    omega
  filter_upwards [hne] with n hn
  exact (sourcePsiOriginalFullRootJacobian_entry hp hp1 n m k hn a φ).symm

/-- The literal contour-limit columns belong to lp and define a bounded operator
on every original placed-root input, including roots outside the gaps. -/
theorem SourceLemma12_4Data.exists_originalLimitOperator
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D) :
    ∃ Q : Coeff p →L[ℂ] Coeff p, ∃ M : ℝ, 0 ≤ M ∧ ‖Q‖ ≤ M ∧
      (∀ᶠ n : ℤ in Filter.comap Int.natAbs atTop,
        ‖sourcePsiOriginalFullRootJacobian hp hp1 n a φ‖ ≤ M) ∧
      (∀ m k : ℤ, ∀ d r : ℝ, 0 < r → D m = ball (d:ℂ) r →
        (Q (lp.single p k 1)) m = sourcePsiLimitMatrixEntry hp hp1 m k a φ (d:ℂ) r) ∧
      ∀ x : Coeff p, ∀ m : ℤ,
        Tendsto (fun n : ℤ => (sourcePsiOriginalFullRootJacobian hp hp1 n a φ x) m)
          (Filter.comap Int.natAbs atTop) (𝓝 ((Q x) m)) := by
  classical
  let l : Filter ℤ := Filter.comap Int.natAbs atTop
  let : NeBot l := (inferInstance : NeBot (atTop : Filter ℕ)).comap_of_surj Int.natAbs_surjective
  let T (n : ℤ) := sourcePsiOriginalFullRootJacobian hp hp1 n a φ
  obtain ⟨M,hM,hbound⟩ := H.originalFullRootJacobian_eventually_bounded φ hφW hφ a
  choose d r hr he using hD.discs
  let f (k m : ℤ) := sourcePsiLimitMatrixEntry hp hp1 m k a φ (d m:ℂ) (r m)
  have hentry (m k : ℤ) : Tendsto (fun n : ℤ => (T n (lp.single p k 1)) m) l (𝓝 (f k m)) :=
    H.originalFullRootJacobian_entry_tendsto hD φ hφW hφV hφ a ha m k (d m) (r m) (hr m) (he m)
  have hcolbound (k : ℤ) : ∀ᶠ n : ℤ in l, ‖T n (lp.single p k 1)‖ ≤ M := by
    filter_upwards [hbound] with n hn
    have hh := (T n).le_of_opNorm_le hn (lp.single p k 1)
    simpa only [lp.norm_single (zero_lt_one.trans hp1),norm_one,mul_one] using hh
  have hlim (k : ℤ) : Tendsto (fun n : ℤ => ((T n (lp.single p k 1):Coeff p):ℤ → ℂ)) l (𝓝 (f k)) :=
    tendsto_pi_nhds.mpr (fun m => hentry m k)
  have hmem (k : ℤ) : Memℓp (f k) p := by
    apply memℓp_gen'
    intro s
    exact lp.sum_rpow_le_of_tendsto hp (hcolbound k) (hlim k) s
  let v (k : ℤ) : Coeff p := ⟨f k,hmem k⟩
  obtain ⟨Q,hQ,hQcol⟩ := Coeff.exists_bounded_operator_of_entrywise_basis_limit hp l T M hM hbound v hentry
  have hentryQ (m k : ℤ) : Tendsto (fun n : ℤ => (T n (lp.single p k 1)) m) l
      (𝓝 ((Q (lp.single p k 1)) m)) := by
    simpa only [hQcol] using hentry m k
  refine ⟨Q,M,hM,hQ,hbound,?_,?_⟩
  · intro m k d' r' hr' he'
    exact tendsto_nhds_unique (hentryQ m k)
      (H.originalFullRootJacobian_entry_tendsto hD φ hφW hφV hφ a ha m k d' r' hr' he')
  · exact Coeff.tendsto_operator_coordinate_of_basis hp l T Q M hM hQ hbound hentryQ

end NLS.ZakharovShabat
