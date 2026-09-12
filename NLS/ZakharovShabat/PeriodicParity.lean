import NLS.SequenceSpaces.Parity
import NLS.ZakharovShabat.ResolventContour

/-!
# Periodic and antiperiodic Fourier subspaces

In the period-two coefficient convention, even frequencies encode period-one
functions and odd frequencies encode period-one antiperiodic functions. We
construct their closed complementary subspaces and prove Lemma 3.6 for potentials
supported on even frequencies. The operator, full resolvent, and spectral circle
projections preserve both spaces. The physical Fourier realization remains separate.
-/

open scoped ENNReal
noncomputable section

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Project both components onto the indicated Fourier parity. -/
def pairParityProjection (r : ℤ) : PairSpace p →L[ℂ] PairSpace p :=
  (Coeff.parityProjection r).prodMap (Coeff.parityProjection r)

@[simp] theorem pairParityProjection_apply (r : ℤ) (a : PairSpace p) :
    pairParityProjection r a = (Coeff.parityProjection r a.1, Coeff.parityProjection r a.2) := rfl

/-- The coefficient versions of `FL_per+` (`r=0`) and `FL_per-` (`r=1`). -/
def pairParitySubspace (r : ℤ) : Submodule ℂ (PairSpace p) :=
  (Coeff.paritySubspace r).prod (Coeff.paritySubspace r)

@[simp] theorem mem_pairParitySubspace (r : ℤ) (a : PairSpace p) :
    a ∈ pairParitySubspace r ↔ a.1 ∈ Coeff.paritySubspace r ∧ a.2 ∈ Coeff.paritySubspace r := Iff.rfl

theorem pairParityProjection_eq_self_iff (r : ℤ) (a : PairSpace p) :
    pairParityProjection r a = a ↔ a ∈ pairParitySubspace r := by
  rcases a with ⟨a₀, a₁⟩
  simp only [pairParityProjection_apply, Prod.mk.injEq, Coeff.parityProjection_eq_self_iff,
    mem_pairParitySubspace]

theorem isClosed_pairParitySubspace (r : ℤ) :
    IsClosed (pairParitySubspace (p := p) r : Set (PairSpace p)) :=
  (Coeff.isClosed_paritySubspace r).prod (Coeff.isClosed_paritySubspace r)

theorem pairParityProjection_mem (r : ℤ) (a : PairSpace p) :
    pairParityProjection r a ∈ pairParitySubspace r :=
  ⟨Coeff.parityProjection_mem r a.1, Coeff.parityProjection_mem r a.2⟩

theorem norm_pairParityProjection_apply_le (r : ℤ) (a : PairSpace p) :
    ‖pairParityProjection r a‖ ≤ ‖a‖ :=
  max_le_max (Coeff.norm_parityProjection_apply_le r a.1) (Coeff.norm_parityProjection_apply_le r a.2)

theorem pairParityProjection_zero_add_one (a : PairSpace p) :
    pairParityProjection 0 a + pairParityProjection 1 a = a :=
  Prod.ext (Coeff.parityProjection_zero_add_one a.1) (Coeff.parityProjection_zero_add_one a.2)

theorem isCompl_pairParitySubspaces :
    IsCompl (pairParitySubspace (p := p) 0) (pairParitySubspace 1) := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro a ha0 ha1
    exact Prod.ext
      ((Submodule.disjoint_def.mp Coeff.isCompl_paritySubspaces.disjoint) _ ha0.1 ha1.1)
      ((Submodule.disjoint_def.mp Coeff.isCompl_paritySubspaces.disjoint) _ ha0.2 ha1.2)
  · rw [codisjoint_iff_le_sup]
    intro a _
    exact Submodule.mem_sup.mpr ⟨pairParityProjection 0 a, pairParityProjection_mem 0 a,
      pairParityProjection 1 a, pairParityProjection_mem 1 a, pairParityProjection_zero_add_one a⟩

/-- The parity projection preserves the one-derivative domain. -/
def domainParityProjection (r : ℤ) : Domain p →L[ℂ] Domain p :=
  (WeightedCoeff.parityProjection (Weight.sobolev 1) r).prodMap
    (WeightedCoeff.parityProjection (Weight.sobolev 1) r)

/-- The parity subspace in the operator domain. -/
def domainParitySubspace (r : ℤ) : Submodule ℂ (Domain p) where
  carrier := {f | ∀ n : ℤ, n % 2 ≠ r % 2 → f.1.val n = 0 ∧ f.2.val n = 0}
  zero_mem' := by intro n _; exact ⟨rfl, rfl⟩
  add_mem' := by
    intro f g hf hg n hn
    constructor
    · change f.1.val n + g.1.val n = 0
      rw [(hf n hn).1, (hg n hn).1, add_zero]
    · change f.2.val n + g.2.val n = 0
      rw [(hf n hn).2, (hg n hn).2, add_zero]
  smul_mem' := by
    intro c f hf n hn
    constructor
    · change c * f.1.val n = 0
      rw [(hf n hn).1, mul_zero]
    · change c * f.2.val n = 0
      rw [(hf n hn).2, mul_zero]

@[simp] theorem mem_domainParitySubspace (r : ℤ) (f : Domain p) :
    f ∈ domainParitySubspace r ↔ domainInclusion f ∈ pairParitySubspace r := by
  rw [mem_pairParitySubspace, Coeff.mem_paritySubspace, Coeff.mem_paritySubspace]
  simp only [domainInclusion_apply, scalarInclusion_apply]
  constructor
  · intro hf
    exact ⟨fun n hn => (hf n hn).1, fun n hn => (hf n hn).2⟩
  · rintro ⟨h₀, h₁⟩ n hn
    exact ⟨h₀ n hn, h₁ n hn⟩

theorem domainInclusion_domainParityProjection (r : ℤ) (f : Domain p) :
    domainInclusion (domainParityProjection r f) = pairParityProjection r (domainInclusion f) := by
  apply Prod.ext <;> ext n <;>
    simp [domainParityProjection, pairParityProjection]

theorem domainParityProjection_eq_self_iff (r : ℤ) (f : Domain p) :
    domainParityProjection r f = f ↔ f ∈ domainParitySubspace r := by
  rw [mem_domainParitySubspace, ← pairParityProjection_eq_self_iff,
    ← domainInclusion_domainParityProjection]
  exact domainInclusion_injective.eq_iff.symm

theorem isClosed_domainParitySubspace (r : ℤ) :
    IsClosed (domainParitySubspace (p := p) r : Set (Domain p)) := by
  convert (isClosed_eq (domainParityProjection (p := p) r).continuous continuous_id) using 1
  ext f
  exact (domainParityProjection_eq_self_iff r f).symm

theorem freeOperator_domainParityProjection (r : ℤ) (f : Domain p) :
    freeOperator (domainParityProjection r f) = pairParityProjection r (freeOperator f) := by
  apply Prod.ext <;> ext n <;>
    by_cases hn : n % 2 = r % 2 <;> simp [domainParityProjection, pairParityProjection, hn]

private theorem potentialMul_parityProjection (hp : p ≠ ⊤) (φ : Coeff p)
    (hφ : φ ∈ Coeff.paritySubspace 0) (r : ℤ) (f : ScalarDomain p) :
    potentialMul hp φ (WeightedCoeff.parityProjection (Weight.sobolev 1) r f) =
      Coeff.parityProjection r (potentialMul hp φ f) := by
  have he : WeightedCoeff.sobolevToL1CLM p hp (WeightedCoeff.parityProjection (Weight.sobolev 1) r f) =
      Coeff.parityProjection r (WeightedCoeff.sobolevToL1CLM p hp f) := by
    ext n
    simp
  change Coeff.convolution φ (WeightedCoeff.sobolevToL1CLM p hp
    (WeightedCoeff.parityProjection (Weight.sobolev 1) r f)) = _
  rw [he, Coeff.convolution_parityProjection φ hφ]
  rfl

/-- Even potential coefficients preserve each Fourier parity under multiplication. -/
theorem potentialOperator_domainParityProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (f : Domain p) :
    potentialOperator hp φ (domainParityProjection r f) =
      pairParityProjection r (potentialOperator hp φ f) :=
  Prod.ext (potentialMul_parityProjection hp φ.1 hφ.1 r f.2)
    (potentialMul_parityProjection hp φ.2 hφ.2 r f.1)

/-- Lemma 3.6 as an intertwining identity between the domain and base projections. -/
theorem operator_domainParityProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (f : Domain p) :
    operator hp φ (domainParityProjection r f) = pairParityProjection r (operator hp φ f) := by
  change freeOperator (domainParityProjection r f) + potentialOperator hp φ (domainParityProjection r f) =
    pairParityProjection r (freeOperator f + potentialOperator hp φ f)
  rw [freeOperator_domainParityProjection, potentialOperator_domainParityProjection hp φ hφ, map_add]

/-- Chapter 1, Lemma 3.6: the operator preserves both parity subspaces for even potentials. -/
theorem operator_mem_pairParitySubspace (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (f : Domain p) (hf : f ∈ domainParitySubspace r) :
    operator hp φ f ∈ pairParitySubspace r := by
  rw [← pairParityProjection_eq_self_iff, ← operator_domainParityProjection hp φ hφ,
    (domainParityProjection_eq_self_iff r f).mpr hf]

/-- The spectral pencil has the same parity intertwining identity. -/
theorem spectralPencil_domainParityProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (z : ℂ) (f : Domain p) :
    spectralPencil hp φ z (domainParityProjection r f) =
      pairParityProjection r (spectralPencil hp φ z f) := by
  simp only [spectralPencil_apply, domainInclusion_domainParityProjection,
    operator_domainParityProjection hp φ hφ, map_sub, map_smul]

/-- Inversion preserves the parity identity into the full operator domain. -/
theorem resolventToDomain_parityProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (z : ℂ) (hz : z ∈ resolventSet hp φ)
    (a : PairSpace p) :
    resolventToDomain hp φ z (pairParityProjection r a) =
      domainParityProjection r (resolventToDomain hp φ z a) := by
  apply hz.injective
  rw [spectralPencil_resolventToDomain hp φ z hz, spectralPencil_domainParityProjection hp φ hφ,
    spectralPencil_resolventToDomain hp φ z hz]

theorem resolventToDomain_mem_domainParitySubspace (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (z : ℂ) (hz : z ∈ resolventSet hp φ)
    (a : PairSpace p) (ha : a ∈ pairParitySubspace r) :
    resolventToDomain hp φ z a ∈ domainParitySubspace r := by
  rw [← domainParityProjection_eq_self_iff, ← resolventToDomain_parityProjection hp φ hφ r z hz,
    (pairParityProjection_eq_self_iff r a).mpr ha]

/-- Both base-space parity projections commute with every resolvent of an even potential. -/
theorem pairParityProjection_commute_resolvent (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (z : ℂ) (hz : z ∈ resolventSet hp φ) :
    Commute (pairParityProjection r) (resolvent hp φ z) := by
  apply ContinuousLinearMap.ext
  intro a
  change pairParityProjection r (domainInclusion (resolventToDomain hp φ z a)) =
    domainInclusion (resolventToDomain hp φ z (pairParityProjection r a))
  rw [← domainInclusion_domainParityProjection, resolventToDomain_parityProjection hp φ hφ r z hz]

theorem resolvent_mem_pairParitySubspace (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (z : ℂ) (hz : z ∈ resolventSet hp φ)
    (a : PairSpace p) (ha : a ∈ pairParitySubspace r) :
    resolvent hp φ z a ∈ pairParitySubspace r := by
  rw [← pairParityProjection_eq_self_iff]
  have h := congrArg (fun T : PairSpace p →L[ℂ] PairSpace p => T a)
    (pairParityProjection_commute_resolvent hp φ hφ r z hz).eq
  change pairParityProjection r (resolvent hp φ z a) = resolvent hp φ z (pairParityProjection r a) at h
  rw [h, (pairParityProjection_eq_self_iff r a).mpr ha]

/-- Parity projections also commute with the spectral circle projectors in (1.4). -/
theorem pairParityProjection_commute_contour (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hc : Metric.sphere c R ⊆ resolventSet hp φ) :
    Commute (pairParityProjection r) (resolventCircleIntegral hp φ c R) :=
  commute_resolventCircleIntegral hp φ c R hR hc _
    (fun z hz => pairParityProjection_commute_resolvent hp φ hφ r z (hc hz))

theorem resolventCircleIntegral_mem_pairParitySubspace (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hc : Metric.sphere c R ⊆ resolventSet hp φ) (a : PairSpace p) (ha : a ∈ pairParitySubspace r) :
    resolventCircleIntegral hp φ c R a ∈ pairParitySubspace r := by
  rw [← pairParityProjection_eq_self_iff]
  have h := congrArg (fun T : PairSpace p →L[ℂ] PairSpace p => T a)
    (pairParityProjection_commute_contour hp φ hφ r c R hR hc).eq
  change pairParityProjection r (resolventCircleIntegral hp φ c R a) =
    resolventCircleIntegral hp φ c R (pairParityProjection r a) at h
  rw [h, (pairParityProjection_eq_self_iff r a).mpr ha]

omit [Fact (1 ≤ p)] in
/-- The signed negative free mode has the parity of its spectral index. -/
theorem negativeMode_mem_domainParitySubspace (n : ℤ) :
    negativeMode (p := p) n ∈ domainParitySubspace n := by
  intro k hk
  have hkn : k ≠ -n := by intro h; subst k; omega
  simp [negativeMode, hkn]

omit [Fact (1 ≤ p)] in
/-- The signed positive free mode has the parity of its spectral index. -/
theorem positiveMode_mem_domainParitySubspace (n : ℤ) :
    positiveMode (p := p) n ∈ domainParitySubspace n := by
  intro k hk
  have hkn : k ≠ n := by intro h; subst k; exact hk rfl
  simp [positiveMode, hkn]

end NLS.ZakharovShabat
