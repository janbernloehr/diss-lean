import NLS.SequenceSpaces.PeriodOneHminusOneDensity

/-! # Real Fourier density in the full unit-period H^-1 space

Reality means conjugate reflection of the raw Fourier coefficients.
Symmetric finite truncations preserve it and converge in the H^-1 norm.
The dense approximants belong to the actual unit-period L2 space.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal ComplexConjugate Classical
namespace NLS

/-- Distributional reality in the unit-period Fourier convention. -/
def IsRealPeriodOneHminusOne (q : PeriodOneHminusOne) : Prop :=
  ∀ k : ℤ, q.val (-k) = conj (q.val k)

abbrev PeriodOneRealHminusOne := {q : PeriodOneHminusOne // IsRealPeriodOneHminusOne q}
abbrev PeriodOneRealL2 := {q : Coeff 2 // ∀ k : ℤ, q (-k) = conj (q k)}

theorem IsRealPeriodOneHminusOne.smul_real {q : PeriodOneHminusOne}
    (hq : IsRealPeriodOneHminusOne q) (s : ℝ) : IsRealPeriodOneHminusOne ((s : ℂ) • q) := by
  intro k
  simp only [WeightedCoeff.smul_val,map_mul,Complex.conj_ofReal,hq k]

/-- The physical L2 inclusion restricted to the original real Fourier subspaces. -/
def periodOneRealL2Inclusion (a : PeriodOneRealL2) : PeriodOneRealHminusOne :=
  ⟨periodOneL2Inclusion a.val,fun k => by simpa only [periodOneL2Inclusion_apply] using a.property k⟩

/-- A finite raw truncation has a literal L2 representative, without
rescaling its Fourier coefficients. -/
def periodOneFiniteL2Approx (q : PeriodOneHminusOne) (S : Finset ℤ) : Coeff 2 :=
  Coeff.ofFinsupp (Finsupp.onFinset S (WeightedCoeff.truncate (Weight.sobolev (-1)) 2 S q).val
    (by intro k hk; by_contra h; exact hk (by simp [h])))

@[simp] theorem periodOneFiniteL2Approx_apply (q : PeriodOneHminusOne) (S : Finset ℤ) (k : ℤ) :
    periodOneFiniteL2Approx q S k = if k ∈ S then q.val k else 0 := by
  simp [periodOneFiniteL2Approx,Coeff.ofFinsupp_apply]

theorem periodOneL2Inclusion_finiteApprox (q : PeriodOneHminusOne) (S : Finset ℤ) :
    periodOneL2Inclusion (periodOneFiniteL2Approx q S) =
      WeightedCoeff.truncate (Weight.sobolev (-1)) 2 S q := by
  apply Subtype.ext
  funext k
  simp

/-- Add the reflected support without dropping any original index. -/
def periodOneSymmetricSupport (S : Finset ℤ) : Finset ℤ := S ∪ S.image (fun k => -k)

@[simp] theorem mem_periodOneSymmetricSupport_neg (S : Finset ℤ) (k : ℤ) :
    -k ∈ periodOneSymmetricSupport S ↔ k ∈ periodOneSymmetricSupport S := by
  simp only [periodOneSymmetricSupport,Finset.mem_union,Finset.mem_image]
  constructor
  · rintro (hk | ⟨j,hj,he⟩)
    · exact Or.inr ⟨-k,hk,neg_neg k⟩
    · left
      have hkj : k = j := by omega
      simpa only [hkj] using hj
  · rintro (hk | ⟨j,hj,he⟩)
    · exact Or.inr ⟨k,hk,rfl⟩
    · left
      have hkj : -k = j := by omega
      simpa only [hkj] using hj

theorem tendsto_periodOneSymmetricSupport :
    Tendsto periodOneSymmetricSupport atTop atTop := by
  apply tendsto_atTop.2
  intro S
  filter_upwards [eventually_ge_atTop S] with T hST
  exact hST.trans Finset.subset_union_left

theorem periodOneFiniteL2Approx_real (q : PeriodOneRealHminusOne) (S : Finset ℤ) :
    ∀ k : ℤ, periodOneFiniteL2Approx q.val (periodOneSymmetricSupport S) (-k) =
      conj (periodOneFiniteL2Approx q.val (periodOneSymmetricSupport S) k) := by
  intro k
  by_cases hk : k ∈ periodOneSymmetricSupport S <;>
    simp [hk,q.property k]

/-- Real finite L2 potentials are dense in every real H^-1 potential.
No bounded L2 norm or extra regularity is required of the approximants. -/
theorem denseRange_periodOneRealL2Inclusion : DenseRange periodOneRealL2Inclusion := by
  intro q
  let a : Finset ℤ → PeriodOneRealL2 := fun S =>
    ⟨periodOneFiniteL2Approx q.val (periodOneSymmetricSupport S),periodOneFiniteL2Approx_real q S⟩
  have ht : Tendsto (fun S => periodOneRealL2Inclusion (a S)) atTop (𝓝 q) := by
    apply tendsto_subtype_rng.mpr
    have hh := (WeightedCoeff.tendsto_truncate (Weight.sobolev (-1)) 2 (by simp) q.val).comp
      tendsto_periodOneSymmetricSupport
    simpa only [periodOneRealL2Inclusion,a,periodOneL2Inclusion_finiteApprox,Function.comp_def] using hh
  exact mem_closure_of_tendsto ht (Eventually.of_forall (fun S => mem_range_self (a S)))

end NLS
