import NLS.ZakharovShabat.SourceAbelianBandTransfer

/-! # Exact signed-index normalization of the half-plane abelian integrals

The adjacent-band boundary increment removes the integer ambiguity left
by the Floquet exponential. Consecutive normalized primitives differ by
`i*pi`, and integer induction gives every signed index and every gap's
endpoint value on both complete half-planes.
-/
noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Moving the normalization gap by one adds exactly `i*pi`, with no
undetermined integer multiple of the exponential period. -/
theorem sourceAbelianHalfPlanePrimitive_succ
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (upper : Bool) :
    EqOn (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ (n+1) upper)
      (fun z => sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper z + I*(Real.pi : ℂ))
      (sourceAbelianHalfPlane upper) := by
  have hs := sourceAbelianHalfPlanePrimitive_spec hp hp1 φ hφ n upper
  obtain ⟨A,hAl,_⟩ := sourceAbelianHalfPlane_primitive_common_boundary hp hp1 φ hφ (n+1) upper
    (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper) hs.1
  have hA : A = -I*(Real.pi : ℂ) := by
    simpa only [sub_zero] using sourceAbelianHalfPlane_boundary_increment hp hp1 φ hφ n upper
      (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper) hs.1 0 A hs.2.2 hAl
  apply sourceAbelianHalfPlanePrimitive_eq_of_normalized hp hp1 φ hφ (n+1) upper _
    (fun z hz => (hs.1 z hz).add_const (I*(Real.pi : ℂ)))
  simpa only [hA,neg_mul,neg_add_cancel] using hAl.add_const (I*(Real.pi : ℂ))

/-- The full signed-index normalization on each complete half-plane. -/
theorem sourceAbelianHalfPlanePrimitive_eq_zeroIndex_add
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (upper : Bool) :
    EqOn (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper)
      (fun z => sourceAbelianHalfPlanePrimitive hp hp1 φ hφ 0 upper z + I*(Real.pi : ℂ)*n)
      (sourceAbelianHalfPlane upper) := by
  intro z hz
  dsimp only
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [sourceAbelianHalfPlanePrimitive_succ hp hp1 φ hφ k upper hz]
    dsimp only
    rw [ih]
    push_cast
    ring
  | pred k ih =>
    have h := sourceAbelianHalfPlanePrimitive_succ hp hp1 φ hφ (-(k : ℤ)-1) upper hz
    rw [sub_add_cancel,ih] at h
    push_cast at h ⊢
    linear_combination -h

/-- Compare any two normalization indices, positive or negative. -/
theorem sourceAbelianHalfPlanePrimitive_index_difference
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n m : ℤ) (upper : Bool) :
    EqOn (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper)
      (fun z => sourceAbelianHalfPlanePrimitive hp hp1 φ hφ m upper z +
        I*(Real.pi : ℂ)*(n-m : ℤ)) (sourceAbelianHalfPlane upper) := by
  intro z hz
  dsimp only
  rw [sourceAbelianHalfPlanePrimitive_eq_zeroIndex_add hp hp1 φ hφ n upper hz]
  dsimp only
  rw [sourceAbelianHalfPlanePrimitive_eq_zeroIndex_add hp hp1 φ hφ m upper hz]
  dsimp only
  push_cast
  ring

/-- Every gap has its exact boundary value from both half-planes,
including collapsed gaps and arbitrary signed normalization indices. -/
theorem sourceAbelianHalfPlanePrimitive_endpoint_limit
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n m : ℤ) (upper : Bool) (a : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m,
      canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m} : Set ℂ)) :
    Tendsto (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ n upper)
      (𝓝[sourceAbelianHalfPlane upper] a) (𝓝 (I*(Real.pi : ℂ)*(n-m : ℤ))) := by
  have hs := sourceAbelianHalfPlanePrimitive_spec hp hp1 φ hφ m upper
  have hm : Tendsto (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ m upper)
      (𝓝[sourceAbelianHalfPlane upper] a) (𝓝 0) := by
    rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using ha) with rfl | rfl
    · exact hs.2.1
    · exact hs.2.2
  have hlim : Tendsto (fun z => sourceAbelianHalfPlanePrimitive hp hp1 φ hφ m upper z +
      I*(Real.pi : ℂ)*(n-m : ℤ)) (𝓝[sourceAbelianHalfPlane upper] a)
      (𝓝 (I*(Real.pi : ℂ)*(n-m : ℤ))) := by
    simpa only [zero_add] using hm.add_const (I*(Real.pi : ℂ)*(n-m : ℤ))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (sourceAbelianHalfPlanePrimitive_index_difference hp hp1 φ hφ n m upper hz).symm

/-- Lemma 19.1(ii)'s endpoint constants for the zero-index primitive,
proved for real sources on both full half-planes. -/
theorem sourceAbelianHalfPlanePrimitive_zeroIndex_endpoint_limit
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (m : ℤ) (upper : Bool) (a : ℂ)
    (ha : a ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m,
      canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m} : Set ℂ)) :
    Tendsto (sourceAbelianHalfPlanePrimitive hp hp1 φ hφ 0 upper)
      (𝓝[sourceAbelianHalfPlane upper] a) (𝓝 (-I*(Real.pi : ℂ)*m)) := by
  simpa only [zero_sub,Int.cast_neg,mul_neg,neg_mul] using
    sourceAbelianHalfPlanePrimitive_endpoint_limit hp hp1 φ hφ 0 m upper a ha

end NLS.ZakharovShabat
