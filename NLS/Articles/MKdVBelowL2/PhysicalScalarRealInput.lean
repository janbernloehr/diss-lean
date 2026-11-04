import NLS.Articles.MKdVBelowL2.PhysicalMKdVDiagonal

/-! # Scalar real physical Fourier–Lebesgue data

The scalar is an original period-one distribution. Its equal pair belongs
to the original NLS real form exactly when its Fourier coefficients obey
the conjugate-reflection reality condition. The diagonal identification is
an isometry for the inherited physical Fourier norms.
-/
noncomputable section
set_option autoImplicit false
open Set Topology
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVBelowL2
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance scalarPeriodOnePositive : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Duplicate the same original physical distribution. -/
def physicalScalarDiagonalCLM : PhysicalFL p →L[ℝ] (PhysicalFL p × PhysicalFL p) :=
  (ContinuousLinearMap.id ℝ (PhysicalFL p)).prod (ContinuousLinearMap.id ℝ (PhysicalFL p))

/-- Real scalar distributions, with the original physical Fourier norm. -/
def physicalScalarRealSubspace (p : ℝ≥0∞) [Fact (1 ≤ p)] : Submodule ℝ (PhysicalFL p) :=
  (physicalRealSubspace p).comap physicalScalarDiagonalCLM.toLinearMap

abbrev PhysicalScalarRealInput (p : ℝ≥0∞) [Fact (1 ≤ p)] := ↥(physicalScalarRealSubspace p)

/-- Reality is the actual conjugate-reflection relation on physical modes. -/
theorem mem_physicalScalarRealSubspace_iff (u : PhysicalFL p) :
    u ∈ physicalScalarRealSubspace p ↔ ∀ n : ℤ,
      u.val (mode (-n)) = conj (u.val (mode n)) := by
  change IsRealType (CoeffPair.toMax p (physicalCoefficients (u,u))) ↔ _
  constructor <;> intro h n
  · have hn := h n
    change (physicalCoefficients (u,u)).snd n = conj ((physicalCoefficients (u,u)).fst (-n)) at hn
    simpa only [(physicalCoefficients_apply (u,u) n).2,
      (physicalCoefficients_apply (u,u) (-n)).1, neg_neg] using hn
  · change (physicalCoefficients (u,u)).snd n = conj ((physicalCoefficients (u,u)).fst (-n))
    simpa only [(physicalCoefficients_apply (u,u) n).2,
      (physicalCoefficients_apply (u,u) (-n)).1, neg_neg] using h n

theorem isClosed_physicalScalarRealSubspace :
    IsClosed (physicalScalarRealSubspace p : Set (PhysicalFL p)) :=
  isClosed_physicalRealSubspace.preimage physicalScalarDiagonalCLM.continuous

instance physicalScalarRealInputCompleteSpace : CompleteSpace (PhysicalScalarRealInput p) :=
  isClosed_physicalScalarRealSubspace.completeSpace_coe

/-- The scalar and equal-pair models have exactly the same norm. -/
def physicalScalarDiagonal : PhysicalScalarRealInput p ≃ₗᵢ[ℝ] PhysicalMKdVInput p where
  toFun u := ⟨⟨(u.val,u.val),u.property⟩,(mem_physicalMKdVSubspace_iff _).mpr rfl⟩
  invFun u := ⟨u.val.val.1,by
    change (u.val.val.1,u.val.val.1) ∈ physicalRealSubspace p
    have he : (u.val.val.1,u.val.val.1) = u.val.val :=
      Prod.ext rfl ((mem_physicalMKdVSubspace_iff u.val).mp u.property)
    rw [he]
    exact u.val.property⟩
  left_inv u := rfl
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl ((mem_physicalMKdVSubspace_iff u.val).mp u.property)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' u := by
    change ‖(u.val,u.val)‖ = ‖u.val‖
    simp only [Prod.norm_def,max_self]

@[simp] theorem physicalScalarDiagonal_fst (u : PhysicalScalarRealInput p) :
    (physicalScalarDiagonal u).val.val.1 = u.val := rfl

@[simp] theorem physicalScalarDiagonal_snd (u : PhysicalScalarRealInput p) :
    (physicalScalarDiagonal u).val.val.2 = u.val := rfl

end NLS.Articles.MKdVBelowL2
