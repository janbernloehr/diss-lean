import Mathlib.Data.Sign.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Literal signs with the topology of a real two-sided sheet

An admissible signed point consists of a base coordinate and a sign,
with zero sign precisely where the sheet height vanishes. Reconstruction
uses the nonnegative square root of the sheet function. The topology is
induced by that full real pair, so both signs join at sheet zeros.
-/
noncomputable section
open Set Topology
namespace NLS.FunctionalAnalysis

/-- Literal base/sign data on a real sheet, including its zero-height points. -/
@[ext] structure RealSignedSheet (G : ℝ → ℝ) (a b : ℝ) where
  base : ℝ
  sign : SignType
  base_mem : base ∈ Icc a b
  height_nonneg : 0 ≤ G base
  sign_zero_iff : sign = 0 ↔ G base = 0

namespace RealSignedSheet
variable {G : ℝ → ℝ} {a b : ℝ}

/-- Reconstruct the full terminal coordinate from its literal sign. -/
def value (q : RealSignedSheet G a b) : ℝ × ℝ :=
  (q.base,(q.sign : ℝ)*Real.sqrt (G q.base))

theorem value_sq (q : RealSignedSheet G a b) : (q.value.2)^2 = G q.base := by
  by_cases hs : q.sign = 0
  · simp [value,hs,q.sign_zero_iff.mp hs]
  · have hsign : (q.sign : ℝ)^2 = 1 := by
      cases he : q.sign <;> simp_all
    simp only [value,mul_pow,hsign,one_mul,Real.sq_sqrt q.height_nonneg]

theorem sign_value (q : RealSignedSheet G a b) : SignType.sign q.value.2 = q.sign := by
  by_cases hs : q.sign = 0
  · simp [value,hs]
  · have hpos : 0 < G q.base := lt_of_le_of_ne q.height_nonneg
      (fun h => hs (q.sign_zero_iff.mpr h.symm))
    have hsqrt : SignType.sign (Real.sqrt (G q.base)) = 1 :=
      sign_eq_one_iff.mpr (Real.sqrt_pos.mpr hpos)
    simp only [value,sign_mul,hsqrt,mul_one]
    cases q.sign <;> simp

/-- The topology is induced by the reconstructed pair, not the discrete sign coordinate. -/
instance : TopologicalSpace (RealSignedSheet G a b) :=
  TopologicalSpace.induced value inferInstance

/-- The literal signed points and the full real sheet are equivalent, including every zero. -/
def equivSheet : RealSignedSheet G a b ≃ {z : ℝ × ℝ | z.1 ∈ Icc a b ∧ z.2^2 = G z.1} where
  toFun q := ⟨q.value,q.base_mem,q.value_sq⟩
  invFun z := {
    base := z.val.1
    sign := SignType.sign z.val.2
    base_mem := z.property.1
    height_nonneg := z.property.2 ▸ sq_nonneg z.val.2
    sign_zero_iff := by rw [sign_eq_zero_iff,← z.property.2,sq_eq_zero_iff] }
  left_inv q := by
    apply RealSignedSheet.ext
    · rfl
    · exact q.sign_value
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change SignType.sign z.val.2 * Real.sqrt (G z.val.1) = z.val.2
      rw [← z.property.2,Real.sqrt_sq_eq_abs,sign_mul_abs]

/-- The induced topology gives precisely the full sheet topology in real coordinates. -/
def homeomorphSheet : RealSignedSheet G a b ≃ₜ
    {z : ℝ × ℝ | z.1 ∈ Icc a b ∧ z.2^2 = G z.1} where
  toEquiv := equivSheet
  continuous_toFun := continuous_induced_dom.subtype_mk _
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    have he : (value ∘ equivSheet.symm) = (Subtype.val : {z : ℝ × ℝ | z.1 ∈ Icc a b ∧ z.2^2 = G z.1} → ℝ × ℝ) := by
      funext z
      exact congrArg Subtype.val (equivSheet.apply_symm_apply z)
    change Continuous (value ∘ equivSheet.symm)
    rw [he]
    exact continuous_subtype_val

/-- The signed reconstruction is injective; the zero-sign convention is essential here. -/
theorem value_injective : Function.Injective (value : RealSignedSheet G a b → ℝ × ℝ) := by
  intro q r h
  exact equivSheet.injective (Subtype.ext h)

instance : T2Space (RealSignedSheet G a b) := homeomorphSheet.symm.t2Space

private def branchSign (s : Bool) : ℝ := if s then 1 else -1

private theorem branchSign_sq (s : Bool) : (branchSign s)^2 = 1 := by
  cases s <;> norm_num [branchSign]

/-- Two copies of the base interval map onto the signed sheet by square-root branches. -/
def branchMap (hG : ∀ x ∈ Icc a b, 0 ≤ G x)
    (d : Icc a b × Bool) : RealSignedSheet G a b :=
  equivSheet.symm ⟨(d.1.val,branchSign d.2 * Real.sqrt (G d.1.val)),d.1.property,by
    rw [mul_pow,branchSign_sq,one_mul,Real.sq_sqrt (hG d.1.val d.1.property)]⟩

@[simp] theorem value_branchMap (hG : ∀ x ∈ Icc a b, 0 ≤ G x) (d : Icc a b × Bool) :
    (branchMap hG d).value = (d.1.val,branchSign d.2 * Real.sqrt (G d.1.val)) :=
  congrArg Subtype.val (equivSheet.apply_symm_apply _)

theorem continuous_branchMap (hG : ∀ x ∈ Icc a b, 0 ≤ G x) (hc : Continuous G) :
    Continuous (branchMap hG) := by
  apply continuous_induced_rng.mpr
  have hx : Continuous (fun d : Icc a b × Bool => d.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hs : Continuous (fun d : Icc a b × Bool => branchSign d.2) :=
    (continuous_of_discreteTopology (f := branchSign)).comp continuous_snd
  simpa only [Function.comp_def,Pi.mul_apply,value_branchMap] using
    hx.prodMk (hs.mul (Real.continuous_sqrt.comp (hc.comp hx)))

theorem branchMap_surjective (hG : ∀ x ∈ Icc a b, 0 ≤ G x) :
    Function.Surjective (branchMap hG) := by
  intro q
  have hex : ∃ s : Bool, branchSign s * Real.sqrt (G q.base) = q.value.2 := by
    cases hs : q.sign with
    | zero =>
      refine ⟨true,?_⟩
      have hz : G q.base = 0 := q.sign_zero_iff.mp hs
      simp [value,branchSign,hs,hz]
    | neg => exact ⟨false,by simp [value,branchSign,hs]⟩
    | pos => exact ⟨true,by simp [value,branchSign,hs]⟩
  obtain ⟨s,hs⟩ := hex
  refine ⟨(⟨q.base,q.base_mem⟩,s),?_⟩
  apply value_injective
  rw [value_branchMap]
  exact Prod.ext rfl hs

/-- For continuous nonnegative sheet functions, the topology is the quotient
of two copies of the compact base interval by their coincident zero-height points. -/
theorem isQuotientMap_branchMap (hG : ∀ x ∈ Icc a b, 0 ≤ G x) (hc : Continuous G) :
    IsQuotientMap (branchMap hG) := by
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  have h := continuous_branchMap hG hc
  exact h.isClosedMap.isQuotientMap h (branchMap_surjective hG)

/-- The two branches over a fixed base point are identified precisely at zero height. -/
theorem branchMap_true_eq_false_iff (hG : ∀ x ∈ Icc a b, 0 ≤ G x) (x : Icc a b) :
    branchMap hG (x,true) = branchMap hG (x,false) ↔ G x.val = 0 := by
  constructor
  · intro he
    have hv := congrArg (fun q : RealSignedSheet G a b => q.value.2) he
    simp [branchSign] at hv
    have hs := Real.sq_sqrt (hG x.val x.property)
    nlinarith [Real.sqrt_nonneg (G x.val)]
  · intro he
    apply value_injective
    simp [value_branchMap,he]

end RealSignedSheet
end NLS.FunctionalAnalysis
