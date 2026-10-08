import NLS.ZakharovShabat.JointDeletedSingleSpectralProducts
import NLS.SequenceSpaces.ExponentEmbedding

/-! # The summable endpoint for joint single-root products

Exponent inclusion preserves every literal cutoff and its limit. Pulling
back the Hilbert-space estimates supplies the missing p=1 endpoint.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Include the displacement exponent while retaining the spectral coordinate. -/
def singleProductExponentMap (hpq : p ≤ q) (t : ℂ × Coeff p) : ℂ × Coeff q :=
  (t.1, Coeff.exponentInclusion hpq t.2)

/-- The componentwise exponent inclusion is analytic. -/
theorem analyticAt_singleProductExponentMap (hpq : p ≤ q) (t : ℂ × Coeff p) :
    AnalyticAt ℂ (singleProductExponentMap hpq) t :=
  analyticAt_fst.prod (((Coeff.exponentInclusion hpq).analyticAt t.2).comp analyticAt_snd)

@[simp] theorem singleProductExponentMap_fst (hpq : p ≤ q) (t : ℂ × Coeff p) :
    (singleProductExponentMap hpq t).1 = t.1 := rfl

@[simp] theorem singleProductExponentMap_snd (hpq : p ≤ q) (t : ℂ × Coeff p) :
    (singleProductExponentMap hpq t).2 = Coeff.exponentInclusion hpq t.2 := rfl

@[simp] theorem displacedRoots_exponentInclusion (hpq : p ≤ q) (a : Coeff p) :
    displacedRoots (Coeff.exponentInclusion hpq a) = displacedRoots a := by
  funext n
  simp only [displacedRoots, Coeff.exponentInclusion_apply]

@[simp] theorem jointSingleSpectralProduct_exponentMap (hpq : p ≤ q) (t : ℂ × Coeff p) :
    jointSingleSpectralProduct (singleProductExponentMap hpq t) = jointSingleSpectralProduct t := by
  simp only [jointSingleSpectralProduct, singleProductExponentMap_fst,
    singleProductExponentMap_snd, displacedRoots_exponentInclusion]

@[simp] theorem jointDeletedSingleSpectralProduct_exponentMap (hpq : p ≤ q) (n : ℤ)
    (t : ℂ × Coeff p) :
    jointDeletedSingleSpectralProduct n (singleProductExponentMap hpq t) =
      jointDeletedSingleSpectralProduct n t := by
  simp only [jointDeletedSingleSpectralProduct, jointDeletedSingleSpectralPartialProduct,
    singleProductExponentMap_fst, singleProductExponentMap_snd, displacedRoots_exponentInclusion]

@[simp] theorem jointSingleSpectralPartialProduct_exponentMap (hpq : p ≤ q) (N : ℕ)
    (t : ℂ × Coeff p) :
    jointSingleSpectralPartialProduct N (singleProductExponentMap hpq t) =
      jointSingleSpectralPartialProduct N t := by
  simp only [jointSingleSpectralPartialProduct, singleProductExponentMap_fst,
    singleProductExponentMap_snd, displacedRoots_exponentInclusion]

@[simp] theorem jointDeletedSingleSpectralPartialProduct_exponentMap (hpq : p ≤ q) (n : ℤ) (N : ℕ)
    (t : ℂ × Coeff p) :
    jointDeletedSingleSpectralPartialProduct n N (singleProductExponentMap hpq t) =
      jointDeletedSingleSpectralPartialProduct n N t := by
  simp only [jointDeletedSingleSpectralPartialProduct, singleProductExponentMap_fst,
    singleProductExponentMap_snd, displacedRoots_exponentInclusion]

omit [Fact (1 ≤ p)] in
private theorem max_two_ne_top (hp : p ≠ ⊤) : max p 2 ≠ ⊤ :=
  (max_lt hp.lt_top (by norm_num)).ne

omit [Fact (1 ≤ p)] in
private theorem one_lt_max_two : 1 < max p (2:ℝ≥0∞) :=
  lt_of_lt_of_le (by norm_num) (le_max_right _ _)

local instance : Fact (1 ≤ max p (2:ℝ≥0∞)) := ⟨one_lt_max_two.le⟩

/-- Full cutoff convergence on bounded displacement families includes p=1. -/
theorem tendstoUniformlyOn_jointSingleSpectralProduct_finite (hp : p ≠ ⊤)
    (K : Set ℂ) (hK : IsCompact K) (S : Set (Coeff p))
    (R : ℝ) (hR : 0 ≤ R) (hb : ∀ a ∈ S, ‖a‖ ≤ R) :
    TendstoUniformlyOn (jointSingleSpectralPartialProduct (p := p))
      (jointSingleSpectralProduct (p := p)) atTop (K ×ˢ S) := by
  let hpq := le_max_left p (2:ℝ≥0∞)
  have h := tendstoUniformlyOn_jointSingleSpectralProduct (max_two_ne_top hp) one_lt_max_two
    K hK (Coeff.exponentInclusion hpq '' S) R hR (by
      rintro _ ⟨a,ha,rfl⟩
      exact (Coeff.norm_exponentInclusion_le hpq a).trans (hb a ha))
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with N hN t ht
  have ht' : singleProductExponentMap hpq t ∈ K ×ˢ (Coeff.exponentInclusion hpq '' S) :=
    ⟨ht.1, ⟨t.2, ht.2, rfl⟩⟩
  simpa only [jointSingleSpectralProduct_exponentMap,
    jointSingleSpectralPartialProduct_exponentMap] using hN (singleProductExponentMap hpq t) ht'

/-- Deleted cutoff convergence on bounded displacement families includes p=1. -/
theorem tendstoUniformlyOn_jointDeletedSingleSpectralProduct_finite (hp : p ≠ ⊤) (n : ℤ)
    (K : Set ℂ) (hK : IsCompact K) (S : Set (Coeff p))
    (R : ℝ) (hR : 0 ≤ R) (hb : ∀ a ∈ S, ‖a‖ ≤ R) :
    TendstoUniformlyOn (jointDeletedSingleSpectralPartialProduct (p := p) n)
      (jointDeletedSingleSpectralProduct n) atTop (K ×ˢ S) := by
  let hpq := le_max_left p (2:ℝ≥0∞)
  have h := tendstoUniformlyOn_jointDeletedSingleSpectralProduct (max_two_ne_top hp) one_lt_max_two
    n K hK (Coeff.exponentInclusion hpq '' S) R hR (by
      rintro _ ⟨a,ha,rfl⟩
      exact (Coeff.norm_exponentInclusion_le hpq a).trans (hb a ha))
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with N hN t ht
  have ht' : singleProductExponentMap hpq t ∈ K ×ˢ (Coeff.exponentInclusion hpq '' S) :=
    ⟨ht.1, ⟨t.2, ht.2, rfl⟩⟩
  simpa only [jointDeletedSingleSpectralProduct_exponentMap,
    jointDeletedSingleSpectralPartialProduct_exponentMap] using hN (singleProductExponentMap hpq t) ht'

/-- Joint analyticity of the full product throughout every finite Banach exponent. -/
theorem analyticOnNhd_jointSingleSpectralProduct_finite (hp : p ≠ ⊤) :
    AnalyticOnNhd ℂ (jointSingleSpectralProduct (p := p)) univ := by
  let hpq := le_max_left p (2:ℝ≥0∞)
  intro t _
  have h : AnalyticAt ℂ (jointSingleSpectralProduct ∘ singleProductExponentMap hpq) t :=
    ((analyticOnNhd_jointSingleSpectralProduct (max_two_ne_top hp) one_lt_max_two)
      (singleProductExponentMap hpq t) (mem_univ _)).comp
        (analyticAt_singleProductExponentMap hpq t)
  simpa only [Function.comp_def, jointSingleSpectralProduct_exponentMap] using h

/-- Joint analyticity after deleting any root, also at p=1. -/
theorem analyticOnNhd_jointDeletedSingleSpectralProduct_finite (hp : p ≠ ⊤) (n : ℤ) :
    AnalyticOnNhd ℂ (jointDeletedSingleSpectralProduct (p := p) n) univ := by
  let hpq := le_max_left p (2:ℝ≥0∞)
  intro t _
  have h : AnalyticAt ℂ (jointDeletedSingleSpectralProduct n ∘ singleProductExponentMap hpq) t :=
    ((analyticOnNhd_jointDeletedSingleSpectralProduct (max_two_ne_top hp) one_lt_max_two n)
      (singleProductExponentMap hpq t) (mem_univ _)).comp
        (analyticAt_singleProductExponentMap hpq t)
  simpa only [Function.comp_def, jointDeletedSingleSpectralProduct_exponentMap] using h

/-- Restoring a deleted root is valid even at the summable endpoint. -/
theorem jointSingleSpectralProduct_eq_deleted_finite (hp : p ≠ ⊤) (n : ℤ) (t : ℂ × Coeff p) :
    jointSingleSpectralProduct t =
      2*(displacedRoots t.2 n-t.1)*jointDeletedSingleSpectralProduct n t := by
  let hpq := le_max_left p (2:ℝ≥0∞)
  have h := jointSingleSpectralProduct_eq_deleted (max_two_ne_top hp) one_lt_max_two n
    (singleProductExponentMap hpq t)
  simpa only [jointSingleSpectralProduct_exponentMap, jointDeletedSingleSpectralProduct_exponentMap,
    singleProductExponentMap_fst, singleProductExponentMap_snd, displacedRoots_exponentInclusion]
    using h

end NLS.ZakharovShabat
