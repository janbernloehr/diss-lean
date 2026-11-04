import NLS.Articles.MKdVBelowL2.FourthMomentSummability
import NLS.ZakharovShabat.SourceAbelianMomentOnePlusDomain

/-! # Absolute H₄ moment sums at every finite exponent

For p > 3, multiply the cubic gap in ℓ^(p/3) by the actual sharp row in
its conjugate exponent. This removes the earlier p ≤ 3 restriction.
The result concerns the candidate moment sum; physical H₄ identification
and analyticity of the infinite sum remain separate obligations.
-/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The index ratio is bounded, so a summable cubic-gap product suffices. -/
theorem summable_weighted_moment_of_product
    {q : ℝ≥0∞} (A : SourceAbelianMomentAtlas hp hp1 W s)
    (ψ : CoeffPair p) (n : ℤ) (a : Coeff q) (b : Coeff 1)
    (hb : ∀ k, b k = (sourcePeriodicGapDisplacement hp hp1 ψ k)^3*a k)
    (hrow : ∀ k : ℤ, k ≠ n → A.moment n k 2 ψ =
      (sourcePeriodicGapDisplacement hp hp1 ψ k)^3/((n-k:ℤ):ℂ)*a k) :
    Summable (fun k : ℤ => ‖(k:ℂ)*A.moment n k 2 ψ‖) := by
  have hs : Summable (fun k => (|(n:ℝ)|+1)*‖b k‖) :=
    b.property.norm.summable_of_one.mul_left _
  have hbound (k : ℤ) (hk : k ≠ n) :
      ‖(k:ℂ)*A.moment n k 2 ψ‖ ≤ (|(n:ℝ)|+1)*‖b k‖ := by
    rw [hrow k hk]
    have he : (k:ℂ)*((sourcePeriodicGapDisplacement hp hp1 ψ k)^3/((n-k:ℤ):ℂ)*a k) =
        ((k:ℂ)/((n-k:ℤ):ℂ))*b k := by rw [hb k]; ring
    rw [he,norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_index_ratio_le n k hk) (norm_nonneg _)
  have hu : Summable (fun k : {k : ℤ // k ≠ n} => ‖(k.val:ℂ)*A.moment n k.val 2 ψ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hbound k.val k.property)
      (hs.subtype (fun k => k ≠ n))
  exact (Set.finite_singleton n).summable_compl_iff.mp hu

/-- For p > 3 the sharp row exponent is dual to the cubic gap exponent. -/
theorem summable_weighted_moment_of_sharp_row
    (A : SourceAbelianMomentAtlas hp hp1 W s) (hp3 : 3 < p)
    (ψ : CoeffPair p) (n : ℤ) (a : Coeff (p/3).conjExponent)
    (hrow : ∀ k : ℤ, k ≠ n → A.moment n k 2 ψ =
      (sourcePeriodicGapDisplacement hp hp1 ψ k)^3/((n-k:ℤ):ℂ)*a k) :
    Summable (fun k : ℤ => ‖(k:ℂ)*A.moment n k 2 ψ‖) := by
  have hr : p/3 ≠ ⊤ := by rw [← Coeff.thirdExponent_eq_div hp]; exact ENNReal.ofReal_ne_top
  have hr1 : 1 < p/3 := by
    exact (ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr (by simpa using hp3)
  let : Fact (1 ≤ p/3) := ⟨hr1.le⟩
  obtain ⟨g,hg,_⟩ := Coeff.exists_refined_triple_product hp (zero_lt_one.trans hp1) hr
    (zero_lt_one.trans hr1) (by rw [Coeff.thirdExponent_eq_div hp])
    (sourcePeriodicGapDisplacement hp hp1 ψ) (sourcePeriodicGapDisplacement hp hp1 ψ)
    (sourcePeriodicGapDisplacement hp hp1 ψ)
  let b := Coeff.quasiHolderProduct (r := 1) g a
  apply summable_weighted_moment_of_product A ψ n a b _ hrow
  intro k
  simp only [b,Coeff.quasiHolderProduct_apply,hg k]
  ring

/-- Construct a convergent actual moment atlas for every finite p > 1.
For p > 3 all inputs of the sharp root comparison are constructed together. -/
theorem exists_fourthMoment_summableAtlas (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W V : Set (CoeffPair p), IsOpen V ∧ realTypeSourceLocus p ⊆ V ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiSquaredGapComplexExtension hp hp1 V s ∧
        ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
        ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
          U ⊆ A.domain ∩ V ∧ ∀ ψ ∈ U, ∀ n : ℤ,
            Summable (fun k : ℤ => ‖(k:ℂ)*A.moment n k 2 ψ‖) := by
  by_cases hp3 : p ≤ 3
  · obtain ⟨W,V,_,_,hV,hrealV,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas hp hp1
    obtain ⟨U,hU,hUc,hreal,hUV,hconv⟩ := exists_weighted_moment_summable A hp3 hs hV hrealV
    exact ⟨W,V,hV,hrealV,s,hs,A,U,hU,hUc,hreal,hUV,hconv⟩
  · have hp3' : 3 < p := lt_of_not_ge hp3
    have hp2 : 2 < p := lt_trans (by norm_num : (2:ℝ≥0∞)<3) hp3'
    obtain ⟨W,V,hV,hrealV,s,hs,A,U,hU,hUc,hreal,hUV,hlocal⟩ :=
      exists_sourceAbelianMoment_onePlusAtlas hp hp2
    refine ⟨W,V,hV,hrealV,s,hs,A,U,hU,hUc,hreal,hUV,?_⟩
    have hr : p/3 ≠ ⊤ := by rw [← Coeff.thirdExponent_eq_div hp]; exact ENNReal.ofReal_ne_top
    have hr1 : 1 < p/3 :=
      (ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr (by simpa using hp3')
    let : Fact (1 ≤ p/3) := ⟨hr1.le⟩
    have hq1 : 1 < (p/3).conjExponent :=
      (ENNReal.HolderConjugate.lt_top_iff_one_lt (p/3) (p/3).conjExponent).mp hr.lt_top
    have hq : (p/3).conjExponent ≠ ⊤ :=
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt (p/3).conjExponent (p/3)).mpr hr1).ne
    intro ψ hψ n
    obtain ⟨T,_,hψT,_,hrows⟩ := hlocal ψ hψ
    obtain ⟨_,_,hb⟩ := hrows (p/3).conjExponent hq hq1
    obtain ⟨a,_,_,_,ha⟩ := hb ψ hψT n
    exact summable_weighted_moment_of_sharp_row A hp3' ψ n a ha

end NLS.Articles.MKdVBelowL2
