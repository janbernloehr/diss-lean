import NLS.Articles.KdVConvexity.IsospectralCanonicalMoments
import NLS.Articles.KdVConvexity.ActionEmbedding
import NLS.KdV.HillHminusOneArnoldMajorant
import NLS.SequenceSpaces.AnalyticSquareTailMajorant
import NLS.SequenceSpaces.WeightedAnalyticRealization

/-! # The actual spectral actions as an analytic weighted ell1 map

The scalar Arnold periods on a common complex potential neighborhood
are realized with the exact base action weight 1/(1+n). The locally
bounded Miura gap majorant controls the complete infinite tail. Finite
low periods require no uniform high-energy estimate.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.Articles.KdVConvexity
open NLS.KdV

def potentialActionSequence (A : ℕ+ → PeriodOneHminusOne → ℂ) :
    PeriodOneHminusOne → BaseActionSpace :=
  fun q => WeightedCoeff.ofFunctionOrZero baseActionWeight 1 (fun k => A (actionIndexEquiv k) q)

theorem exists_analytic_potentialActionSequence_of_high_agreement
    (q : PeriodOneHminusOne) (W : Set PeriodOneHminusOne) (hW : IsOpen W) (hq : q ∈ W)
    (A : ℕ+ → PeriodOneHminusOne → ℂ) (hA : ∀ n, AnalyticOnNhd ℂ (A n) W)
    (N : ℕ) (hhigh : ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ p ∈ W,
      A n p = hillHminusHighContourMoment (n : ℕ) 0 p) :
    ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q ∈ V ∧ V ⊆ W ∧
      AnalyticOnNhd ℂ (potentialActionSequence A) V ∧
      ∀ p ∈ V, ∀ k : ℤ, (potentialActionSequence A p).val k = A (actionIndexEquiv k) p := by
  classical
  obtain ⟨M,T,g,B,C,_,hT,hqT,hB,hC,hbound⟩ := exists_hillHminus_local_weighted_arnold_majorant q
  let V := W ∩ T
  let f : PeriodOneHminusOne → ℤ → ℂ := fun p k =>
    (baseActionWeight k : ℂ)*A (actionIndexEquiv k) p
  let K := max N M
  let s : Finset ℤ := ((Finset.range K).image (fun k : ℕ => (⟨k+1,by omega⟩ : ℕ+))).image actionIndexEquiv.symm
  let e : ℤ → ℤ := fun k => (actionIndexEquiv k : ℤ)
  have he : Function.Injective e := by
    intro i j hij
    apply actionIndexEquiv.injective
    apply Subtype.ext
    change ((actionIndexEquiv i : ℕ) : ℤ) = ((actionIndexEquiv j : ℕ) : ℤ) at hij
    exact Int.ofNat.inj hij
  have hV : IsOpen V := hW.inter hT
  have hf (k : ℤ) : AnalyticOnNhd ℂ (fun p => f p k) V :=
    analyticOnNhd_const.mul ((hA (actionIndexEquiv k)).mono inter_subset_left)
  have htail (p : PeriodOneHminusOne) (hp : p ∈ V) (k : ℤ) (hk : k ∉ s) :
      ‖f p k‖ ≤ C*‖g p (e k)‖^2 := by
    let n := actionIndexEquiv k
    have hn : K ≤ (n : ℕ) := by
      by_contra hn
      apply hk
      apply Finset.mem_image.mpr
      refine ⟨n,?_,actionIndexEquiv.symm_apply_apply k⟩
      apply Finset.mem_image.mpr
      refine ⟨(n : ℕ)-1,Finset.mem_range.mpr (by omega),?_⟩
      apply Subtype.ext
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt n.property)
    have hnN : N ≤ (n : ℕ) := (le_max_left N M).trans hn
    have hnM : M ≤ (n : ℕ) := (le_max_right N M).trans hn
    have hb := (hbound p hp.2).2 n hnM
    have hweight : ‖f p k‖ = ‖A n p‖/(1+(n : ℝ)) := by
      simp only [f,n,baseActionWeight,norm_mul,Complex.norm_real,
        Real.norm_of_nonneg (by positivity : 0 ≤ (1+(actionIndexEquiv k : ℝ))⁻¹)]
      ring
    rw [hweight,hhigh n hnN p hp.1]
    exact hb
  obtain ⟨hcoord,han⟩ := Coeff.analytic_l1_realization_of_sampled_square_tail f V hV hf s e he
    g B C hB hC (fun p hp => (hbound p hp.2).1) htail
  refine ⟨V,hV,⟨hq,hqT⟩,inter_subset_left,?_,?_⟩
  · intro p hp
    exact ((WeightedCoeff.weightIsometry baseActionWeight 1).symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp
      (han p hp)
  intro p hp k
  change Coeff.ofFunctionOrZero 1 (f p) k/(baseActionWeight k : ℂ) = A (actionIndexEquiv k) p
  rw [hcoord p hp k]
  exact mul_div_cancel_left₀ _ (baseActionWeight.complex_ne_zero k)

end NLS.Articles.KdVConvexity
