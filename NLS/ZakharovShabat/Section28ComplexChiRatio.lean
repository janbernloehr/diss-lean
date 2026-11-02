import NLS.ZakharovShabat.Section28ComplexCentralProduct
import NLS.ZakharovShabat.Section28ComplexEnclosingRoot
import NLS.ZakharovShabat.SourceLemmaF1
import NLS.ZakharovShabat.SourceH1GapProductReduction
import NLS.ZakharovShabat.SourceActionChi

/-! # The signed rational estimate for the literal complex chi product

The actual exterior product, adjacent-factor telescope and enclosing roots
are combined on one source neighborhood. The rational expression uses
absolute indices and includes the boundary and zero cutoffs.
-/
noncomputable section
open Set Complex
open scoped ENNReal BigOperators
namespace NLS.ZakharovShabat

/-- One connected L2 neighborhood gives the reflected rational bound for
the literal chi product on every closed complex H1 gap. -/
theorem section28_complex_chi_ratio_neighborhood
    (W : Set (CoeffPair 2)) (hW : IsOpen W) (hrealW : realTypeSourceLocus 2 ⊆ W) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus 2 ⊆ U ∧ U ⊆ W ∧
      ∀ ψ ∈ U,
        ∀ φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2,
          weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ →
          ∀ N : ℕ, 8*‖φ‖^2 ≤ 1+(N:ℝ) → ∀ n : ℤ, N ≤ n.natAbs →
            ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) ψ n,
              ‖sourceActionChi (by simp) (by norm_num) n ψ z‖ ≤
                128*((|(n:ℝ)|+N+2/5)/(|(n:ℝ)|-N+3/10)) := by
  classical
  obtain ⟨_,_,_,_,_,hoffset⟩ := sourceLemmaF1 (by simp : (2:ℝ≥0∞) ≠ ⊤) (by norm_num)
  have hlocal (φ : realTypeSourceSubmodule 2) := hoffset φ.val φ.property
  choose V hV hφV hVD hcrit using hlocal
  let O := ⋃ φ : realTypeSourceSubmodule 2, V φ
  have hO : IsOpen O := isOpen_iUnion hV
  have hrO : realTypeSourceLocus 2 ⊆ O := fun φ hφ =>
    mem_iUnion.mpr ⟨⟨φ,hφ⟩,hφV ⟨φ,hφ⟩⟩
  obtain ⟨D,hD,_,hrD,hdisjoint⟩ := exists_global_source_disjoint_periodicSegments
    (by simp : (2:ℝ≥0∞) ≠ ⊤) (by norm_num)
  obtain ⟨U,hU,hUc,hrU,hsub,hcentral⟩ := section28_complex_central_product_neighborhood
    (by simp : (2:ℝ≥0∞) ≠ ⊤) (by norm_num) (W ∩ O ∩ D) ((hW.inter hO).inter hD)
    (fun ψ hψ => ⟨⟨hrealW hψ,hrO hψ⟩,hrD hψ⟩)
  refine ⟨U,hU,hUc,hrU,fun ψ hψ => (hsub hψ).1.1,?_⟩
  intro ψ hψ φ hφ N hN n hn z hz
  obtain ⟨ψ₀,hψ₀⟩ := mem_iUnion.mp (hsub hψ).1.2
  have hdom : z ∈ sourceStandardRootOmittedDomain (by simp) (by norm_num) ψ n := by
    intro m hmn
    exact Set.disjoint_left.mp (hdisjoint ψ (hsub hψ).2 n m hmn.symm) hz
  have hfull := sourceCriticalRootRatioExtension_le_finite_core (by simp) (by norm_num)
    ψ n N hn z hdom 128 (by
      intro s hs hsext
      exact sourceH1_exterior_product_le_128 ψ φ hφ N hN s n hs hsext hn z hz
        (fun m _ => hcrit ψ₀ ψ hψ₀ m))
  rw [sourceCriticalRootRatioExtension_eq_neg_I_chi (by simp) (by norm_num) ψ n z hdom,
    norm_mul,norm_neg,norm_I,one_mul] at hfull
  apply hfull.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 128)
  by_cases hN0 : N = 0
  · subst N
    simp only [Nat.cast_zero,neg_zero,Finset.Ioo_self,Finset.prod_empty,norm_one,add_zero,sub_zero]
    apply (le_div_iff₀ (by positivity : 0 < |(n:ℝ)|+3/10)).mpr
    linarith
  · have hNp : 1 ≤ N := by omega
    by_cases hn0 : 0 ≤ n
    · have hnN : (N:ℤ) ≤ n := by omega
      exact ((hcentral ψ hψ N hNp n z hz).1 hnN).trans
        (section28_complex_enclosing_root_ratio_signed ψ φ hφ N hN _ _ n
          (by simp) (by omega) hn z hz)
    · have hnN : n ≤ -(N:ℤ) := by omega
      exact ((hcentral ψ hψ N hNp n z hz).2 hnN).trans
        (section28_complex_enclosing_root_ratio_signed ψ φ hφ N hN _ _ n
          (by simp) (by omega) hn z hz)

end NLS.ZakharovShabat
