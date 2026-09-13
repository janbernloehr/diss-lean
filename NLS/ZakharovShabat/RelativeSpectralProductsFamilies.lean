import NLS.ZakharovShabat.RelativeSpectralProductsUniform
import NLS.SequenceSpaces.UniformHolderTails

/-!
# Spectral-product convergence uniform over bounded displacement families

On a closed half-gap ball, reciprocal free denominators lie in a finite
conjugate sequence space. Hölder tail estimates give uniform convergence over
all bounded displacement families, without continuity of eigenvalue labels.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Relative displacements have a uniform total bound and vanishing absolute tails on bounded families. -/
theorem uniform_absolute_spectralRelativeDisplacements {X : Type*} (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ξ : X → ℤ → ℂ) (hξ : ∀ x, Memℓp (fun n => ξ x n-(Real.pi : ℂ)*n) p)
    (S : Set X) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ x ∈ S, ‖(⟨_,hξ x⟩ : Coeff p)‖ ≤ R) (z₀ : ℂ) (hz₀ : z₀ ∉ freeLattice) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ D : ℕ → ℝ, Tendsto D atTop (𝓝 0) ∧
      (∀ t ∈ closedBall z₀ (freeGap z₀/2) ×ˢ S, ∀ s : Finset ℤ,
        (∑ n ∈ s, ‖-((ξ t.2 n-(Real.pi : ℂ)*n)/(t.1-(Real.pi : ℂ)*n))‖) ≤ B) ∧
      ∀ N : ℕ, ∀ t ∈ closedBall z₀ (freeGap z₀/2) ×ˢ S, ∀ s : Finset ℤ,
        (∀ n ∈ s, N ≤ n.natAbs) →
        (∑ n ∈ s, ‖-((ξ t.2 n-(Real.pi : ℂ)*n)/(t.1-(Real.pi : ℂ)*n))‖) ≤ D N := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  have hq : p.conjExponent ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  have hq1 : 1 < p.conjExponent :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  let b : Coeff p.conjExponent := ⟨_,inverse_denominator_memlp hq1 z₀ hz₀⟩
  let a (t : ℂ × X) : Coeff p := ⟨_,hξ t.2⟩
  have h := Coeff.uniform_absolute_holder_tails a b hq
    (fun t n => -((ξ t.2 n-(Real.pi : ℂ)*n)/(t.1-(Real.pi : ℂ)*n)))
    (closedBall z₀ (freeGap z₀/2) ×ˢ S) 2 R (by norm_num)
    (fun t ht => hbound t.2 ht.2) (fun t ht n => by
      simpa only [norm_neg, div_eq_mul_inv] using norm_relativeDisplacement_le_twice (ξ t.2) z₀ hz₀ t.1 ht.1 n)
  exact ⟨2*R*‖b‖,by positivity,_,h.2.1,h.1,h.2.2⟩

/-- Single relative products are uniformly bounded and uniformly Cauchy over every bounded family. -/
theorem uniformCauchySeqOn_spectralRelativeFactor_family {X : Type*} (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ξ : X → ℤ → ℂ) (hξ : ∀ x, Memℓp (fun n => ξ x n-(Real.pi : ℂ)*n) p)
    (S : Set X) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ x ∈ S, ‖(⟨_,hξ x⟩ : Coeff p)‖ ≤ R) (z₀ : ℂ) (hz₀ : z₀ ∉ freeLattice) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ N : ℕ, ∀ t ∈ closedBall z₀ (freeGap z₀/2) ×ˢ S,
        ‖∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), spectralRelativeFactor (ξ t.2) t.1 n‖ ≤ B) ∧
      UniformCauchySeqOn (fun (N : ℕ) t => ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        spectralRelativeFactor (ξ t.2) t.1 n) atTop (closedBall z₀ (freeGap z₀/2) ×ˢ S) := by
  obtain ⟨B,_,D,hD,hb,ht⟩ := uniform_absolute_spectralRelativeDisplacements hp hp1 ξ hξ S R hR hbound z₀ hz₀
  let u (t : ℂ × X) (n : ℤ) := -((ξ t.2 n-(Real.pi : ℂ)*n)/(t.1-(Real.pi : ℂ)*n))
  have he (t : ℂ × X) (ht : t ∈ closedBall z₀ (freeGap z₀/2) ×ˢ S) (N : ℕ) :
      (∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), spectralRelativeFactor (ξ t.2) t.1 n) =
        ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1+u t n) := by
    apply Finset.prod_congr rfl
    intro n _
    exact spectralRelativeFactor_eq (ξ t.2) t.1 (closedBall_half_freeGap_subset z₀ hz₀ ht.1) n
  refine ⟨Real.exp B,(Real.exp_pos _).le,?_,?_⟩
  · intro N t ht
    rw [he t ht N]
    exact (NLS.ComplexAnalysis.norm_prod_one_add_le_exp _ (u t)).trans (Real.exp_le_exp.mpr (hb t ht _))
  · have h := NLS.ComplexAnalysis.uniformCauchySeqOn_prod_one_add u _ B D hD hb ht
    rw [Metric.uniformCauchySeqOn_iff] at h ⊢
    intro ε hε
    obtain ⟨N,hN⟩ := h ε hε
    exact ⟨N,fun M hM K hK t ht => by simpa only [he t ht M, he t ht K] using hN M hM K hK t ht⟩

/-- Paired relative products converge uniformly over bounded families, even across root collisions. -/
theorem tendstoUniformlyOn_spectralRelativePair_family {X : Type*} (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ξ η : X → ℤ → ℂ) (hξ : ∀ x, Memℓp (fun n => ξ x n-(Real.pi : ℂ)*n) p)
    (hη : ∀ x, Memℓp (fun n => η x n-(Real.pi : ℂ)*n) p)
    (S : Set X) (R : ℝ) (hR : 0 ≤ R)
    (hbξ : ∀ x ∈ S, ‖(⟨_,hξ x⟩ : Coeff p)‖ ≤ R)
    (hbη : ∀ x ∈ S, ‖(⟨_,hη x⟩ : Coeff p)‖ ≤ R) (z₀ : ℂ) (hz₀ : z₀ ∉ freeLattice) :
    TendstoUniformlyOn (fun (N : ℕ) t => ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      spectralRelativeFactor (ξ t.2) t.1 n*spectralRelativeFactor (η t.2) t.1 n)
      (fun t => spectralRelativePairProduct (ξ t.2) (η t.2) t.1) atTop
      (closedBall z₀ (freeGap z₀/2) ×ˢ S) := by
  obtain ⟨A,hA,hξb,hξc⟩ := uniformCauchySeqOn_spectralRelativeFactor_family hp hp1 ξ hξ S R hR hbξ z₀ hz₀
  obtain ⟨B,hB,hηb,hηc⟩ := uniformCauchySeqOn_spectralRelativeFactor_family hp hp1 η hη S R hR hbη z₀ hz₀
  have h := NLS.ComplexAnalysis.uniformCauchySeqOn_mul_bounded _ _ _ A B hA hB hξc hηc hξb hηb
  simp_rw [← Finset.prod_mul_distrib] at h
  exact h.tendstoUniformlyOn_of_tendsto (fun t ht =>
    tendsto_spectralRelativePairProduct hp (ξ t.2) (η t.2) (hξ t.2) (hη t.2) t.1
      (closedBall_half_freeGap_subset z₀ hz₀ ht.1))

end NLS.ZakharovShabat
