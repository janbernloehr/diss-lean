import NLS.ZakharovShabat.SourceBirkhoffGlobalInverse

/-! # Open dense range at every finite exponent above one

At exponents above two, every finite output truncation is the inclusion
of a Hilbert target and hence is attained by an actual source. Their
norm convergence proves density. At exponents at most two the stronger
surjectivity statement is available. This completes the range assertion
of Theorem 14.1(iv), without claiming surjectivity above two.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Every finite target truncation is attained, also above exponent two. -/
theorem truncatePair_mem_real_map_range
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (A : Finset ℤ) (z : RealCoeff p × RealCoeff p) :
    RealCoeff.truncatePair A z ∈ range (sourceRealBirkhoffMap hp hp1 s) := by
  by_cases hp2 : p ≤ 2
  · exact D.proposition17_3 hp2 _
  · have h2p : (2 : ℝ≥0∞) ≤ p := le_of_not_ge hp2
    obtain ⟨V₀,C,V,u,E⟩ :=
      exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
    let y := RealCoeff.finitePair 2 A z
    let φ := E.hilbertRealHomeomorph.symm y
    refine ⟨realTypeSourceExponentInclusion h2p φ,?_⟩
    rw [← E.real_map_exponent D h2p]
    have he : sourceRealBirkhoffMap (by simp) (by norm_num) u φ = y :=
      E.hilbertRealHomeomorph.apply_symm_apply y
    rw [he]
    apply Prod.ext <;> ext n
    · change y.1 n = RealCoeff.truncate A z.1 n
      rw [RealCoeff.truncate_apply]
      exact (RealCoeff.finitePair_apply A z n).1
    · change y.2 n = RealCoeff.truncate A z.2 n
      rw [RealCoeff.truncate_apply]
      exact (RealCoeff.finitePair_apply A z n).2

/-- The actual real Birkhoff map has dense range for every `1 < p < ∞`. -/
theorem real_map_denseRange (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) :
    DenseRange (sourceRealBirkhoffMap hp hp1 s) := by
  intro z
  exact isClosed_closure.mem_of_tendsto (RealCoeff.tendsto_truncatePair hp z)
    (Eventually.of_forall (fun A => subset_closure (D.truncatePair_mem_real_map_range A z)))

/-- The open dense image asserted in Theorem 14.1(iv). -/
theorem real_map_open_dense_range (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) :
    IsOpen (range (sourceRealBirkhoffMap hp hp1 s)) ∧
      Dense (range (sourceRealBirkhoffMap hp hp1 s)) := by
  refine ⟨?_,D.real_map_denseRange⟩
  simpa only [image_univ] using D.real_map_isOpenEmbedding.isOpenMap univ isOpen_univ

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
