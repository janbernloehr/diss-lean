import NLS.ZakharovShabat.CompletePeriodicParityPairs
import NLS.ZakharovShabat.UniformSpectralDisplacements

/-!
# Uniform displacement bounds for completed actual parity roots

The fixed central box bounds every admissible central label. Replacing finitely
many coordinates therefore preserves a common displacement norm bound, without
requiring any continuity of the chosen labels.
-/

noncomputable section
open scoped ENNReal
namespace NLS
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Finite replacement is bounded by its coordinate budget and the unchanged sequence norm. -/
theorem Coeff.norm_le_of_eq_outside_finset (a b : Coeff p) (s : Finset ℤ) (B : ℝ)
    (hb : ∀ n ∈ s, ‖a n‖ ≤ B) (he : ∀ n ∉ s, a n = b n) :
    ‖a‖ ≤ s.card*B+‖b‖ := by
  have ha : a = Coeff.truncate s a + (b-Coeff.truncate s b) := by
    ext n
    by_cases hn : n ∈ s
    · simp [Coeff.truncate_apply, hn]
    · simp [Coeff.truncate_apply, hn, he n hn]
  have hfinite : ‖Coeff.truncate s a‖ ≤ s.card*B := by
    unfold Coeff.truncate
    apply (norm_sum_le _ _).trans
    calc
      _ = ∑ n ∈ s, ‖a n‖ := by
        apply Finset.sum_congr rfl
        intro n _
        exact lp.norm_single (E := fun _ : ℤ => ℂ) (zero_lt_one.trans_le (Fact.out : 1 ≤ p)) n (a n)
      _ ≤ ∑ _n ∈ s, B := Finset.sum_le_sum hb
      _ = _ := by simp
  calc
    ‖a‖ = ‖Coeff.truncate s a+(b-Coeff.truncate s b)‖ := congrArg norm ha
    _ ≤ ‖Coeff.truncate s a‖+‖b-Coeff.truncate s b‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hfinite
      (Coeff.norm_sub_truncate_le (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' s b)

namespace ZakharovShabat

/-- One bound controls all central parity labels and their displacements for a fixed central cutoff. -/
theorem exists_bound_centralParityLabel_displacements (hp : p ≠ ⊤) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (φ : PairSpace p) (ξ η : ℤ → ℂ), CentralParityLabeling hp φ N ξ η →
      ∀ n : ℤ, n.natAbs ≤ N → ‖ξ n-(Real.pi : ℂ)*n‖ ≤ B ∧ ‖η n-(Real.pi : ℂ)*n‖ ≤ B := by
  obtain ⟨A,hA,hAb⟩ := (isBounded_centralSpectralBox N).exists_pos_norm_le
  let s := Finset.Icc (-(N : ℤ)) (N : ℤ)
  obtain ⟨D,hD,hDb⟩ := ((s.finite_toSet.image (fun n : ℤ => (Real.pi : ℂ)*n)).isBounded).exists_pos_norm_le
  refine ⟨A+D,by positivity,fun φ ξ η h n hn => ?_⟩
  have hns : n ∈ s := by simp only [s, Finset.mem_Icc]; omega
  have hpar : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have hni : n ∈ centralParityIndices N (n%2) := by
    simp only [centralParityIndices, Finset.mem_filter, Int.emod_emod]
    exact ⟨hns,trivial⟩
  have hx := ((h.root_iff (n%2) hpar (ξ n)).mp ⟨n,hni,Or.inl rfl⟩).1
  have hy := ((h.root_iff (n%2) hpar (η n)).mp ⟨n,hni,Or.inr rfl⟩).1
  have hfree := hDb ((Real.pi : ℂ)*n) ⟨n,hns,rfl⟩
  exact ⟨(norm_sub_le _ _).trans (add_le_add (hAb _ ((mem_centralPeriodicSpectrum hp φ N _).mp hx).2) hfree),
    (norm_sub_le _ _).trans (add_le_add (hAb _ ((mem_centralPeriodicSpectrum hp φ N _).mp hy).2) hfree)⟩

/-- Actual completed parity roots have uniformly bounded displacement norms on a common potential neighborhood. -/
theorem exists_uniform_bounded_completePeriodicParityPairs (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∃ R : ℝ, 0 ≤ R ∧ ∀ ψ ∈ U,
        weightedBaseToPair w ψ ∈ pairParitySubspace 0 →
        ∃ ξ η : ℤ → ℂ, ∃ h : CompletePeriodicParityPairs hp w ψ N₀ ξ η,
          ‖(⟨_,h.left_displacement⟩ : Coeff p)‖ ≤ R ∧ ‖(⟨_,h.right_displacement⟩ : Coeff p)‖ ≤ R := by
  obtain ⟨N,hN,U,ho,hconv,hφ,h0,R,hR,hdata⟩ := exists_uniform_bounded_periodicDisplacements hp hp1 w φ
  obtain ⟨B,hB,hBb⟩ := exists_bound_centralParityLabel_displacements hp N
  let s := Finset.Icc (-(N : ℤ)) (N : ℤ)
  refine ⟨N,hN,U,ho,hconv,hφ,h0,s.card*B+R,by positivity,?_⟩
  intro ψ hψ heven
  obtain ⟨ξ,η,hξ,hη,hbξ,hbη,_,hr,hc⟩ := hdata ψ hψ
  obtain ⟨α,β,h,hagree⟩ := exists_completePeriodicParityPairs hp w ψ heven N (hc N le_rfl) ξ η hξ hη hr
  have hlow (n : ℤ) (hn : n ∈ s) := hBb _ α β h.central n (by simp only [s, Finset.mem_Icc] at hn; omega)
  refine ⟨α,β,h,?_,?_⟩
  · apply (Coeff.norm_le_of_eq_outside_finset (⟨_,h.left_displacement⟩ : Coeff p) (⟨_,hξ⟩ : Coeff p)
      s B (fun n hn => (hlow n hn).1) (fun n hn => ?_)).trans (add_le_add le_rfl hbξ)
    change α n-(Real.pi : ℂ)*n = ξ n-(Real.pi : ℂ)*n
    rw [(hagree n (by simp only [s, Finset.mem_Icc] at hn; omega)).1]
  · apply (Coeff.norm_le_of_eq_outside_finset (⟨_,h.right_displacement⟩ : Coeff p) (⟨_,hη⟩ : Coeff p)
      s B (fun n hn => (hlow n hn).2) (fun n hn => ?_)).trans (add_le_add le_rfl hbη)
    change β n-(Real.pi : ℂ)*n = η n-(Real.pi : ℂ)*n
    rw [(hagree n (by simp only [s, Finset.mem_Icc] at hn; omega)).2]

end ZakharovShabat
end NLS
