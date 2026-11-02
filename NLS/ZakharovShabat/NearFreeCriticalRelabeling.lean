import NLS.ZakharovShabat.FreeDerivativeZeroCounts
import NLS.ZakharovShabat.CriticalPointLabeling
import NLS.SequenceSpaces.FiniteModification

/-! # Complete critical labels from uniformly close free-lattice roots

A complete arbitrary central labeling can be replaced by actual distinct
roots close to every free center. The central multiplicities are retained
by a submultiset/cardinality argument; distant uniqueness fixes the tail.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : PairSpace p} {hφ : φ ∈ pairParitySubspace 0}
variable {N : ℕ} {η : ℤ → ℂ}

theorem CriticalPointLabeling.relabel_of_near_free
    (h : CriticalPointLabeling hp hp1 φ hφ N η) (ξ : ℤ → ℂ)
    (hcrit : ∀ n, deriv (canonicalDiscriminant hp φ) (ξ n) = 0)
    (hclose : ∀ n, ‖ξ n-(Real.pi : ℂ)*n‖ < Real.pi/8) :
    CriticalPointLabeling hp hp1 φ hφ N ξ ∧ ∀ n, N < n.natAbs → ξ n = η n := by
  classical
  have hagree (n : ℤ) (hn : N < n.natAbs) : ξ n = η n :=
    ((h.distant n hn).2.2.2 _ (mem_closedBall_iff_norm.mpr
      ((hclose n).le.trans (by linarith [Real.pi_pos])))).mp (hcrit n)
  have hinj : Function.Injective ξ := by
    intro m n he
    by_contra hmn
    have ht := norm_add_le ((Real.pi : ℂ)*m-ξ m) (ξ n-(Real.pi : ℂ)*n)
    have heq : (Real.pi : ℂ)*m-ξ m+(ξ n-(Real.pi : ℂ)*n) =
        (Real.pi : ℂ)*m-(Real.pi : ℂ)*n := by rw [he]; ring
    rw [heq,norm_free_center_sub] at ht
    have hgap : (1 : ℝ) ≤ |((m-n : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmn)
    have hm : ‖(Real.pi : ℂ)*m-ξ m‖ < Real.pi/8 := by
      rw [norm_sub_rev]
      exact hclose m
    have hn := hclose n
    nlinarith [Real.pi_pos,mul_le_mul_of_nonneg_left hgap Real.pi_pos.le]
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) N
  let B : Multiset ℂ := ∑ n ∈ S, ({ξ n} : Multiset ℂ)
  have hBimage : B = (S.image ξ).val := by
    rw [← Finset.sum_multiset_singleton (S.image ξ),Finset.sum_image]
    intro i _ j _ he
    exact hinj he
  have hnodup : B.Nodup := by rw [hBimage]; exact (S.image ξ).nodup
  have hcentralMem (n : ℤ) (hn : n ∈ S) : ξ n ∈ centralCriticalRoots hp hp1 φ hφ N := by
    have hnN : n.natAbs ≤ N := by simp only [S,Finset.mem_Icc] at hn; omega
    have hnreal : (n.natAbs : ℝ) ≤ N := by exact_mod_cast hnN
    have hnorm : ‖(Real.pi : ℂ)*n‖ = Real.pi*(n.natAbs : ℝ) := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
        Complex.norm_intCast,← Int.cast_abs,← Int.natCast_natAbs,Int.cast_natCast]
    have ht := norm_le_norm_sub_add (ξ n) ((Real.pi : ℂ)*n)
    rw [hnorm] at ht
    apply (mem_centralCriticalRoots hp hp1 φ hφ N _).mpr
    refine ⟨?_,hcrit n⟩
    rw [mem_closedBall,dist_zero_right,centralCircleRadius]
    nlinarith [hclose n,Real.pi_pos]
  have hsub : B ⊆ centralCriticalRoots hp hp1 φ hφ N := by
    intro z hz
    obtain ⟨n,hn,he⟩ : ∃ n ∈ S, ξ n = z := by
      simpa only [B,Multiset.mem_sum,Multiset.mem_singleton,eq_comm] using hz
    rw [← he]
    exact hcentralMem n hn
  have hle := (Multiset.le_iff_subset hnodup).mpr hsub
  have hcard : (centralCriticalRoots hp hp1 φ hφ N).card ≤ B.card := by
    rw [← h.central]
    simp only [B,S,Multiset.card_sum,Multiset.card_singleton]
    exact le_rfl
  have hcentral : B = centralCriticalRoots hp hp1 φ hφ N := Multiset.eq_of_le_of_card_le hle hcard
  refine ⟨⟨hcentral,?_,?_⟩,hagree⟩
  · intro n hn
    rw [hagree n hn]
    exact h.distant n hn
  intro z
  constructor
  · intro hz
    obtain ⟨n,hn⟩ := (h.exhaustive z).mp hz
    by_cases hnN : N < n.natAbs
    · exact ⟨n,(hagree n hnN).trans hn⟩
    have hnS : n ∈ S := by simp only [S,Finset.mem_Icc]; omega
    have hzmem : z ∈ centralCriticalRoots hp hp1 φ hφ N := by
      rw [← h.central]
      simp only [Multiset.mem_sum,Multiset.mem_singleton]
      exact ⟨n,hnS,hn.symm⟩
    rw [← hcentral] at hzmem
    obtain ⟨j,_,hj⟩ : ∃ j ∈ S, ξ j = z := by
      simpa only [B,Multiset.mem_sum,Multiset.mem_singleton,eq_comm] using hzmem
    exact ⟨j,hj⟩
  · rintro ⟨n,rfl⟩
    exact hcrit n

theorem CriticalPointLabeling.memℓp_of_near_free_relabeling
    (h : CriticalPointLabeling hp hp1 φ hφ N η) (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p)
    (ξ : ℤ → ℂ) (hcrit : ∀ n, deriv (canonicalDiscriminant hp φ) (ξ n) = 0)
    (hclose : ∀ n, ‖ξ n-(Real.pi : ℂ)*n‖ < Real.pi/8) :
    Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p := by
  apply NLS.memℓp_of_eq_outside_finset hη (Finset.Icc (-(N : ℤ)) N)
  intro n hn
  have hnN : N < n.natAbs := by simp only [Finset.mem_Icc] at hn; omega
  rw [(h.relabel_of_near_free ξ hcrit hclose).2 n hnN]

end NLS.ZakharovShabat
