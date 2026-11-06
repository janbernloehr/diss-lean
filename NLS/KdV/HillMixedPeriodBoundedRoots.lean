import NLS.KdV.HillProductPeriodBoundedRoots
import NLS.KdV.HillMixedHilbertPeriodMap

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- A finite original low-contour Hilbert head has one source neighborhood
and one bound for all omitted indices and bounded root inputs. -/
theorem exists_hillLowComplexPeriodSequence_bounded_roots
    (N : ℕ) (A : ℝ) :
    ∃ U : Set (Coeff 2), ∃ L : ℝ, IsOpen U ∧ SpectralWeight.one.toCoeff q∈U ∧ 0<L ∧
      ∀ n : ℕ, 1≤n → ∀ a : Coeff 2, ‖a‖≤A → ∀ p∈U,
        ‖hillLowComplexPeriodSequence q hq hr N n (a,p)‖≤L := by
  have hex (j : Fin N) : ∃ U : Set (Coeff 2), ∃ C : ℝ,
      IsOpen U ∧ SpectralWeight.one.toCoeff q∈U ∧ 0<C ∧
        (1≤j.val → ∀ n : ℕ, ∀ a : Coeff 2, ‖a‖≤A → ∀ p∈U,
          ‖hillAbelianProductComplexPeriod q hq hr n j.val (a,p)‖≤C) := by
    by_cases hj : 1≤j.val
    · obtain ⟨U,C,hU,hqU,hC,_,hbound⟩ := exists_hillAbelianProductComplexPeriod_bounded_roots q hq hr j.val hj A
      exact ⟨U,C,hU,hqU,hC,fun _ => hbound⟩
    · exact ⟨univ,1,isOpen_univ,mem_univ _,by norm_num,fun h => (hj h).elim⟩
  choose U C hopen hmem hC hbound using hex
  let V : Set (Coeff 2) := ⋂ j : Fin N, U j
  let b : Fin N → ℝ := fun j => (2*Real.pi+2*|freeHillValue j.val|/Real.pi)*C j
  let L : ℝ := (∑ j : Fin N, b j)+1
  have hb (j : Fin N) : 0≤b j := by
    have hcj := hC j
    dsimp only [b]
    positivity
  have hL : 0<L := by
    have hsum : 0≤∑ j : Fin N, b j := Finset.sum_nonneg (fun j _ => hb j)
    dsimp only [L]
    linarith
  refine ⟨V,L,isOpen_iInter_of_finite hopen,mem_iInter.mpr hmem,hL,?_⟩
  intro n hn a ha p hp
  unfold hillLowComplexPeriodSequence
  have hnorm := norm_sum_le (Finset.range N) (fun k : ℕ =>
    if 1≤k ∧ k≠n then lp.single (E := fun _ : ℤ => ℂ) 2 (k : ℤ)
      ((((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*hillAbelianComplexPeriod q hq hr n k (a,p)) else 0)
  simp_rw [←Fin.sum_univ_eq_sum_range] at hnorm ⊢
  apply hnorm.trans
  have hsum : (∑ j : Fin N, ‖if 1≤j.val ∧ j.val≠n then
      lp.single (E := fun _ : ℤ => ℂ) 2 (j.val : ℤ) ((((freeHillValue j.val : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
        hillAbelianComplexPeriod q hq hr n j.val (a,p)) else 0‖)≤∑ j : Fin N, b j := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : 1≤j.val ∧ j.val≠n
    · rw [if_pos hj,lp.norm_single (by norm_num : (0 : ℝ≥0∞)<2),
        scaled_hillAbelianComplexPeriod_eq_productPeriod q hq hr n j.val hn,norm_mul]
      exact mul_le_mul (norm_hillScaledProductPeriodCoefficient_le n j.val hn)
        (hbound j hj.1 n a ha p (mem_iInter.mp hp j)) (norm_nonneg _) (by positivity)
    · rw [if_neg hj,norm_zero]
      exact hb j
  exact hsum.trans (by dsimp only [L];linarith)

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The actual mixed Hilbert periods are bounded on bounded root inputs
and a common original source neighborhood, independently of the index. -/
theorem exists_hillMixedComplexPeriodSequence_bounded_roots
    (N : ℕ) (B D A : ℝ) (hB : 0≤B) (hD : 0≤D) (hA : 0≤A)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) :
    ∃ V : Set (Coeff 2), ∃ M : ℝ, IsOpen V ∧ SpectralWeight.one.toCoeff q∈V ∧ 0<M ∧
      ∀ n : ℕ, 1≤n → ∀ a : Coeff 2, ‖a‖≤A → ∀ p∈V, ‖p‖≤B →
        ‖hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a,p)‖≤M := by
  obtain ⟨V,L,hV,hqV,hL,hLow⟩ := exists_hillLowComplexPeriodSequence_bounded_roots q hq hr N A
  let M := L+Real.exp ((2/Real.pi^2)*A)*A+2*D*Real.exp ((8/Real.pi^2)*A)*B
  have hM : 0<M := by dsimp only [M];positivity
  refine ⟨V,M,hV,hqV,hM,?_⟩
  intro n hn a ha p hp hpB
  have htail := norm_hillComplexScaledTailPeriodSequence_le h0q h0r N n hn a p D hD
    (fun k hk hnk => (hc p hpB).2 n k hn hk hnk a)
  rw [hillMixedComplexPeriodSequence]
  apply (norm_add_le _ _).trans
  have htail' : ‖hillComplexScaledTailPeriodSequence h0q h0r N n (a,p)‖≤
      Real.exp ((2/Real.pi^2)*A)*A+2*D*Real.exp ((8/Real.pi^2)*A)*B := by
    apply htail.trans
    gcongr
  dsimp only [M]
  linarith [hLow n hn a ha p hp]

end NLS.KdV
