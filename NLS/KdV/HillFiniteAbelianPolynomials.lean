import NLS.KdV.HillGlobalNormalizedDifferentials
import NLS.KdV.HillDirichletCosineData
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # Finite polynomial prefixes of the independent Abelian numerator

Collapsed gaps identify the actual Dirichlet and selected numerator roots.
The polynomial prefix omits its own index and consequently has degree
strictly below the number of retained Dirichlet nodes.
-/
noncomputable section
open Set Complex Filter Topology Polynomial
open NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

def hillDirichletEnergies (q : RealPeriodOneHillPotential) (k : ℕ) : ℝ :=
  hillDirichletEnergy q.val q.property.1 q.property.2 (k+1) (by omega)

theorem hillDirichletEnergies_mem_box (q : RealPeriodOneHillPotential) :
    hillDirichletEnergies q ∈ hillGapRootBox q.val q.property.1 q.property.2 :=
  fun k => hillDirichletEnergy_mem_gap q.val q.property.1 q.property.2 (k+1) (by omega)

theorem injective_hillDirichletEnergies (q : RealPeriodOneHillPotential) :
    Function.Injective (fun k => (hillDirichletEnergies q k : ℂ)) := by
  intro k j he
  by_contra hkj
  exact hillDirichletEnergy_ne_of_ne q (k+1) (j+1) (by omega) (by omega) (by omega) he

def hillAbelianFiniteNumeratorPolynomial (σ : ℕ → ℝ) (n K : ℕ) : Polynomial ℂ :=
  ∏ k ∈ Finset.range K,
    if k+1 = n then 1 else
      C ((freeHillValue (k+1 : ℕ) : ℂ)⁻¹)*(C (σ k : ℂ)-X)

theorem eval_hillAbelianFiniteNumeratorPolynomial (σ : ℕ → ℝ) (n K : ℕ) (E : ℂ) :
    (hillAbelianFiniteNumeratorPolynomial σ n K).eval E =
      ∏ k ∈ Finset.range K,hillAbelianNumeratorFactor σ n k E := by
  unfold hillAbelianFiniteNumeratorPolynomial
  rw [eval_prod]
  apply Finset.prod_congr rfl
  intro k _
  unfold hillAbelianNumeratorFactor hillGapRootEnergyFactor
  split_ifs <;> simp only [eval_one,eval_mul,eval_C,eval_sub,eval_X,div_eq_mul_inv,mul_comm]

theorem degree_hillAbelianFiniteNumeratorPolynomial (σ : ℕ → ℝ) (n K : ℕ)
    (hn : 1 ≤ n) (hK : n ≤ K) :
    (hillAbelianFiniteNumeratorPolynomial σ n K).degree < K := by
  let F (k : ℕ) : Polynomial ℂ :=
    if k+1 = n then 1 else C ((freeHillValue (k+1 : ℕ) : ℂ)⁻¹)*(C (σ k : ℂ)-X)
  have hi : n-1 ∈ Finset.range K := Finset.mem_range.mpr (by omega)
  have he : F (n-1) = 1 := by simp [F,show n-1+1 = n by omega]
  have heq : hillAbelianFiniteNumeratorPolynomial σ n K =
      ∏ k ∈ (Finset.range K).erase (n-1),F k := (Finset.prod_erase _ he).symm
  have hdeg : (hillAbelianFiniteNumeratorPolynomial σ n K).natDegree ≤ K-1 := by
    rw [heq]
    apply (natDegree_prod_le _ _).trans
    calc
      _ ≤ ∑ k ∈ (Finset.range K).erase (n-1),(1 : ℕ) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkne : k+1 ≠ n := by have h := (Finset.mem_erase.mp hk).1;omega
        dsimp only [F]
        rw [if_neg hkne]
        have hd : (C ((freeHillValue (k+1 : ℕ) : ℂ)⁻¹)*(C (σ k : ℂ)-X)).natDegree ≤
            (C ((freeHillValue (k+1 : ℕ) : ℂ)⁻¹)).natDegree+(C (σ k : ℂ)-X).natDegree := natDegree_mul_le
        have hneg : C (σ k : ℂ)-X = -(X-C (σ k : ℂ)) := by ring
        simpa only [hneg,natDegree_neg,natDegree_X_sub_C,natDegree_C,zero_add] using hd
      _ = K-1 := by simp only [Finset.sum_const,Finset.card_erase_of_mem hi,Finset.card_range,smul_eq_mul,mul_one]
  have hlt : (hillAbelianFiniteNumeratorPolynomial σ n K).natDegree < K :=
    lt_of_le_of_lt hdeg (by omega)
  exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hlt)

theorem degree_const_mul_hillAbelianFiniteNumeratorPolynomial (σ : ℕ → ℝ) (n K : ℕ)
    (hn : 1 ≤ n) (hK : n ≤ K) (c : ℂ) :
    (C c*hillAbelianFiniteNumeratorPolynomial σ n K).degree < K := by
  by_cases hc : c = 0
  · simp only [hc,map_zero,zero_mul,degree_zero]
    exact WithBot.bot_lt_coe _
  · rw [degree_C_mul hc]
    exact degree_hillAbelianFiniteNumeratorPolynomial σ n K hn hK

theorem hillGapRoot_eq_Dirichlet_of_closed (q : RealPeriodOneHillPotential)
    (σ : ℕ → ℝ) (hσ : σ ∈ hillGapRootBox q.val q.property.1 q.property.2) (k : ℕ)
    (hclosed : hillRealGapHalfLength q.val q.property.1 q.property.2 (k+1) = 0) :
    σ k = hillDirichletEnergy q.val q.property.1 q.property.2 (k+1) (by omega) := by
  have hs := hσ k
  have hμ := hillDirichletEnergy_mem_gap q.val q.property.1 q.property.2 (k+1) (by omega)
  dsimp only [hillRealGapHalfLength] at hclosed
  have hends : hillRealLabels q.val q.property.1 q.property.2 (2*(k+1)) =
      hillRealLabels q.val q.property.1 q.property.2 (2*(k+1)-1) := by linarith
  rw [hends] at hs hμ
  exact (le_antisymm hs.2 hs.1).trans (le_antisymm hμ.2 hμ.1).symm

end NLS.KdV
