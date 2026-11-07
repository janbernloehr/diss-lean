import NLS.KdV.HillIndependentFrequencyLifting
import NLS.ZakharovShabat.BalancedSingleSpectralProducts
import NLS.ZakharovShabat.SourcePsiCandidate

/-! Exact LITERAL cutoff pairing of the independent balanced frequency
product with the Hill energy product, including zero factors. Restoring
the omitted positive energy index restores BOTH signed frequencies. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem singleSpectralPartialProduct_independent_Hill_restore (n : ℕ+) (N : ℕ)
    (hN : (n:ℕ) ≤ N) (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2) (z : ℂ) :
    singleSpectralPartialProduct (hillIndependentFrequency (c,d)) z N =
      -2*z*((hillEnergySequenceZero n d+c-z^2)/((Real.pi:ℂ)*(n:ℕ))^2)*
        hillEnergySequencePartialProduct n N (z^2-c,d) := by
  rw [singleSpectralPartialProduct_eq_of_balanced _ (hillIndependentFrequency_zero (c,d))
    (hillIndependentFrequency_neg (c,d))]
  have hp : (∏ j ∈ Finset.range N,
      ((hillIndependentFrequency (c,d) ((j:ℤ)+1))^2-z^2)/((Real.pi:ℂ)*((j:ℂ)+1))^2) =
      ∏ j ∈ Finset.range N,hillEnergySequenceFactor (z^2-c,d) j := by
    apply Finset.prod_congr rfl
    intro j _
    let m : ℕ+ := ⟨j+1,by omega⟩
    have hj : ((m:ℕ):ℤ) = (j:ℤ)+1 := by
      change ((j+1:ℕ):ℤ) = (j:ℤ)+1
      simp only [Nat.cast_add,Nat.cast_one]
    have hc : ((m:ℕ):ℂ) = (j:ℂ)+1 := by
      change ((j+1:ℕ):ℂ) = (j:ℂ)+1
      simp only [Nat.cast_add,Nat.cast_one]
    rw [← hj,hillIndependentFrequency_positive_sq]
    change (hillEnergySequenceZero m d+c-z^2)/((Real.pi:ℂ)*((j:ℂ)+1))^2 = _
    unfold hillEnergySequenceZero
    rw [hc]
    change ((((Real.pi:ℂ)*((j:ℂ)+1))^2+((j:ℂ)+1)*d m+c-z^2)/
      ((Real.pi:ℂ)*((j:ℂ)+1))^2) =
      (((Real.pi:ℂ)*((j:ℂ)+1))^2+((j:ℂ)+1)*d m-(z^2-c))/
        ((Real.pi:ℂ)*((j:ℂ)+1))^2
    ring
  rw [hp]
  have hmem : (n:ℕ)-1 ∈ Finset.range N := by simp only [Finset.mem_range]; have hn := n.pos; omega
  rw [← Finset.mul_prod_erase (Finset.range N) (hillEnergySequenceFactor (z^2-c,d)) hmem,
    hillEnergySequenceFactor_selected_eq]
  change -2*z*(((hillEnergySequenceZero n d-(z^2-c))/((Real.pi:ℂ)*(n:ℕ))^2)*
    hillEnergySequencePartialProduct n N (z^2-c,d)) = _
  ring

theorem jointSingleSpectralProduct_independent_Hill_restore (n : ℕ+)
    (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2) (z : ℂ) :
    jointSingleSpectralProduct (z,hillIndependentFrequencyDisplacement (c,d)) =
      -2*z*((hillEnergySequenceZero n d+c-z^2)/((Real.pi:ℂ)*(n:ℕ))^2)*
        hillEnergySequenceProduct n (z^2-c,d) := by
  have hs := (tendstoLocallyUniformlyOn_entireSingleSpectralProduct (by norm_num)
    (displacedRoots (hillIndependentFrequencyDisplacement (c,d)))
    (memℓp_displacedRoots (hillIndependentFrequencyDisplacement (c,d)))).tendsto_at (mem_univ z)
  have hp := (tendsto_hillEnergySequencePartialProduct n (z^2-c,d)).const_mul
    (-2*z*((hillEnergySequenceZero n d+c-z^2)/((Real.pi:ℂ)*(n:ℕ))^2))
  have he : ∀ᶠ N : ℕ in atTop,
      -2*z*((hillEnergySequenceZero n d+c-z^2)/((Real.pi:ℂ)*(n:ℕ))^2)*
        hillEnergySequencePartialProduct n N (z^2-c,d) =
      singleSpectralPartialProduct (hillIndependentFrequency (c,d)) z N := by
    filter_upwards [eventually_ge_atTop (n:ℕ)] with N hN
    exact (singleSpectralPartialProduct_independent_Hill_restore n N hN c d z).symm
  exact tendsto_nhds_unique hs (hp.congr' he)

end NLS.KdV
