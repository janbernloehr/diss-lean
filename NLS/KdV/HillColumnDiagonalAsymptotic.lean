import NLS.KdV.HillWeightedColumnIndexRatios
import NLS.ZakharovShabat.SourcePsiMovingRowRatios

/-! For each fixed numerator index, the actual regular weighted
column tends to minus one along any points in the original row discs,
provided the literal omitted-root quotients tend to one there. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillWeightedColumnGapNumerator_tendsto_of_quotient
    {V : Set (CoeffPair 2)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (ψ : CoeffPair 2) (hψ : ψ ∈ V) (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2)
    (hplace : ∀ k : ℤ, hillIndependentFrequency (c,d) k ∈ D k)
    (n : ℕ+) (z : ℕ → ℂ) (hz : ∀ j : ℕ, z j ∈ D ((j:ℤ)+1))
    (hquot : Tendsto (fun j : ℕ => sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num)
      ((j:ℤ)+1) (z j,(hillIndependentFrequencyDisplacement (c,d),ψ))) atTop (𝓝 1)) :
    Tendsto (fun j => hillPeriodEquationWeight n ⟨j+1,by omega⟩*
      hillProductColumnGapNumerator n ⟨j+1,by omega⟩ c ψ ((j:ℤ)+1) d (z j)) atTop (𝓝 (-1)) := by
  let a := hillIndependentFrequencyDisplacement (c,d)
  have ha : a ∈ sourcePsiOriginalRootPlacement (p := 2) D := hplace
  have h1 := hD.tendsto_indexRatio_of_spacing (fun _ => a) (fun _ => ha)
    (fun j => -((j:ℤ)+1)) (fun j => (j:ℤ)+1) z hz tendsto_norm_negative_positive_index_spacing
  have h2 := hD.tendsto_indexRatio_of_spacing (fun _ => a) (fun _ => ha)
    (fun _ => ((n:ℕ):ℤ)) (fun j => (j:ℤ)+1) z hz (tendsto_norm_fixed_sub_positive_index ((n:ℕ):ℤ))
  have h3 := hD.tendsto_indexRatio_of_spacing (fun _ => a) (fun _ => ha)
    (fun _ => -((n:ℕ):ℤ)) (fun j => (j:ℤ)+1) z hz (tendsto_norm_fixed_sub_positive_index (-((n:ℕ):ℤ)))
  have hlim := ((h1.neg.mul h2).mul h3).mul hquot
  simp only [mul_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (n:ℕ)] with j hj
  let m : ℕ+ := ⟨j+1,by omega⟩
  have hmn : m ≠ n := by intro he; have h := congrArg (fun k : ℕ+ => (k:ℕ)) he; change j+1 = (n:ℕ) at h; omega
  have hm : ((m:ℕ):ℤ) = (j:ℤ)+1 := by simp [m]
  have hother : z j ∈ sourceStandardRootOmittedDomain (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ) := by
    intro k hkm hzk
    exact Set.disjoint_left.mp (hD.disjoint ((m:ℕ):ℤ) k hkm.symm)
      (by rw [hm]; exact hz j) (hD.gap ψ hψ k hzk)
  have he := hillWeightedColumnGapNumerator_eq_indexRatios hD ψ c d hplace n m hmn (z j)
    (subset_closure (by rw [hm]; exact hz j)) hother
  simpa only [hm,a] using he.symm

end NLS.KdV
