import NLS.KdV.HillWeightedColumnNumeratorBound
import NLS.ZakharovShabat.SourcePsiOriginalIndexRatio

/-! The regular weighted diagonal column is exactly minus three
original index ratios times the literal omitted-root quotient. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillWeightedColumnGapNumerator_eq_indexRatios
    {V : Set (CoeffPair 2)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (ψ : CoeffPair 2) (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2)
    (hplace : ∀ k : ℤ, hillIndependentFrequency (c,d) k ∈ D k)
    (n m : ℕ+) (hmn : m ≠ n) (z : ℂ) (hz : z ∈ closure (D ((m:ℕ):ℤ)))
    (hother : z ∈ sourceStandardRootOmittedDomain (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ)) :
    hillPeriodEquationWeight n m*hillProductColumnGapNumerator n m c ψ ((m:ℕ):ℤ) d z =
      -sourcePsiOriginalIndexRatio (-((m:ℕ):ℤ)) ((m:ℕ):ℤ) (hillIndependentFrequencyDisplacement (c,d)) z*
        sourcePsiOriginalIndexRatio ((n:ℕ):ℤ) ((m:ℕ):ℤ) (hillIndependentFrequencyDisplacement (c,d)) z*
        sourcePsiOriginalIndexRatio (-((n:ℕ):ℤ)) ((m:ℕ):ℤ) (hillIndependentFrequencyDisplacement (c,d)) z*
        sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) ((m:ℕ):ℤ)
          (z,(hillIndependentFrequencyDisplacement (c,d),ψ)) := by
  let b := hillIndependentFrequencyDisplacement (c,d)
  let bn := hillIndependentFrequency (c,d) ((n:ℕ):ℤ)
  let bm := hillIndependentFrequency (c,d) ((m:ℕ):ℤ)
  have hmn' : ((m:ℕ):ℤ) ≠ ((n:ℕ):ℤ) := by
    intro h
    exact hmn (Subtype.ext (Int.ofNat.inj h))
  have hs := hD.weighted_separation_closure ((n:ℕ):ℤ) ((m:ℕ):ℤ) hmn'
    (hillIndependentFrequency (c,d) ((n:ℕ):ℤ)) (hplace _) z hz
  have hnz : bn-z ≠ 0 := sub_ne_zero.mpr hs.1.symm
  have hnp : bn+z ≠ 0 := (hillIndependent_multiplier_bound hD (c,d) hplace n m z hz).1
  have hmp : bm+z ≠ 0 := (hillIndependent_multiplier_bound hD (c,d) hplace m m z hz).1
  have ho := sourceStandardRootOmittedProduct_ne_zero (by norm_num) (by norm_num) ψ z ((m:ℕ):ℤ) hother
  have hn : ((n:ℕ):ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hf := hillEnergyProductCoordinateDerivative_frequency_filled n m hmn c d z
  change (bn-z)*(bn+z)*(bm+z)*z*hillEnergyProductCoordinateDerivative n m (z^2-c,d) =
    -((Real.pi:ℂ)*(n:ℕ))^2*(m:ℕ)*jointDeletedSingleSpectralProduct ((m:ℕ):ℤ) (z,b) at hf
  unfold sourcePsiOriginalIndexRatio
  rw [show displacedRoots (hillIndependentFrequencyDisplacement (c,d)) (-((m:ℕ):ℤ)) = -bm from
    hillIndependentFrequency_neg (c,d) ((m:ℕ):ℤ),
    show displacedRoots (hillIndependentFrequencyDisplacement (c,d)) (-((n:ℕ):ℤ)) = -bn from
      hillIndependentFrequency_neg (c,d) ((n:ℕ):ℤ)]
  change hillPeriodEquationWeight n m*(z*hillEnergyProductCoordinateDerivative n m (z^2-c,d)/
    sourceStandardRootOmittedProduct (by norm_num) (by norm_num) ((m:ℕ):ℤ) ψ z) =
    -((Real.pi:ℂ)*((-((m:ℕ):ℤ)-((m:ℕ):ℤ):ℤ):ℂ)/(-bm-z))*
      ((Real.pi:ℂ)*((((n:ℕ):ℤ)-((m:ℕ):ℤ):ℤ):ℂ)/(bn-z))*
      ((Real.pi:ℂ)*((-((n:ℕ):ℤ)-((m:ℕ):ℤ):ℤ):ℂ)/(-bn-z))*
      (jointDeletedSingleSpectralProduct ((m:ℕ):ℤ) (z,b)/
        sourceStandardRootOmittedProduct (by norm_num) (by norm_num) ((m:ℕ):ℤ) ψ z)
  have hmneg : -bm-z ≠ 0 := by rw [show -bm-z = -(bm+z) by ring,neg_ne_zero]; exact hmp
  have hnneg : -bn-z ≠ 0 := by rw [show -bn-z = -(bn+z) by ring,neg_ne_zero]; exact hnp
  unfold hillPeriodEquationWeight
  push_cast
  field_simp [ho,hn,hp,hnz,hmneg,hnneg]
  linear_combination (2*(((n:ℕ):ℂ)^2-((m:ℕ):ℂ)^2))*hf

end NLS.KdV
