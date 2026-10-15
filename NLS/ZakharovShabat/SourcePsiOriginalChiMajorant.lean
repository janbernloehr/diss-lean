import NLS.ZakharovShabat.SourcePsiOriginalFamilyQuotient
import NLS.ZakharovShabat.SourcePsiOriginalChi
import NLS.ZakharovShabat.SourcePsiOriginalIndexRatio

/-!
# Equation (2.32) on every original disk at every complex source

The original disk separation controls the omitted midpoint denominator.
Combining its reciprocal-lattice error with the actual family quotient
majorant gives one lp bound independent of the omitted index, locally
throughout the unchanged complex domain, on the full original disks.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
variable {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n} {D : ℤ → Set ℂ} {c : ℝ}

/-- The midpoint denominator obeys the original reciprocal-distance bound. -/
theorem SourceIsolatingNeighborhoods.original_midpointRatio_bounds
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ V, ∀ n m : ℤ, m ≠ n → ∀ z ∈ D m,
      ‖((Real.pi:ℂ)*((n-m:ℤ):ℂ))/(sourceStandardRootMidpoint hp hp1 ψ n-z)‖ ≤ Real.pi*c ∧
      ‖((Real.pi:ℂ)*((n-m:ℤ):ℂ))/(sourceStandardRootMidpoint hp hp1 ψ n-z)-1‖ ≤
        K/‖((n-m:ℤ):ℂ)‖ := by
  obtain ⟨K,hK,hb⟩ := hD.original_indexRatio_uniform_bound
  refine ⟨K,hK,?_⟩
  intro ψ hψ n m hmn z hz
  let τ := sourcePeriodicMidpointDisplacement hp hp1 ψ
  have he (k : ℤ) : displacedRoots τ k = sourceStandardRootMidpoint hp hp1 ψ k := by
    simp only [τ,displacedRoots,sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint]
    ring
  have hτ : τ ∈ sourcePsiOriginalRootPlacement D := by
    intro k
    rw [he k]
    exact hD.gap ψ hψ k (sourcePeriodicMidpoint_mem_segment hp hp1 ψ k)
  constructor
  · have hsep := hD.weighted_separation_closure n m hmn _
      (hD.gap ψ hψ n (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)) z (subset_closure hz)
    rw [norm_div,norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hsep.2 Real.pi_pos.le
  · simpa only [sourcePsiOriginalIndexRatio,he n] using hb τ hτ n m hmn z hz

/-- Every original chi error admits a full lp majorant with an index-independent norm. -/
theorem SourceLemma12_11Data.original_allDisk_chi_errorBound
    (H : SourceLemma12_11Data hp hp1 W₀ W s)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (hψV : ψ ∈ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ ψ ∈ U ∧ U ⊆ W ∩ V ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ χ ∈ U, ∀ n : ℤ, ∃ E : Coeff p, ‖E‖ ≤ C ∧
        ∀ m : ℤ, m ≠ n → ∀ z ∈ D m,
          ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n χ) χ z-I‖ ≤ ‖E m‖ := by
  obtain ⟨U,hU,hψU,hUV,C,hC,hquot⟩ := H.original_allDisk_quotient_errorBound hD hV ψ hψ hψV
  obtain ⟨K,hK,hratio⟩ := hD.original_midpointRatio_bounds
  have hc : 0 ≤ c := zero_le_one.trans hD.one_le
  let A := Real.pi*c
  have hA : 0 ≤ A := mul_nonneg Real.pi_pos.le hc
  refine ⟨U,hU,hψU,hUV,A*C+K*‖Coeff.puncturedLattice p hp1‖,by positivity,?_⟩
  intro χ hχ n
  obtain ⟨B,hB,_,hb⟩ := hquot χ hχ n
  let L := Coeff.shift n (Coeff.puncturedLattice p hp1)
  let E : Coeff p := (A:ℂ) • Coeff.magnitude B+(K:ℂ) • Coeff.magnitude L
  have hEpoint (m : ℤ) : ‖E m‖ = A*‖B m‖+K*‖L m‖ := by
    simp only [E,lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,Coeff.magnitude_apply,smul_eq_mul,
      ← Complex.ofReal_mul,← Complex.ofReal_add,Complex.norm_real,
      Real.norm_of_nonneg (by positivity : 0 ≤ A*‖B m‖+K*‖L m‖)]
  refine ⟨E,?_,?_⟩
  · calc
      ‖E‖ ≤ ‖(A:ℂ) • Coeff.magnitude B‖+‖(K:ℂ) • Coeff.magnitude L‖ := norm_add_le _ _
      _ = A*‖B‖+K*‖Coeff.puncturedLattice p hp1‖ := by
        simp only [norm_smul,Coeff.norm_magnitude,Complex.norm_real,Real.norm_of_nonneg hA,
          Real.norm_of_nonneg hK,L,Coeff.norm_shift]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hB hA) le_rfl
  · intro m hmn z hz
    let r := ((Real.pi:ℂ)*((n-m:ℤ):ℂ))/(sourceStandardRootMidpoint hp hp1 χ n-z)
    let Q := sourceSingleRootQuotientJointProduct hp hp1 m
      (z,(sourcePsiFillDeletedRoot n (s n χ) (sourceStandardRootMidpoint hp hp1 χ n),χ))
    have he : sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n χ) χ z-I =
        I*(r*(Q-1)+(r-1)) := by
      simp only [sourcePsiMidpointFilledRegularFactor,sourcePsiGapRegularFactor,
        displacedRoots_sourcePsiFillDeletedRoot_same]
      dsimp only [r,Q]
      ring
    obtain ⟨hr,hre⟩ := hratio χ (hUV hχ).2 n m hmn z hz
    have hL : ‖L m‖ = ‖((n-m:ℤ):ℂ)‖⁻¹ := by
      simp only [L,Coeff.shift_apply,Coeff.puncturedLattice_apply,if_neg (sub_ne_zero.mpr hmn),
        norm_inv,Int.cast_sub,norm_sub_rev]
    rw [he,norm_mul,norm_I,one_mul,hEpoint,hL]
    calc
      ‖r*(Q-1)+(r-1)‖ ≤ ‖r‖*‖Q-1‖+‖r-1‖ := by
        simpa only [norm_mul] using norm_add_le (r*(Q-1)) (r-1)
      _ ≤ A*‖B m‖+K/‖((n-m:ℤ):ℂ)‖ :=
        add_le_add (mul_le_mul hr (hb m z hz) (norm_nonneg _) hA) hre
      _ = _ := by rw [div_eq_mul_inv]

end NLS.ZakharovShabat
