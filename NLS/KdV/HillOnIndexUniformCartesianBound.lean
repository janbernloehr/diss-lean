import NLS.KdV.HillOnIndexUniformCorrectionBound

/-! A uniform diagonal Cartesian bound in the ACTUAL frequency data.
This retains the physical AUXILIARY divisor and sheet. Conversion to
original Hill energy weights is the next separate estimate. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem norm_physicalOnIndexCartesian_le_of_phase_bounds (P : HillProductEquationPatch)
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource)
    (C : ℝ)
    (hp : ‖Complex.exp (I*P.physicalOnIndexAbelianCorrection n q)‖ ≤ C)
    (hm : ‖Complex.exp (-I*P.physicalOnIndexAbelianCorrection n q)‖ ≤ C) :
    ‖P.physicalOnIndexCartesianPlus n q‖ ≤ 8*C*
      ‖sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)‖*
      (‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)‖+
        ‖P.physicalDirichletFrequency ((n:ℕ):ℤ) q-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)‖) ∧
    ‖P.physicalOnIndexCartesianMinus n q‖ ≤ 8*C*
      ‖sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)‖*
      (‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)‖+
        ‖P.physicalDirichletFrequency ((n:ℕ):ℤ) q-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)‖) := by
  let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)
  let d := P.physicalDirichletFrequency ((n:ℕ):ℤ) q-τ
  let g := ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi q) ((n:ℕ):ℤ)‖
  let r := P.physicalDirichletRootCoefficient n q
  have hr : ‖r‖ ≤ ‖d‖+g/2 := P.norm_physicalDirichletRootCoefficient_le n q hq
  have hs : ‖d-r‖ ≤ 2*(g+‖d‖) ∧ ‖d+r‖ ≤ 2*(g+‖d‖) := by
    have hg : 0 ≤ g := norm_nonneg _
    constructor
    · exact (norm_sub_le _ _).trans (by linarith)
    · exact (norm_add_le _ _).trans (by linarith)
  have hbound (s e : ℂ) (hs : ‖s‖ ≤ 2*(g+‖d‖)) (he : ‖Complex.exp e‖ ≤ C) :
      ‖(-4:ℂ)*τ*s*Complex.exp e‖ ≤ 8*C*‖τ‖*(g+‖d‖) := by
    have hfour : ‖(-4:ℂ)‖ = 4 := by norm_num
    simp only [norm_mul,hfour]
    calc
      _ ≤ (4*‖τ‖*(2*(g+‖d‖)))*C :=
        mul_le_mul (mul_le_mul_of_nonneg_left hs (by positivity)) he (norm_nonneg _) (by positivity)
      _ = _ := by ring
  exact ⟨hbound (d-r) _ hs.1 hp,hbound (d+r) _ hs.2 hm⟩

theorem exists_local_uniform_physicalOnIndexCartesian_frequency_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.physicalDirichletSource ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n : ℕ+,
        ‖P.physicalOnIndexCartesianPlus n a‖ ≤ C*
          ‖sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) ((n:ℕ):ℤ)‖*
          (‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a) ((n:ℕ):ℤ)‖+
            ‖P.physicalDirichletFrequency ((n:ℕ):ℤ) a-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) ((n:ℕ):ℤ)‖) ∧
        ‖P.physicalOnIndexCartesianMinus n a‖ ≤ C*
          ‖sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) ((n:ℕ):ℤ)‖*
          (‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a) ((n:ℕ):ℤ)‖+
            ‖P.physicalDirichletFrequency ((n:ℕ):ℤ) a-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) ((n:ℕ):ℤ)‖) := by
  obtain ⟨U,hU,hqU,hUP,C,hC,hphase⟩ := P.exists_local_uniform_physicalOnIndex_phase_exponential_bound H q hq
  refine ⟨U,hU,hqU,hUP,8*C,by positivity,?_⟩
  intro a ha n
  have h := hphase a ha n
  exact P.norm_physicalOnIndexCartesian_le_of_phase_bounds n a (hUP ha) C h.1 h.2

end NLS.KdV.HillProductEquationPatch
