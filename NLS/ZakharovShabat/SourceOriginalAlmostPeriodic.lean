import NLS.ZakharovShabat.SourceFlowAlmostPeriodic
import NLS.ZakharovShabat.SourceSection22Original

/-! # Almost periodicity for original global NLS solutions

Constructed original data and uniqueness give Bohr almost periodicity
for every global solution in the all-smooth-approximation sense, for
1 < p <= 2. Both solution curves exist for every source in this range.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every global ordinary solution in the original smooth-approximation sense
is Bohr almost periodic in the full source norm when 1 < p ≤ 2. -/
theorem bohrAlmostPeriodic_of_isOrdinaryNLSSolutionOn_univ
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    {φ : realTypeSourceSubmodule p} {γ : ℝ → realTypeSourceSubmodule p}
    (hγ : IsOrdinaryNLSSolutionOn univ φ γ) : Dynamics.BohrAlmostPeriodic γ := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection20_original hp hp1
  have he : γ = A.hamiltonianOrdinarySourceFlow D.complex hp2 φ := by
    funext τ
    exact hγ.eqOn_inter (Q.global_physical_solutions hp2 φ).2 hp hp1
      ⟨mem_univ τ,mem_univ τ⟩
  rw [he]
  exact A.bohrAlmostPeriodic_hamiltonianOrdinarySourceFlow D.complex hp2 φ

/-- The same unconditional recurrence holds for every global renormalized solution. -/
theorem bohrAlmostPeriodic_of_isRenormalizedNLSSolutionOn_univ
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    {φ : realTypeSourceSubmodule p} {γ : ℝ → realTypeSourceSubmodule p}
    (hγ : IsRenormalizedNLSSolutionOn univ φ γ) : Dynamics.BohrAlmostPeriodic γ := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection20_original hp hp1
  have he : γ = A.hamiltonianRenormalizedSourceFlow D.complex hp2 φ := by
    funext τ
    exact hγ.eqOn_inter (Q.global_physical_solutions hp2 φ).1 hp hp1
      ⟨mem_univ τ,mem_univ τ⟩
  rw [he]
  exact A.bohrAlmostPeriodic_hamiltonianRenormalizedSourceFlow D.complex hp2 φ

/-- Every source in the global exponent range has both actual solution curves,
with uniform recurrence in the original norm. No atlas is assumed as input. -/
theorem exists_original_almostPeriodic_solutions
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) :
    ∃ γ γstar : ℝ → realTypeSourceSubmodule p,
      IsOrdinaryNLSSolutionOn univ φ γ ∧ Dynamics.BohrAlmostPeriodic γ ∧
      IsRenormalizedNLSSolutionOn univ φ γstar ∧ Dynamics.BohrAlmostPeriodic γstar := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection20_original hp hp1
  exact ⟨A.hamiltonianOrdinarySourceFlow D.complex hp2 φ,
    A.hamiltonianRenormalizedSourceFlow D.complex hp2 φ,
    (Q.global_physical_solutions hp2 φ).2,
    A.bohrAlmostPeriodic_hamiltonianOrdinarySourceFlow D.complex hp2 φ,
    (Q.global_physical_solutions hp2 φ).1,
    A.bohrAlmostPeriodic_hamiltonianRenormalizedSourceFlow D.complex hp2 φ⟩

end NLS.ZakharovShabat
