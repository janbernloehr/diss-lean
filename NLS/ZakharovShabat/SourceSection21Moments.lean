import NLS.ZakharovShabat.SourceSection21Domain
import NLS.ZakharovShabat.SourcePrimitivePowerHamiltonian

/-! # Lemmas 21.1 and 21.2 for the retained original primitive

The actual power contours use exactly the Section 19 primitive retained
by the Section 20 family. All five moment clauses and the corrected
negative cubic Hamiltonian term hold for these same moments.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s}

namespace SourceSection21MomentData
variable {Q : SourceSection20Data D A B U}
  {Wp T : Set (CoeffPair p)} {P : SourcePrimitivePowerAtlas hp hp1 Wp}
  (E : SourceSection21MomentData Q P T)
include E

/-- One all-index circle family represents every primitive-power moment
using the same primitive as Sections 19 and 20. -/
theorem moment_contours (ψ : CoeffPair p) (hψ : ψ ∈ T) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ, sourcePsiRealCenteredContourFamily hp hp1 ψ c R ∧
      ∀ (n : ℤ) (m : ℕ), P.moment n m ψ = sourcePrimitivePowerCircle hp hp1 B n m ψ (c n) (R n) := by
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp (E.power_subset hψ)
  obtain ⟨L⟩ := (P.localChart φ).charts ψ hφ
  obtain ⟨L'⟩ := Q.charts ψ (E.source_subset hψ)
  obtain ⟨c,R,hC,he⟩ := P.circle_representation ψ (E.power_subset hψ)
  refine ⟨c,R,hC,?_⟩
  intro n m
  exact (he n m).trans (sourcePrimitivePowerCircle_independent_neighborhood hp hp1 Wp B n m
    ψ L L' (c n) (R n) (hC.2 n).1.le (hC.2 n).2.2.2)

/-- All five clauses of Lemma 21.1 on one original-family domain,
including order zero and all-index bounds at complex sources. -/
theorem lemma21_1 :
    (∀ n m, AnalyticOnNhd ℂ (P.moment n m) T) ∧
    (∀ ψ ∈ T, ∀ n m, P.moment n (2*m) ψ = 0) ∧
    (∀ φ ∈ T, ∃ r : ℝ, 0 < r ∧ ball φ r ⊆ T ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ψ ∈ ball φ r, ∀ (n : ℤ) (m : ℕ), ‖P.moment n m ψ‖ ≤ C^m *
        ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖^(m+1)) ∧
    (∀ ψ ∈ T, ∀ n, canonicalPeriodicGap hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0 → ∀ m, P.moment n m ψ = 0) ∧
    (∀ φ : realTypeSourceSubmodule p, ∀ n m,
      0 ≤ (P.moment n m φ.val).re ∧ (P.moment n m φ.val).im = 0) ∧
    (∀ φ : realTypeSourceSubmodule p, ∀ n m, P.moment n (2*m+1) φ.val = 0 ↔
      canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0) ∧
    (∀ n, EqOn (P.moment n 1) (sourceComplexAction hp hp1 n) T) :=
  ⟨fun n m => (P.analytic_moment n m).mono E.power_subset,
    fun ψ hψ => P.moment_even ψ (E.power_subset hψ),E.locally_uniform,
    fun ψ hψ => P.moment_of_collapsed ψ (E.power_subset hψ),
    P.real_moment_nonneg,P.real_odd_moment_eq_zero_iff,fun n => (P.moment_one n).mono E.power_subset⟩

/-- Restriction preserves the moment bounds and the original primitive. -/
theorem restrict (S : Set (CoeffPair p)) (hS : IsOpen S) (hc : IsConnected S)
    (hr : realTypeSourceLocus p ⊆ S) (hST : S ⊆ T) : SourceSection21MomentData Q P S := by
  refine ⟨hS,hc,hr,hST.trans E.source_subset,hST.trans E.power_subset,?_⟩
  intro φ hφ
  obtain ⟨r,hr,_,C,hC,hb⟩ := E.locally_uniform φ (hST hφ)
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hφ)
  exact ⟨min r δ,lt_min hr hδ,(ball_subset_ball (min_le_right _ _)).trans hd,C,hC,
    fun ψ hψ => hb ψ (ball_subset_ball (min_le_left _ _) hψ)⟩

/-- The corrected equation (4.13) uses the negative cubic moment sum. -/
theorem lemma21_2 (φ : realTypeSourceLocus p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ, sourcePsiRealCenteredContourFamily hp hp1 φ.val c R ∧
      (∀ n m, P.moment n m φ.val = sourcePrimitivePowerCircle hp hp1 B n m φ.val (c n) (R n)) ∧
      sourceFiniteGapNLSHamiltonian hp hp1 φ hf 3-2*(sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1)^2-
        (∑' n : ℤ, (2*(n:ℂ)*Real.pi)^2*sourceComplexAction hp hp1 n φ.val) =
          -(4/3:ℂ)*(∑' n : ℤ, P.moment n 3 φ.val) := by
  obtain ⟨c,R,hC,he⟩ := E.moment_contours φ.val (E.real_subset φ.property)
  exact ⟨c,R,hC,he,P.finiteGap_hamiltonian_identity φ hf⟩

end SourceSection21MomentData
end NLS.ZakharovShabat
