import NLS.ZakharovShabat.SourceSection20Original
import NLS.ZakharovShabat.SourcePrimitivePowerLemma21_1

/-! # Original Section 21 primitive-power moment domain

An open connected neighborhood retains the original Section 20 family and
Section 19 primitive. Its primitive-power atlas carries one local bound
chosen before every index and natural moment order.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s}

/-- Primitive-power moments on a connected subdomain of the retained
original Section 20 neighborhood. -/
structure SourceSection21MomentData (Q : SourceSection20Data D A B U)
    {Wp : Set (CoeffPair p)} (P : SourcePrimitivePowerAtlas hp hp1 Wp)
    (T : Set (CoeffPair p)) : Prop where
  source_open : IsOpen T
  connected : IsConnected T
  real_subset : realTypeSourceLocus p ⊆ T
  source_subset : T ⊆ U
  power_subset : T ⊆ P.domain
  locally_uniform : ∀ φ ∈ T, ∃ r : ℝ, 0 < r ∧ ball φ r ⊆ T ∧ ∃ C : ℝ, 0 < C ∧
    ∀ ψ ∈ ball φ r, ∀ (n : ℤ) (m : ℕ), ‖P.moment n m ψ‖ ≤ C^m *
      ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖^(m+1)

/-- Attach the actual primitive-power atlas to any chosen original Section 20 family. -/
theorem SourceSection20Data.exists_section21_moments (Q : SourceSection20Data D A B U) :
    ∃ Wp : Set (CoeffPair p), ∃ P : SourcePrimitivePowerAtlas hp hp1 Wp,
      ∃ T : Set (CoeffPair p), SourceSection21MomentData Q P T := by
  obtain ⟨Wp,_,_,⟨P⟩⟩ := exists_sourcePrimitivePowerAtlas hp hp1
  obtain ⟨T₀,ho,_,hr,hp,hb⟩ := P.exists_almostReal_all_moments_power_bound
  let T := connectedComponentIn (T₀ ∩ U) (0 : CoeffPair p)
  have hT : IsOpen T := (ho.inter Q.source_open).connectedComponentIn
  have hsub : T ⊆ T₀ ∩ U := connectedComponentIn_subset _ _
  have hz : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  refine ⟨Wp,P,T,{
    source_open := hT
    connected := isConnected_connectedComponentIn_iff.mpr ⟨hr hz,Q.real_subset hz⟩
    real_subset := isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hz
      (fun ψ hψ => ⟨hr hψ,Q.real_subset hψ⟩)
    source_subset := fun ψ hψ => (hsub hψ).2
    power_subset := fun ψ hψ => hp (hsub hψ).1
    locally_uniform := ?_
  }⟩
  intro φ hφ
  obtain ⟨r,hr,_,C,hC,hb⟩ := hb φ (hsub hφ).1
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds hφ)
  refine ⟨min r δ,lt_min hr hδ,(ball_subset_ball (min_le_right _ _)).trans hd,C,hC,?_⟩
  exact fun ψ hψ => hb ψ (ball_subset_ball (min_le_left _ _) hψ)

end NLS.ZakharovShabat
