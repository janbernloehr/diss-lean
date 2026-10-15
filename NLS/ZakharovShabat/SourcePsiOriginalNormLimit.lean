import NLS.ZakharovShabat.SourceEquation2_29
import NLS.ZakharovShabat.SourcePsiJacobianDiagonalNormLimit
import NLS.SequenceSpaces.ReciprocalMatrixConvergence

/-!
# Operator-norm convergence on the original real root domain

Real root inputs suffice for the escaping diagonal estimate; gap placement
is unnecessary. The actual original off-diagonal matrices share one lp
reciprocal majorant at every placed input. Combining the two norm limits
proves Qn → Q* throughout the original real domain, in both index directions.
This is convergence at each fixed input, with no fixed-neighborhood claim.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Distant diagonal corrections are eventually uniformly small for any fixed
real root input, even without original disk placement. -/
theorem SourceLemma12_4Data.originalFullRootJacobian_diagonal_uniformTail
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (φ : CoeffPair p) (hφW : φ ∈ W)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (haReal : ∀ k : ℤ, (a k).im = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ,
      ∀ᶠ n : ℤ in Filter.comap Int.natAbs atTop,
        ∀ m : ℤ, K ≤ m.natAbs →
          ‖(sourcePsiOriginalFullRootJacobian hp hp1 n a φ (lp.single p m 1)) m-2‖ < ε := by
  obtain ⟨c,R,hc,hgeom,_,_,_,_,K,hfree,hmatrix⟩ :=
    exists_common_sourcePsi_fullJacobian_uniformNorm_entryLimit_realCentered hp hp1 a φ hφ
  have htail := sourcePsiFullRootJacobian_diagonal_uniformTail_of_real_roots
    hp hp1 a φ hφ haReal c R K hfree hmatrix
  simpa only [H.originalFullRootJacobian_eq_selected φ hφW hφ c R ⟨hc,hgeom⟩] using htail

/-- One fixed lp sequence bounds every original off-diagonal entry, including
the finite head and the omitted row and column. -/
theorem SourceLemma12_4Data.originalFullRootJacobian_offDiagonal_majorant
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D) :
    ∃ B : Coeff p, ∀ n m k : ℤ, k ≠ m →
      ‖(sourcePsiOriginalFullRootJacobian hp hp1 n a φ (lp.single p k 1)) m‖ ≤
        ‖B m‖/|((k-m:ℤ):ℝ)| := by
  obtain ⟨U,_,hbase,_,C,_,hb⟩ := H.originalJacobian_offDiagonal_commonMajorant hW hD hV φ hφW hφV a
  obtain ⟨B,_,hB⟩ := hb (a,φ) hbase hφ ha
  refine ⟨B,?_⟩
  intro n m k hkm
  by_cases hmn : m = n
  · subst m
    simp [sourcePsiOriginalFullRootJacobian,Coeff.deletedJacobianExtension,Pi.single_eq_of_ne hkm.symm]
    positivity
  rw [sourcePsiOriginalFullRootJacobian_entry hp hp1 n m k hmn]
  have hden : ‖((m-k:ℤ):ℂ)‖ = |((k-m:ℤ):ℝ)| := by
    rw [Complex.norm_intCast]
    simp only [Int.cast_sub,abs_sub_comm]
  have hpos : 0 < |((k-m:ℤ):ℝ)| := abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr hkm)
  apply (le_div_iff₀ hpos).mpr
  simpa only [norm_mul,hden,mul_comm] using hB n m k hkm.symm

/-- The original off-diagonal operators converge in norm for every placed
complex root input at a real-type source. -/
theorem SourceLemma12_4Data.originalFullRootJacobian_offDiagonal_tendsto
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D) :
    Tendsto (fun n : ℤ => Coeff.operatorOffDiagonal (sourcePsiOriginalFullRootJacobian hp hp1 n a φ))
      (Filter.comap Int.natAbs atTop) (𝓝 (Coeff.operatorOffDiagonal (sourcePsiOriginalLimitOperator hp hp1 a φ))) := by
  obtain ⟨B,hB⟩ := H.originalFullRootJacobian_offDiagonal_majorant hW hD hV φ hφW hφV hφ a ha
  exact Coeff.tendsto_offDiagonal_of_coordinatewise_and_reciprocalEntries hp hp1 _ _
    (H.originalLimitOperator_spec hD φ hφW hφV hφ a ha) B hB

/-- The actual full original Jacobians converge in operator norm at every
real placed root input, without requiring the roots to lie in the gaps. -/
theorem SourceLemma12_4Data.originalFullRootJacobian_tendsto
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (haReal : ∀ k : ℤ, (a k).im = 0) :
    Tendsto (fun n : ℤ => sourcePsiOriginalFullRootJacobian hp hp1 n a φ)
      (Filter.comap Int.natAbs atTop) (𝓝 (sourcePsiOriginalLimitOperator hp hp1 a φ)) := by
  let l : Filter ℤ := Filter.comap Int.natAbs atTop
  let : NeBot l := (inferInstance : NeBot (atTop : Filter ℕ)).comap_of_surj Int.natAbs_surjective
  have hdiag := Coeff.tendsto_operatorDiagonalMultiplier_of_uniform_constantTail l
    (fun n => sourcePsiOriginalFullRootJacobian hp hp1 n a φ) (sourcePsiOriginalLimitOperator hp hp1 a φ) 2
    (fun m => H.originalLimitOperator_spec hD φ hφW hφV hφ a ha (lp.single p m 1) m)
    (H.originalFullRootJacobian_diagonal_uniformTail φ hφW hφ a haReal)
  have hoff := H.originalFullRootJacobian_offDiagonal_tendsto hW hD hV φ hφW hφV hφ a ha
  simpa only [← Coeff.operator_eq_diagonal_add_offDiagonal] using hdiag.add hoff

end NLS.ZakharovShabat
