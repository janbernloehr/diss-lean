import NLS.MKdV.HierarchyRestriction
import NLS.MKdV.MiuraL2Actions
import NLS.ZakharovShabat.SourceWeightedZeroLaurentAnalytic
import NLS.ZakharovShabat.SourceHigherSobolevHigherActionBound
import NLS.SequenceSpaces.Multiplier

/-! # The full physical action sequence in its native weighted topology

The positive actions have weight (1+n)^(2s+1) at scalar Sobolev order s.
The actual Laurent integrals give all coordinates on one complex source
neighborhood. Uniform weighted l1 bounds prove Banach analyticity, with
closed gaps and zero mean included. Negative and central entries are
zero only to encode the original positive-index target inside Z.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraSpectralActionWeight (s : ℕ) : Weight := Weight.sobolev ((2*s+1 : ℕ) : ℝ)

def miuraSobolevActionSource (s : ℕ) : ScalarSobolev s →L[ℂ] CoeffPair 2 :=
  (higherSobolevSourceInclusion s).comp (hierarchyDiagonal s)

@[simp] theorem miuraSobolevActionSource_fst (s : ℕ) (a : ScalarSobolev s) (j : ℤ) :
    (miuraSobolevActionSource s a).fst j = a.val j :=
  higherSobolevSourceInclusion_fst s (a,a) j

@[simp] theorem miuraSobolevActionSource_snd (s : ℕ) (a : ScalarSobolev s) (j : ℤ) :
    (miuraSobolevActionSource s a).snd j = a.val j :=
  higherSobolevSourceInclusion_snd s (a,a) j

private def positiveActionHalfSymbol : Coeff ⊤ :=
  ⟨fun n => if 0 < n then (1/2 : ℂ) else 0,memℓp_infty ⟨1,by
    rintro _ ⟨n,rfl⟩
    change ‖(if 0 < n then (1/2 : ℂ) else 0)‖ ≤ 1
    split_ifs <;> norm_num⟩⟩

def miuraPositiveActionProjection : Coeff 1 →L[ℂ] Coeff 1 := Coeff.multiplierCLM positiveActionHalfSymbol

def miuraSobolevActionSequence (s : ℕ) (a : ScalarSobolev s) :
    WeightedCoeff (miuraSpectralActionWeight s) 1 :=
  (WeightedCoeff.weightIsometry (miuraSpectralActionWeight s) 1).symm
    (miuraPositiveActionProjection (sourceWeightedZeroLaurentSequence (miuraSpectralActionWeight s)
      (miuraSobolevActionSource s) a))

theorem miuraSpectralActionWeight_gap_bound (s : ℕ) (n : ℤ) :
    miuraSpectralActionWeight s n/(1+|(n : ℝ)|) ≤
      ((SpectralWeight.sobolev (s : ℝ) (Nat.cast_nonneg s)) (2*n))^2 := by
  have hn : (1+|(n : ℝ)|) ≠ 0 := by positivity
  rw [miuraSpectralActionWeight,Weight.sobolev_apply,Real.rpow_natCast,pow_succ,mul_div_cancel_right₀ _ hn]
  exact higherAction_higherSobolev_weight_bound s n (2*s) le_rfl

theorem miuraSobolevActionSequence_nonpositive (s : ℕ) (a : ScalarSobolev s)
    (n : ℤ) (hn : ¬ 0 < n) : (miuraSobolevActionSequence s a).val n = 0 := by
  change ((if 0 < n then (1/2 : ℂ) else 0)*
    sourceWeightedZeroLaurentSequence (miuraSpectralActionWeight s) (miuraSobolevActionSource s) a n)/
      (miuraSpectralActionWeight s n : ℂ) = 0
  rw [if_neg hn,zero_mul,zero_div]

theorem exists_local_miuraSobolevActionSequence_analytic (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    ∃ U : Set (ScalarSobolev s), IsOpen U ∧ a ∈ U ∧
      AnalyticOnNhd ℂ (miuraSobolevActionSequence s) U ∧
      ∀ b ∈ U, ∀ n : ℤ, 0 < n → (miuraSobolevActionSequence s b).val n =
        (1/2 : ℂ)*sourceDiagonalLaurentAction (by simp) (by norm_num) n 0 (miuraSobolevActionSource s b) := by
  let L := miuraSobolevActionSource s
  let T := (higherSobolevSourceWeightedPeriodOne s).comp (hierarchyDiagonal s)
  have hTL (b : ScalarSobolev s) : weightedBaseToPair (SpectralWeight.sobolev (s : ℝ) (Nat.cast_nonneg s)) (T b) =
      periodOnePotential (L b) := weightedBaseToPair_higherSobolevSourceWeightedPeriodOne s (b,b)
  have hreal : L a ∈ realDiagonalSourceLocus 2 := by
    constructor
    · intro j
      change (L a).snd j = conj ((L a).fst (-j))
      rw [miuraSobolevActionSource_snd,miuraSobolevActionSource_fst]
      exact ha j
    · ext j
      exact (miuraSobolevActionSource_fst s a j).trans (miuraSobolevActionSource_snd s a j).symm
  obtain ⟨U,hU,haU,he,hseq⟩ := exists_local_sourceWeightedZeroLaurentSequence_analytic
    (SpectralWeight.sobolev (s : ℝ) (Nat.cast_nonneg s)) (miuraSpectralActionWeight s)
    (fun n => (miuraSpectralActionWeight s).positive n |>.le)
    (miuraSpectralActionWeight_gap_bound s) L T hTL a hreal
  refine ⟨U,hU,haU,?_,?_⟩
  · intro b hb
    exact (((WeightedCoeff.weightIsometry (miuraSpectralActionWeight s) 1).symm.toContinuousLinearEquiv.analyticAt _).comp
      ((miuraPositiveActionProjection.analyticAt _).comp (hseq b hb)))
  · intro b hb n hn
    change ((if 0 < n then (1/2 : ℂ) else 0)*sourceWeightedZeroLaurentSequence (miuraSpectralActionWeight s) L b n)/
      (miuraSpectralActionWeight s n : ℂ) = _
    rw [if_pos hn,he b hb n,if_neg (ne_of_gt hn)]
    calc
      _ = (miuraSpectralActionWeight s n : ℂ)*
          ((1/2 : ℂ)*sourceDiagonalLaurentAction (by simp) (by norm_num) n 0 (L b))/
            (miuraSpectralActionWeight s n : ℂ) := by ring
      _ = _ := mul_div_cancel_left₀ _ ((miuraSpectralActionWeight s).complex_ne_zero n)

theorem exists_miuraSobolevActionSequence_domain (s : ℕ) :
    ∃ U : Set (ScalarSobolev s), IsOpen U ∧
      {a | ∀ j, a.val j = conj (a.val (-j))} ⊆ U ∧
      AnalyticOnNhd ℂ (miuraSobolevActionSequence s) U ∧
      ∀ b ∈ U, ∀ n : ℤ, 0 < n → (miuraSobolevActionSequence s b).val n =
        (1/2 : ℂ)*sourceDiagonalLaurentAction (by simp) (by norm_num) n 0 (miuraSobolevActionSource s b) := by
  let R := {a : ScalarSobolev s // ∀ j, a.val j = conj (a.val (-j))}
  have hlocal (a : R) := exists_local_miuraSobolevActionSequence_analytic s a.val a.property
  choose V hV haV hA hcoord using hlocal
  refine ⟨⋃ a : R, V a,isOpen_iUnion hV,?_,?_,?_⟩
  · intro a ha
    exact mem_iUnion.mpr ⟨⟨a,ha⟩,haV ⟨a,ha⟩⟩
  · intro b hb
    obtain ⟨a,ha⟩ := mem_iUnion.mp hb
    exact hA a b ha
  · intro b hb
    obtain ⟨a,ha⟩ := mem_iUnion.mp hb
    exact hcoord a b ha

end NLS.MKdV
