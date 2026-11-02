import NLS.MKdV.MiuraSobolevNLSCoordinates
import NLS.MKdV.MiuraL2CartesianSequence
import NLS.ZakharovShabat.SourceDiagonalActionRootSequence
import NLS.SequenceSpaces.AnalyticPhaseTrajectory

/-! # Native analytic Cartesian maps at every integer Sobolev order

The same original Cartesian variables are realized in the weighted Hilbert
pair of order s+1/2 for every integer s>=0. A bounded analytic scaling
symbol multiplies the actual native weighted NLS coordinates. All raw
coefficients survive, including closed selected gaps and zero mean.
-/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraCartesianWeight (s : ℕ) : Weight := Weight.sobolev ((s : ℝ)+1/2)

theorem miuraCartesianWeight_factor (s : ℕ) (n : ℤ) :
    miuraCartesianWeight s n = Weight.sobolev (s : ℝ) n*Weight.sobolev (1/2) n := by
  rw [miuraCartesianWeight,Weight.sobolev_apply,Real.rpow_add (by positivity)]
  rfl

theorem miuraSobolevActionSource_eq_L2_diagonal (s : ℕ) (a : ScalarSobolev s) :
    miuraSobolevActionSource s a = scalarL2Diagonal (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext j
  · change (miuraSobolevActionSource s a).fst j = (scalarL2Diagonal _).fst j
    rw [miuraSobolevActionSource_fst,scalarL2Diagonal_fst,hierarchySobolevJetL2_apply,pow_zero,one_mul]
  · change (miuraSobolevActionSource s a).snd j = (scalarL2Diagonal _).snd j
    rw [miuraSobolevActionSource_snd,scalarL2Diagonal_snd,hierarchySobolevJetL2_apply,pow_zero,one_mul]

def miuraSobolevCartesianSequence (s : ℕ) (a : ScalarSobolev s) :
    WeightedCoeff (miuraCartesianWeight s) 2 × WeightedCoeff (miuraCartesianWeight s) 2 :=
  let m := sourceDiagonalActionRootSequence (miuraSobolevActionSource s a)
  let z := miuraSobolevNLSNormalizedCoordinates s a
  ((WeightedCoeff.weightIsometry (miuraCartesianWeight s) 2).symm (Coeff.multiplier m z.1),
   (WeightedCoeff.weightIsometry (miuraCartesianWeight s) 2).symm (-(Coeff.multiplier m z.2)))

/-- Native Banach analyticity and exact original Cartesian coefficients
on one complex source neighborhood at every integer Sobolev order. -/
theorem exists_local_miuraSobolevCartesianSequence_analytic
    (s : ℕ) (a : ScalarSobolev s) (ha : ∀ j, a.val j = conj (a.val (-j))) :
    ∃ U : Set (ScalarSobolev s), IsOpen U ∧ a ∈ U ∧
      AnalyticOnNhd ℂ (miuraSobolevCartesianSequence s) U ∧
      ∀ b ∈ U, ∀ n : ℤ,
        ((miuraSobolevCartesianSequence s b).1.val n,(miuraSobolevCartesianSequence s b).2.val n) =
          miuraL2CartesianCoefficient (hierarchySobolevJetL2 s 0 (Nat.zero_le s) b) n := by
  have hraw : ∀ j, hierarchySobolevJetL2 s 0 (Nat.zero_le s) a j =
      conj (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a (-j)) := by
    intro j
    simpa only [hierarchySobolevJetL2_apply,pow_zero,one_mul] using ha j
  let φ : realDiagonalSourceLocus 2 :=
    ⟨miuraSobolevActionSource s a,by
      rw [miuraSobolevActionSource_eq_L2_diagonal]
      exact scalarL2Diagonal_realDiagonal _ hraw⟩
  obtain ⟨A,hA,hφA,hmA,hmcoord⟩ := exists_local_sourceDiagonalActionRootSequence_analytic φ
  obtain ⟨B,hB,hrealB,hzA,hzcoord⟩ := exists_miuraSobolevNLSNormalizedCoordinates_domain s
  let U := miuraSobolevActionSource s ⁻¹' A ∩ B
  have hU : IsOpen U := (hA.preimage (miuraSobolevActionSource s).continuous).inter hB
  refine ⟨U,hU,⟨hφA,hrealB ha⟩,?_,?_⟩
  · intro b hb
    have hm := (hmA _ hb.1).comp ((miuraSobolevActionSource s).analyticAt b)
    have hz := hzA b hb.2
    have hx := ((Coeff.multiplierBilinear (p := 2)).analyticAt_bilinear _).comp₂ hm (analyticAt_fst.comp hz)
    have hy := ((Coeff.multiplierBilinear (p := 2)).analyticAt_bilinear _).comp₂ hm (analyticAt_snd.comp hz)
    exact (((WeightedCoeff.weightIsometry (miuraCartesianWeight s) 2).symm.toContinuousLinearEquiv.analyticAt _).comp hx).prod
      (((WeightedCoeff.weightIsometry (miuraCartesianWeight s) 2).symm.toContinuousLinearEquiv.analyticAt _).comp hy.neg)
  · intro b hb n
    have hm := hmcoord _ hb.1 n
    obtain ⟨hx,hy⟩ := hzcoord b hb.2 n
    have hw := miuraCartesianWeight_factor s n
    by_cases hn : 0 < n
    · have hi : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
      rw [sourceDiagonalScaledActionRoot,if_pos hn] at hm
      have hsource := miuraSobolevActionSource_eq_L2_diagonal s b
      apply Prod.ext
      · change (sourceDiagonalActionRootSequence (miuraSobolevActionSource s b) n*
          (miuraSobolevNLSNormalizedCoordinates s b).1 n)/(miuraCartesianWeight s n : ℂ) =
            (miuraL2CartesianCoefficient _ n).1
        rw [hm,hx,hw,miuraL2CartesianCoefficient,if_pos hn]
        dsimp only [miuraL2CartesianCoordinates]
        rw [hi,← hsource]
        push_cast
        apply (div_eq_iff (mul_ne_zero ((Weight.sobolev (s : ℝ)).complex_ne_zero n)
          ((Weight.sobolev (1/2)).complex_ne_zero n))).mpr
        ring
      · change (-(sourceDiagonalActionRootSequence (miuraSobolevActionSource s b) n*
          (miuraSobolevNLSNormalizedCoordinates s b).2 n))/(miuraCartesianWeight s n : ℂ) =
            (miuraL2CartesianCoefficient _ n).2
        rw [hm,hy,hw,miuraL2CartesianCoefficient,if_pos hn]
        dsimp only [miuraL2CartesianCoordinates]
        rw [hi,← hsource]
        push_cast
        apply (div_eq_iff (mul_ne_zero ((Weight.sobolev (s : ℝ)).complex_ne_zero n)
          ((Weight.sobolev (1/2)).complex_ne_zero n))).mpr
        ring
    · rw [sourceDiagonalScaledActionRoot,if_neg hn] at hm
      apply Prod.ext
      · change (sourceDiagonalActionRootSequence (miuraSobolevActionSource s b) n*
          (miuraSobolevNLSNormalizedCoordinates s b).1 n)/(miuraCartesianWeight s n : ℂ) =
            (miuraL2CartesianCoefficient _ n).1
        rw [hm,miuraL2CartesianCoefficient,if_neg hn]
        simp
      · change (-(sourceDiagonalActionRootSequence (miuraSobolevActionSource s b) n*
          (miuraSobolevNLSNormalizedCoordinates s b).2 n))/(miuraCartesianWeight s n : ℂ) =
            (miuraL2CartesianCoefficient _ n).2
        rw [hm,miuraL2CartesianCoefficient,if_neg hn]
        simp

theorem exists_miuraSobolevCartesianSequence_domain (s : ℕ) :
    ∃ U : Set (ScalarSobolev s), IsOpen U ∧ {a | ∀ j, a.val j = conj (a.val (-j))} ⊆ U ∧
      AnalyticOnNhd ℂ (miuraSobolevCartesianSequence s) U ∧
      ∀ b ∈ U, ∀ n : ℤ,
        ((miuraSobolevCartesianSequence s b).1.val n,(miuraSobolevCartesianSequence s b).2.val n) =
          miuraL2CartesianCoefficient (hierarchySobolevJetL2 s 0 (Nat.zero_le s) b) n := by
  let R := {a : ScalarSobolev s // ∀ j, a.val j = conj (a.val (-j))}
  have hlocal (a : R) := exists_local_miuraSobolevCartesianSequence_analytic s a.val a.property
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
