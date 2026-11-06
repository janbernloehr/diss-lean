import NLS.MKdV.MiuraL2CartesianCoordinates
import NLS.ZakharovShabat.SourceDiagonalActionRootCommonDomain
import NLS.SequenceSpaces.WeightedTwoSequenceBound

/-! # The full analytic Cartesian sequence in the native half-order norm

A common complex neighborhood supports all selected physical action roots
with inverse-square-root frequency decay. Multiplication by the original
NLS coordinate sequences gives actual membership, uniform local bounds,
and Banach analyticity in the full weighted Hilbert target. Nonpositive
entries are zero only to encode the positive-index target inside Z.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraL2CartesianCoefficient (a : Coeff 2) (n : ℤ) : ℂ × ℂ :=
  if 0 < n then miuraL2CartesianCoordinates n.toNat a else 0

def miuraL2CartesianSequence (a : Coeff 2) :
    WeightedCoeff (Weight.sobolev (1/2)) 2 × WeightedCoeff (Weight.sobolev (1/2)) 2 :=
  (WeightedCoeff.ofFunctionOrZero (Weight.sobolev (1/2)) 2 (fun n => (miuraL2CartesianCoefficient a n).1),
   WeightedCoeff.ofFunctionOrZero (Weight.sobolev (1/2)) 2 (fun n => (miuraL2CartesianCoefficient a n).2))

/-- The full native Cartesian map is analytic on an original complex L²
neighborhood and every raw coefficient is the actual selected pair. -/
theorem exists_local_miuraL2CartesianSequence_analytic
    (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ a ∈ U ∧
      AnalyticOnNhd ℂ miuraL2CartesianSequence U ∧
      ∀ b ∈ U, ∀ n : ℤ,
        ((miuraL2CartesianSequence b).1.val n,(miuraL2CartesianSequence b).2.val n) =
          miuraL2CartesianCoefficient b n := by
  let D := miuraActionFlowFamily.data
  let φ : realDiagonalSourceLocus 2 := ⟨scalarL2Diagonal a,scalarL2Diagonal_realDiagonal a ha⟩
  obtain ⟨A,hA,hφA,hr,R,hR,hroot⟩ := exists_local_sourceDiagonalActionRoot_allIndices_analytic_bound φ
  obtain ⟨B,hB,hφB,hBW,M,hM,hmapBound⟩ := D.locally_bounded φ.val (D.real_subset φ.property.1)
  let U := scalarL2Diagonal ⁻¹' (A ∩ B)
  have hU : IsOpen U := (hA.inter hB).preimage scalarL2Diagonal.continuous
  have haU : a ∈ U := ⟨hφA,hφB⟩
  have hcoord (n : ℤ) : AnalyticOnNhd ℂ (fun b => miuraL2CartesianCoefficient b n) U := by
    intro b hb
    by_cases hn : 0 < n
    · have hi : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
      have he : (fun c => miuraL2CartesianCoefficient c n) = miuraL2CartesianCoordinates n.toNat := by
        funext c
        exact if_pos hn
      rw [he]
      have hm := (D.analytic (scalarL2Diagonal b) (hBW hb.2)).comp (scalarL2Diagonal.analyticAt b)
      have hx := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).analyticAt _).comp (analyticAt_fst.comp hm)
      have hy := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).analyticAt _).comp (analyticAt_snd.comp hm)
      have ht := (hr n hn (scalarL2Diagonal b) hb.1).comp (scalarL2Diagonal.analyticAt b)
      change AnalyticAt ℂ (fun c => miuraL2CartesianCoordinates n.toNat c) b
      simpa [miuraL2CartesianCoordinates,hi,Function.comp_def] using! (ht.mul hx).prod ((ht.mul hy).neg)
    · have he : (fun c : Coeff 2 => miuraL2CartesianCoefficient c n) = fun _ => 0 := by
        funext c
        exact if_neg hn
      rw [he]
      exact analyticAt_const
  have hbound (b : Coeff 2) (hb : b ∈ U) (n : ℤ) :
      ‖((Weight.sobolev (1/2) n : ℝ) : ℂ)*(miuraL2CartesianCoefficient b n).1‖ ≤
        R*(‖(sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi (scalarL2Diagonal b)).1 n‖+
          ‖(sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi (scalarL2Diagonal b)).2 n‖) ∧
      ‖((Weight.sobolev (1/2) n : ℝ) : ℂ)*(miuraL2CartesianCoefficient b n).2‖ ≤
        R*(‖(sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi (scalarL2Diagonal b)).1 n‖+
          ‖(sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi (scalarL2Diagonal b)).2 n‖) := by
    by_cases hn : 0 < n
    · have hi : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
      simp only [miuraL2CartesianCoefficient,if_pos hn,miuraL2CartesianCoordinates,hi]
      have ht := hroot (scalarL2Diagonal b) hb.1 n hn
      constructor
      · rw [norm_mul,Complex.norm_of_nonneg ((Weight.sobolev (1/2)).positive n).le,norm_mul,← mul_assoc]
        calc
          _ ≤ R*‖(sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi (scalarL2Diagonal b)).1 n‖ :=
            mul_le_mul_of_nonneg_right ht (norm_nonneg _)
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) hR
      · rw [norm_mul,Complex.norm_of_nonneg ((Weight.sobolev (1/2)).positive n).le,norm_neg,norm_mul,← mul_assoc]
        calc
          _ ≤ R*‖(sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi (scalarL2Diagonal b)).2 n‖ :=
            mul_le_mul_of_nonneg_right ht (norm_nonneg _)
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) hR
    · simp only [miuraL2CartesianCoefficient,if_neg hn]
      constructor <;> change ‖((Weight.sobolev (1/2) n : ℝ) : ℂ)*0‖ ≤ _
      all_goals simp only [mul_zero,norm_zero]; positivity
  have hrealize (b : Coeff 2) (hb : b ∈ U) :
      (∃ v : WeightedCoeff (Weight.sobolev (1/2)) 2,
        (∀ n, v.val n = (miuraL2CartesianCoefficient b n).1) ∧ ‖v‖ ≤ 2*R*M) ∧
      (∃ v : WeightedCoeff (Weight.sobolev (1/2)) 2,
        (∀ n, v.val n = (miuraL2CartesianCoefficient b n).2) ∧ ‖v‖ ≤ 2*R*M) := by
    let z := sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi (scalarL2Diagonal b)
    have hm := hmapBound (scalarL2Diagonal b) hb.2
    have hsum : R*(‖z.1‖+‖z.2‖) ≤ 2*R*M := by
      have hx : ‖z.1‖ ≤ M := (norm_fst_le z).trans hm
      have hy : ‖z.2‖ ≤ M := (norm_snd_le z).trans hm
      nlinarith
    obtain ⟨x,hx,hxn⟩ := WeightedCoeff.exists_of_two_sequence_bound (Weight.sobolev (1/2))
      (fun n => (miuraL2CartesianCoefficient b n).1) z.1 z.2 R hR (fun n => (hbound b hb n).1)
    obtain ⟨y,hy,hyn⟩ := WeightedCoeff.exists_of_two_sequence_bound (Weight.sobolev (1/2))
      (fun n => (miuraL2CartesianCoefficient b n).2) z.1 z.2 R hR (fun n => (hbound b hb n).2)
    exact ⟨⟨x,hx,hxn.trans hsum⟩,y,hy,hyn.trans hsum⟩
  obtain ⟨hXA,hX⟩ := WeightedCoeff.analytic_realization_of_bound (Weight.sobolev (1/2))
    (fun b n => (miuraL2CartesianCoefficient b n).1) hU
    (fun n b hb => analyticAt_fst.comp (hcoord n b hb)) (2*R*M) (fun b hb => (hrealize b hb).1)
  obtain ⟨hYA,hY⟩ := WeightedCoeff.analytic_realization_of_bound (Weight.sobolev (1/2))
    (fun b n => (miuraL2CartesianCoefficient b n).2) hU
    (fun n b hb => analyticAt_snd.comp (hcoord n b hb)) (2*R*M) (fun b hb => (hrealize b hb).2)
  refine ⟨U,hU,haU,fun b hb => (hXA b hb).prod (hYA b hb),?_⟩
  intro b hb n
  exact Prod.ext ((hX b hb).2 n) ((hY b hb).2 n)

theorem analyticAt_miuraL2CartesianSequence
    (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) :
    AnalyticAt ℂ miuraL2CartesianSequence a := by
  obtain ⟨U,_,haU,hA,_⟩ := exists_local_miuraL2CartesianSequence_analytic a ha
  exact hA a haU

/-- One open complex source domain contains the entire physical real L²
space and supports the actual full weighted Cartesian map. -/
theorem exists_miuraL2CartesianSequence_domain :
    ∃ U : Set (Coeff 2), IsOpen U ∧ {a | ∀ j, a j = conj (a (-j))} ⊆ U ∧
      AnalyticOnNhd ℂ miuraL2CartesianSequence U ∧
      ∀ b ∈ U, ∀ n : ℤ,
        ((miuraL2CartesianSequence b).1.val n,(miuraL2CartesianSequence b).2.val n) =
          miuraL2CartesianCoefficient b n := by
  let R := {a : Coeff 2 // ∀ j, a j = conj (a (-j))}
  have hlocal (a : R) := exists_local_miuraL2CartesianSequence_analytic a.val a.property
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
