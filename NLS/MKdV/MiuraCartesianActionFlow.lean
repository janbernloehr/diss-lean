import NLS.MKdV.MiuraL2CartesianCoordinates
import NLS.MKdV.MiuraActionFlowInvariants
import NLS.ZakharovShabat.SourceDiagonalActionIsospectral
import NLS.ZakharovShabat.SourcePairedCartesianTransport

/-! # Exact physical Cartesian rotations along every complete action flow

The actual Laurent scaling is isospectral even at a collapsed gap. The
second Cartesian sign changes the NLS rotation to the Gardner orientation.
All integer Sobolev profiles, all real times, and all closed actions are
included in the literal coordinate identity.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraActionInitialSource_L2_diagonal (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    (miuraActionInitialSource s a ha).val = scalarL2Diagonal (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext j
  · change (miuraActionInitialSource s a ha).val.fst j =
      (scalarL2Diagonal (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a)).fst j
    rw [miuraActionInitialSource_fst,scalarL2Diagonal_fst]
    simp only [hierarchySobolevJetL2_apply,pow_zero,one_mul]
  · change (miuraActionInitialSource s a ha).val.snd j =
      (scalarL2Diagonal (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a)).snd j
    rw [miuraActionInitialSource_snd,scalarL2Diagonal_snd]
    simp only [hierarchySobolevJetL2_apply,pow_zero,one_mul]

def miuraActionInitialDiagonalSource (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) : realDiagonalSourceLocus 2 :=
  ⟨(miuraActionInitialSource s a ha).val,(miuraActionInitialSource s a ha).property,
    miuraActionInitialSource_diagonal s a ha⟩

/-- The whole Cartesian pair rotates clockwise at unit speed for the
selected action, and stays fixed for every other positive action. -/
theorem miuraL2CartesianCoordinates_miuraActionFlow (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (t : ℝ) :
    miuraL2CartesianCoordinates m (hierarchySobolevJetL2 s 0 (Nat.zero_le s) (miuraActionFlow s a ha n t)) =
      if m = n then cartesianPlaneRotation t (miuraL2CartesianCoordinates m (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a))
      else miuraL2CartesianCoordinates m (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a) := by
  let φ := miuraActionInitialSource s a ha
  let b := miuraActionFlow s a ha n t
  have hb := miuraActionFlow_real s a ha n t
  have hA := (miuraActionInitialSource_L2_diagonal s a ha).symm
  have hB := (miuraActionInitialSource_L2_diagonal s b hb).symm
  have hs := congrArg Subtype.val (miuraActionFlow_source s a ha n t)
  have hr := sourceDiagonalActionRoot_eq_of_isospectral (by simp) (by norm_num)
    (miuraActionInitialDiagonalSource s a ha) (miuraActionInitialDiagonalSource s b hb)
    (miuraActionFlow_isospectral s a ha n t) m (by omega)
  change sourceDiagonalActionRoot (by simp) (by norm_num) m (miuraActionInitialSource s b hb).val =
    sourceDiagonalActionRoot (by simp) (by norm_num) m (miuraActionInitialSource s a ha).val at hr
  have hc := miuraActionFlowFamily.data.birkhoff_pairedActionFlow_coordinates_of_ne_second
    φ n (-(n : ℤ)) m (by omega) t
  rw [← hs] at hc
  by_cases hmn : m = n
  · rw [if_pos hmn]
    have hmnZ : (m : ℤ) = n := by exact_mod_cast hmn
    rw [if_pos hmnZ] at hc
    dsimp only [miuraL2CartesianCoordinates]
    rw [hA,hB,hr]
    exact (congrArg (fun z : ℂ × ℂ =>
      (sourceDiagonalActionRoot (by simp) (by norm_num) m (miuraActionInitialSource s a ha).val*z.1,
       -(sourceDiagonalActionRoot (by simp) (by norm_num) m (miuraActionInitialSource s a ha).val*z.2))) hc).trans
      (cartesianPlaneRotation_scaled_reflection _ t _)
  · rw [if_neg hmn]
    have hmnZ : (m : ℤ) ≠ n := by exact_mod_cast hmn
    rw [if_neg hmnZ] at hc
    dsimp only [miuraL2CartesianCoordinates]
    rw [hA,hB,hr]
    exact congrArg (fun z : ℂ × ℂ =>
      (sourceDiagonalActionRoot (by simp) (by norm_num) m (miuraActionInitialSource s a ha).val*z.1,
       -(sourceDiagonalActionRoot (by simp) (by norm_num) m (miuraActionInitialSource s a ha).val*z.2))) hc

end NLS.MKdV
