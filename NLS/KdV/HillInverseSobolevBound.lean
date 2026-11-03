import NLS.KdV.HillLowerSobolevTrace
import NLS.SequenceSpaces.TriangularHierarchyBounds

/-! # The actual integer inverse action-to-Sobolev estimate from the full hierarchy trace and coercivity. -/

noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology NLS.Fourier NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV
def hillNativeActionMass (M m : ℕ) (p : RealHillWeightedPotential (hillIntegerWeight M)) : ℝ :=
  ∑' n, hillGapActionTerm (hillPeriodOneUnitPotential (hillIntegerWeight M) p.val)
    (hillPeriodOneUnitPotential_even (hillIntegerWeight M) p.val)
    (hillPeriodOneUnitPotential_real (hillIntegerWeight M) p.val p.property) m n

theorem hillNativeActionMass_nonneg (M m : ℕ)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) : 0 ≤ hillNativeActionMass M m p :=
  tsum_nonneg (fun n => hillGapActionTerm_nonneg _ _ _ m n)

theorem hillNativeActionMass_mono (M i j : ℕ) (hij : i ≤ j) (hj : j ≤ M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) :
    hillNativeActionMass M i p ≤ hillNativeActionMass M j p :=
  tsum_hillNativeGapActions_mono_order M i j hij hj p

theorem exists_hillNativeHamiltonianActionBound (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, m ≤ M →
      ∀ p : RealHillWeightedPotential (hillIntegerWeight M), p.val.val 0 = 0 →
      ‖hillSobolevHamiltonianFamily M (hillNativeIntegerToScalar M p.val) m‖ ≤
        C*(hillNativeActionMass M m p+
          (1+hillNativeActionMass M (m-1) p)^m*hillNativeActionMass M (m-1) p) := by
  let K : ℕ → ℝ := fun j => (exists_hillNativeGlobalMomentComparisons_uniform j).choose
  have hK (j : ℕ) : 0 ≤ K j := (exists_hillNativeGlobalMomentComparisons_uniform j).choose_spec.1
  let D : ℕ → ℝ := fun j => (4 : ℝ)^j*((Real.pi^2+1)^j+K j)
  have hD (j : ℕ) : 0 ≤ D j := by
    exact mul_nonneg (by positivity) (add_nonneg (by positivity) (hK j))
  obtain ⟨C,hC,hbound⟩ := NLS.SequenceSpaces.exists_hierarchy_action_majorant_lower D hD m hm
  refine ⟨C,hC,?_⟩
  intro M hmM p hmean
  let H := hillSobolevHamiltonianFamily M (hillNativeIntegerToScalar M p.val)
  let A := fun j => hillNativeActionMass M j p
  apply hbound A (fun j => ‖H j‖)
  · exact fun j _ => hillNativeActionMass_nonneg M j p
  · exact fun i j hij hj => hillNativeActionMass_mono M i j hij (hj.trans hmM) p
  · exact fun j _ => norm_nonneg _
  · intro j hj
    have hjM := hj.trans hmM
    have ht := norm_hillSobolevHamiltonianFamily_le_moment_convolution M j hjM p hmean
    have hc := (exists_hillNativeGlobalMomentComparisons_uniform j).choose_spec.2 M hjM p hmean
    dsimp only at hc ht
    have hs : (∑' n, |hillHierarchyMomentTerm (hillIntegerWeight M) p j n|) ≤
        (Real.pi^2+1)^j*A j+K j*(1+A 0)^j*A 0 := hc.2
    have hAj : 0 ≤ A j := hillNativeActionMass_nonneg M j p
    have hA0 : 0 ≤ A 0 := hillNativeActionMass_nonneg M 0 p
    have hE : 0 ≤ (1+A 0)^j*A 0 := mul_nonneg (by positivity) hA0
    have hL : 0 ≤ (Real.pi^2+1)^j := by positivity
    have hmain : (4 : ℝ)^j*((Real.pi^2+1)^j*A j+K j*(1+A 0)^j*A 0) ≤
        D j*(A j+(1+A 0)^j*A 0) := by
      dsimp only [D]
      have hi : (Real.pi^2+1)^j*A j+K j*(1+A 0)^j*A 0 ≤
          ((Real.pi^2+1)^j+K j)*(A j+(1+A 0)^j*A 0) := by
        nlinarith [mul_nonneg hL hE, mul_nonneg (hK j) hAj]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hi (show (0 : ℝ) ≤ 4^j by positivity)
    exact ht.trans (add_le_add
      ((mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 4^j by positivity)).trans hmain) le_rfl)

theorem hill_norm_error_le_action_mass (m : ℕ) (r B : ℝ) (hB : 0 ≤ B)
    (hrB : r^2 ≤ 2*B) :
    (1+r^(2*m))*r^2 ≤ 2*(1+(2 : ℝ)^m)*((1+B)^m*B) := by
  have hp1 : 1 ≤ (1+B)^m := one_le_pow₀ (by linarith)
  have hp2 : r^(2*m) ≤ (2 : ℝ)^m*(1+B)^m := by
    rw [pow_mul]
    have h := pow_le_pow_left₀ (sq_nonneg r) (hrB.trans (show 2*B ≤ 2*(1+B) by linarith)) m
    simpa only [mul_pow] using h
  have hf : 1+r^(2*m) ≤ (1+(2 : ℝ)^m)*(1+B)^m := by nlinarith
  have he := mul_le_mul hf hrB (sq_nonneg r) (by positivity : 0 ≤ (1+(2 : ℝ)^m)*(1+B)^m)
  nlinarith

theorem exists_hillNativeInverseSobolevBound (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : RealHillWeightedPotential (hillIntegerWeight m),
      p.val.val 0 = 0 → ‖p.val‖^2 ≤ C*(hillNativeActionMass m m p+
        (1+hillNativeActionMass m (m-1) p)^m*hillNativeActionMass m (m-1) p) := by
  obtain ⟨CH,hCH,hHam⟩ := exists_hillNativeHamiltonianActionBound m hm
  obtain ⟨CK,hCK,hKin⟩ := exists_hillSobolevHamiltonian_polynomial_coercivity m hm
  let P : ℝ := 2^(2*m)
  let R : ℝ := 2*(1+(2 : ℝ)^m)
  let C : ℝ := 2+4*CH+CK*R
  let L : ℝ := ‖hillScalarToNativeInteger m‖
  have hP : 0 ≤ P := by positivity
  have hR : 0 ≤ R := by positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨L^2*P*C, by positivity, ?_⟩
  intro p hmean
  let a := hillNativeIntegerToScalar m p.val
  let A := fun j => hillNativeActionMass m j p
  let B := A (m-1)
  let E := (1+B)^m*B
  let r := ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖
  have hA : 0 ≤ A m := hillNativeActionMass_nonneg m m p
  have hB : 0 ≤ B := hillNativeActionMass_nonneg m (m-1) p
  have hE : 0 ≤ E := mul_nonneg (by positivity) hB
  have h0B : A 0 ≤ B := hillNativeActionMass_mono m 0 (m-1) (by omega) (by omega) p
  have hmass := tsum_hillNativeBaseActions_eq_half_norm m p hmean
  dsimp only at hmass
  rw [norm_hillPeriodOneUnitPotential_eq_sharedL2] at hmass
  have hr2 : r^2 = 2*A 0 := by change A 0 = (1/2 : ℝ)*r^2 at hmass; linarith
  have hrB : r^2 ≤ 2*B := by linarith
  have herr : (1+r^(2*m))*r^2 ≤ R*E := hill_norm_error_le_action_mass m r B hB hrB
  have hreal (k : ℤ) : a.val (-k) = conj (a.val k) := by
    have h := p.property k
    simpa only [a,hillNativeIntegerToScalar_apply,SpectralWeight.toCoeff_apply] using h
  have hH := hHam m le_rfl p hmean
  rw [hillSobolevHamiltonianFamily_self m hm] at hH
  change ‖hillSobolevHamiltonian m hm a‖ ≤ CH*(A m+E) at hH
  have hk := hKin a hreal
  have hre := Complex.re_le_norm (hillSobolevHamiltonian m hm a)
  have hJ : ‖hierarchySobolevJetL2 m m le_rfl a‖^2 ≤ 4*CH*(A m+E)+CK*R*E := by
    have he := mul_le_mul_of_nonneg_left herr hCK
    change ‖hierarchySobolevJetL2 m m le_rfl a‖^2 ≤
      4*(hillSobolevHamiltonian m hm a).re+CK*(1+r^(2*m))*r^2 at hk
    nlinarith
  have hp1 : 1 ≤ (1+B)^m := one_le_pow₀ (by linarith)
  have hBE : B ≤ E := by
    have h := mul_le_mul_of_nonneg_right hp1 hB
    simpa only [one_mul] using h
  have hrs : r^2 ≤ 2*E := hrB.trans (by linarith)
  have hs := norm_sobolev_sq_le_highestJet m a
  have hsbound : ‖a‖^2 ≤ P*C*(A m+E) := by
    change ‖a‖^2 ≤ P*(r^2+‖hierarchySobolevJetL2 m m le_rfl a‖^2) at hs
    have hinner : r^2+‖hierarchySobolevJetL2 m m le_rfl a‖^2 ≤ C*(A m+E) := by
      dsimp only [C]
      nlinarith [mul_nonneg (mul_nonneg hCK hR) hA]
    exact hs.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hinner hP)
  have hn := (hillScalarToNativeInteger m).le_opNorm a
  rw [show hillScalarToNativeInteger m a = p.val from
    hillScalarToNativeInteger_nativeIntegerToScalar m p.val] at hn
  have hn2 := pow_le_pow_left₀ (norm_nonneg p.val) hn 2
  rw [mul_pow] at hn2
  have hscaled := mul_le_mul_of_nonneg_left hsbound (sq_nonneg L)
  change ‖p.val‖^2 ≤ L^2*P*C*(A m+E)
  exact hn2.trans (by simpa only [L,mul_assoc] using hscaled)

end NLS.KdV
