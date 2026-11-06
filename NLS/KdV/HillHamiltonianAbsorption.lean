import NLS.KdV.HillMonomialInterpolation
import NLS.DifferentialPolynomial.JetMajorants
import NLS.SequenceSpaces.GeometricAbsorption

/-! # Uniform absorption of the actual scalar remainder with the precise L2-only power. -/

noncomputable section
set_option autoImplicit false
open NLS.Fourier NLS.DifferentialPolynomial NLS.ZakharovShabat MeasureTheory
namespace NLS.KdV

theorem exists_hillMonomial_absorption (m : ℕ) (hm : 1 ≤ m)
    (d : Monomial) (hd : d ∈ (hillReducedPolynomial m hm).support) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : SobolevSource m,
      ‖(hillReducedPolynomial m hm).coeff d‖*(∫ x in (0 : ℝ)..1, sobolevRealMonomial m d a x) ≤
        ε*‖a.1‖^2+C*‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.1‖^((4*m+6 : ℝ)/3) := by
  obtain ⟨K,hK,hbound⟩ := exists_hillMonomial_interpolation_bound m hm d hd
  let D : ℝ := ∑ k ∈ Finset.range m, (jetMultiplicity d k : ℝ)
  let α := 2-3*(D-2)/(2*m)
  let β := (1+3/(2*m))*(D-2)
  let γ : ℝ := (4*m+6)/3
  have hD := hillReducedPolynomial_field_degree_bounds m hm d hd
  obtain ⟨hα,hα2,hpower⟩ := scalar_monomial_interpolation_power_range m hm D
    (by dsimp [D]; exact_mod_cast hD.1) (by dsimp [D]; exact_mod_cast hD.2)
  have hβ : γ*(1-α/2) = β := by
    have h := (div_eq_iff (by dsimp [α]; linarith : 1-α/2 ≠ 0)).mp hpower
    exact h.symm
  obtain ⟨C,hC,hCbound⟩ := NLS.exists_geometric_absorption (α/2)
    (‖(hillReducedPolynomial m hm).coeff d‖*K) ε
    (by positivity) (by dsimp [α]; linarith) (mul_nonneg (norm_nonneg _) hK) hε
  refine ⟨C,hC,?_⟩
  intro a
  have h := hCbound (‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.1‖^γ)
    (‖a.1‖^2) (by positivity) (sq_nonneg _)
  rw [← Real.rpow_mul (norm_nonneg _),hβ,← Real.rpow_natCast_mul (norm_nonneg _)] at h
  simp only [Nat.cast_ofNat, show (2 : ℝ)*(α/2)=α by ring] at h
  have hb := mul_le_mul_of_nonneg_left (hbound a) (norm_nonneg ((hillReducedPolynomial m hm).coeff d))
  apply le_trans ?_ h
  simpa only [mul_assoc] using hb

def hillSobolevRemainderMajorant (m : ℕ) (hm : 1 ≤ m) (a : ScalarSobolev m) (x : ℝ) : ℝ :=
  ∑ d ∈ (hillReducedPolynomial m hm).support,
    ‖(hillReducedPolynomial m hm).coeff d‖ * sobolevRealMonomial m d (a,0) x

theorem norm_hillSobolevRemainderField_le (m : ℕ) (hm : 1 ≤ m)
    (a : ScalarSobolev m) (x : ℝ) :
    ‖sobolevPolynomialField m (hillReducedPolynomial m hm) (a,0) (x : AddCircle (2 : ℝ))‖ ≤
      hillSobolevRemainderMajorant m hm a x := by
  rw [sobolevPolynomialField_apply]
  apply norm_eval_le_lower_jet_majorant m hm _ (hillReducedPolynomial_order m hm)
  intro v hv
  rcases v with ⟨b,k⟩
  cases b
  · exact le_rfl
  · simp [lowerSobolevJet, hv]

theorem exists_hillSobolevRemainder_Hm_absorption (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ScalarSobolev m,
      (∫ x in (0 : ℝ)..1, ‖sobolevPolynomialField m (hillReducedPolynomial m hm) (a,0)
        (x : AddCircle (2 : ℝ))‖) ≤ ε*‖a‖^2+
          C*‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^((4*m+6 : ℝ)/3) := by
  classical
  let S := (hillReducedPolynomial m hm).support
  let δ := ε/(S.card+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  choose C hC hbound using (fun d : S => exists_hillMonomial_absorption m hm d.val d.property δ hδ)
  refine ⟨∑ d ∈ S.attach, C d,Finset.sum_nonneg (fun d _ => hC d),?_⟩
  intro a
  have hc : Continuous (hillSobolevRemainderMajorant m hm a) := by
    unfold hillSobolevRemainderMajorant
    exact continuous_finsetSum _ fun d _ => continuous_const.mul (continuous_sobolevRealMonomial m d (a,0))
  have hfield : (∫ x in (0 : ℝ)..1, ‖sobolevPolynomialField m (hillReducedPolynomial m hm) (a,0)
      (x : AddCircle (2 : ℝ))‖) ≤ ∫ x in (0 : ℝ)..1, hillSobolevRemainderMajorant m hm a x := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact ((sobolevPolynomialField m (hillReducedPolynomial m hm) (a,0)).continuous.comp
        continuous_quotient_mk').norm.intervalIntegrable 0 1
    · exact hc.intervalIntegrable 0 1
    · intro x _
      exact norm_hillSobolevRemainderField_le m hm a x
  apply hfield.trans
  have hint : (∫ x in (0 : ℝ)..1, hillSobolevRemainderMajorant m hm a x) =
      ∑ d ∈ S, ‖(hillReducedPolynomial m hm).coeff d‖ *
        ∫ x in (0 : ℝ)..1, sobolevRealMonomial m d (a,0) x := by
    unfold hillSobolevRemainderMajorant
    rw [intervalIntegral.integral_finsetSum]
    · exact Finset.sum_congr rfl fun d _ => intervalIntegral.integral_const_mul _ _
    · intro d _
      exact (continuous_const.mul (continuous_sobolevRealMonomial m d (a,0))).intervalIntegrable 0 1
  rw [hint, ← Finset.sum_attach]
  calc
    _ ≤ ∑ d ∈ S.attach, (δ*‖a‖^2+C d*‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^((4*m+6 : ℝ)/3)) :=
      Finset.sum_le_sum (fun d _ => hbound d (a,0))
    _ = (S.card : ℝ)*δ*‖a‖^2+(∑ d ∈ S.attach, C d)*
        ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖^((4*m+6 : ℝ)/3) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_mul, Finset.card_attach,
        nsmul_eq_mul, mul_assoc]
    _ ≤ _ := by
      have hδle : (S.card : ℝ)*δ ≤ ε := by
        dsimp [δ]
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < S.card+1)).mpr
        nlinarith
      gcongr

end NLS.KdV
