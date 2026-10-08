import NLS.ZakharovShabat.SobolevMonomialInterpolation
import NLS.SequenceSpaces.GeometricAbsorption

/-! # Absorbing the odd remainder into the H^m norm

Young's inequality gives an arbitrary small H^m-square coefficient and the
exact L² power 4m+2, first per monomial and then for the physical remainder.
-/
noncomputable section
open NLS.Fourier NLS.DifferentialPolynomial MeasureTheory
namespace NLS.ZakharovShabat

/-- A single coefficient-weighted physical monomial has the exact Young bound. -/
theorem exists_sobolevRealMonomial_absorption (m : ℕ) (hm : 1 ≤ m)
    (d : Monomial) (hd : d ∈ (nlsOddReducedPolynomial m hm).support) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : SobolevSource m,
      ‖(nlsOddReducedPolynomial m hm).coeff d‖*(∫ x in (0:ℝ)..1, sobolevRealMonomial m d a x) ≤
        ε*‖a.1‖^2+C*‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.1‖^(4*m+2) := by
  obtain ⟨K,hK,hbound⟩ := exists_sobolevRealMonomial_interpolation_bound m hm d hd
  let D : ℝ := ∑ k ∈ Finset.range m, (jetMultiplicity d k:ℝ)
  let α := 2-(D-2)/(2*m)
  let β := (1+1/(2*m))*(D-2)
  have hD := nlsOddReducedPolynomial_field_degree_bounds m hm d hd
  obtain ⟨hα,hα2,hpower⟩ := monomial_interpolation_power_range m hm D
    (by dsimp [D]; exact_mod_cast hD.1) (by dsimp [D]; exact_mod_cast hD.2)
  have hβ : ((4*m+2:ℕ):ℝ)*(1-α/2) = β := by
    have h := (div_eq_iff (by dsimp [α]; linarith : 1-α/2 ≠ 0)).mp hpower
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using h.symm
  obtain ⟨C,hC,hCbound⟩ := exists_geometric_absorption (α/2)
    (‖(nlsOddReducedPolynomial m hm).coeff d‖*K) ε
    (by positivity) (by dsimp [α]; linarith) (mul_nonneg (norm_nonneg _) hK) hε
  refine ⟨C,hC,?_⟩
  intro a
  have h := hCbound (‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.1‖^((4*m+2:ℕ):ℝ))
    (‖a.1‖^2) (by positivity) (sq_nonneg _)
  rw [← Real.rpow_mul (norm_nonneg _),hβ,← Real.rpow_natCast_mul (norm_nonneg _)] at h
  simp only [Nat.cast_ofNat,show (2:ℝ)*(α/2)=α by ring,Real.rpow_natCast] at h
  have hb := mul_le_mul_of_nonneg_left (hbound a) (norm_nonneg ((nlsOddReducedPolynomial m hm).coeff d))
  apply le_trans ?_ h
  simpa only [mul_assoc] using hb

/-- Finite summation retains an arbitrarily small H^m coefficient and the
L²-only power 4m+2; all constants are independent of the source. -/
theorem exists_sobolevOddRemainder_Hm_absorption (m : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : realTypeHigherSobolevSourceLocus m,
      (∫ x in (0:ℝ)..1, ‖sobolevPolynomialField m (nlsOddReducedPolynomial m hm) a.val
        (x : AddCircle (2:ℝ))‖) ≤ ε*‖a.val.1‖^2+
          C*‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^(4*m+2) := by
  classical
  let S := (nlsOddReducedPolynomial m hm).support
  let δ := ε/(S.card+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  choose C hC hbound using (fun d : S => exists_sobolevRealMonomial_absorption m hm d.val d.property δ hδ)
  refine ⟨∑ d ∈ S.attach, C d,Finset.sum_nonneg (fun d _ => hC d),?_⟩
  intro a
  have hfield : (∫ x in (0:ℝ)..1, ‖sobolevPolynomialField m (nlsOddReducedPolynomial m hm) a.val
        (x : AddCircle (2:ℝ))‖) ≤ ∫ x in (0:ℝ)..1, sobolevOddRemainderMajorant m hm a.val x := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact ((sobolevPolynomialField m (nlsOddReducedPolynomial m hm) a.val).continuous.comp
        continuous_quotient_mk').norm.intervalIntegrable 0 1
    · exact (continuous_sobolevOddRemainderMajorant m hm a.val).intervalIntegrable 0 1
    · intro x _
      exact norm_sobolevOddRemainderField_le m hm a x
  apply hfield.trans
  rw [integral_sobolevOddRemainderMajorant]
  change (∑ d ∈ S, _) ≤ _
  rw [← Finset.sum_attach]
  calc
    _ ≤ ∑ d ∈ S.attach, (δ*‖a.val.1‖^2+C d*‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^(4*m+2)) :=
      Finset.sum_le_sum (fun d _ => hbound d a.val)
    _ = (S.card:ℝ)*δ*‖a.val.1‖^2+(∑ d ∈ S.attach, C d)*‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.val.1‖^(4*m+2) := by
      rw [Finset.sum_add_distrib,Finset.sum_const,← Finset.sum_mul,Finset.card_attach,nsmul_eq_mul,mul_assoc]
    _ ≤ _ := by
      have hδle : (S.card:ℝ)*δ ≤ ε := by
        dsimp [δ]
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity : (0:ℝ) < S.card+1)).mpr
        nlinarith
      gcongr

end NLS.ZakharovShabat
