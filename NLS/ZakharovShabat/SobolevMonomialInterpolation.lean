import NLS.ZakharovShabat.SobolevMonomialIntegral
import NLS.DifferentialPolynomial.MonomialInterpolationExponents

/-! # The actual monomial interpolation estimate (5.12) -/
noncomputable section
open NLS.Fourier NLS.DifferentialPolynomial MeasureTheory
namespace NLS.ZakharovShabat

private theorem lower_jet_norm_bound (m k : ℕ) (hk : k < m) (a : SobolevSource m) :
    ‖lowerSobolevJet m (false,k) a‖ ≤ 4*(2*Real.pi)^k*
      ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.1‖^(1-((k:ℝ)+1/2)/m)*
      ‖a.1‖^(((k:ℝ)+1/2)/m) := by
  simp only [lowerSobolevJet,hk,↓reduceDIte,Bool.false_eq_true,↓reduceIte,ContinuousLinearMap.comp_apply]
  exact norm_hierarchySobolevJetContinuous_interpolate m k hk a.1

/-- A supported reduced monomial obeys (5.12), with a constant independent
of the source. The exponents retain the actual total field count. -/
theorem exists_sobolevRealMonomial_interpolation_bound (m : ℕ) (hm : 1 ≤ m)
    (d : Monomial) (hd : d ∈ (nlsOddReducedPolynomial m hm).support) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : SobolevSource m,
      (∫ x in (0:ℝ)..1, sobolevRealMonomial m d a x) ≤
        C*‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.1‖^
          ((1+1/(2*m))*((∑ k ∈ Finset.range m, (jetMultiplicity d k:ℝ))-2))*
        ‖a.1‖^(2-((∑ k ∈ Finset.range m, (jetMultiplicity d k:ℝ))-2)/(2*m)) := by
  obtain ⟨hD,_⟩ := nlsOddReducedPolynomial_field_degree_bounds m hm d hd
  obtain ⟨i,hi,j,hj,ν,hν⟩ := exists_two_factor_split (Finset.range m) (jetMultiplicity d) (by omega)
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  let c := fun k : ℕ => 4*(2*Real.pi)^k
  let θ := fun k : ℕ => ((k:ℝ)+1/2)/m
  let K := (∏ k ∈ Finset.range m, c k^ν k)*(2*Real.pi)^i*(2*Real.pi)^j
  have hK : 0 ≤ K := by dsimp [K,c]; positivity
  refine ⟨K,hK,?_⟩
  intro a
  by_cases ha : a.1 = 0
  · have hz (x : ℝ) : sobolevRealMonomial m d a x = 0 := by
      unfold sobolevRealMonomial
      apply Finset.prod_eq_zero hi
      rw [lowerSobolevJet_first_apply m i hi',ha,map_zero]
      have hpos : jetMultiplicity d i ≠ 0 := by have := hν i hi; simp only [↓reduceIte] at this; omega
      simp [hpos]
    simp only [hz,intervalIntegral.integral_zero]
    positivity
  let A := ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.1‖
  let B := ‖a.1‖
  have hB : 0 < B := norm_pos_iff.mpr ha
  have hA : 0 < A := by
    apply lt_of_le_of_ne (norm_nonneg _)
    intro hz
    have he := norm_eq_zero.mp hz.symm
    apply ha
    apply Subtype.ext
    funext n
    have hn := congrArg (fun z : Coeff 2 => z n) he
    change WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a.1 n = 0 at hn
    simpa only [WeightedCoeff.sobolevToL2_apply,WeightedCoeff.zero_val] using hn
  have hw : (∑ k ∈ Finset.range m, ((k:ℝ)+1)*jetMultiplicity d k) = 2*m+2 := by
    exact_mod_cast (nlsOddReducedPolynomial_multiplicity_constraints m hm d hd).1
  obtain ⟨hα,hβ⟩ := two_factor_interpolation_exponents m hm (jetMultiplicity d) ν i j hi' hj' hν hw
  have hU : (∏ k ∈ Finset.range m, ‖lowerSobolevJet m (false,k) a‖^ν k) ≤
      ∏ k ∈ Finset.range m, (c k*A^(1-θ k)*B^(θ k))^ν k := by
    apply Finset.prod_le_prod (fun k _ => pow_nonneg (norm_nonneg _) _)
    intro k hk
    exact pow_le_pow_left₀ (norm_nonneg _) (lower_jet_norm_bound m k (Finset.mem_range.mp hk) a) _
  have hL₁ := norm_hierarchySobolevJetL2_interpolate m i hm hi'.le a.1
  have hL₂ := norm_hierarchySobolevJetL2_interpolate m j hm hj'.le a.1
  calc
    _ ≤ (∏ k ∈ Finset.range m, ‖lowerSobolevJet m (false,k) a‖^ν k)*
        ‖hierarchySobolevJetL2 m i hi'.le a.1‖*‖hierarchySobolevJetL2 m j hj'.le a.1‖ :=
      integral_sobolevRealMonomial_le_split m d i j hi' hj' ν hν a
    _ ≤ (∏ k ∈ Finset.range m, (c k*A^(1-θ k)*B^(θ k))^ν k)*
        ((2*Real.pi)^i*A^(1-(i:ℝ)/m)*B^((i:ℝ)/m))*
        ((2*Real.pi)^j*A^(1-(j:ℝ)/m)*B^((j:ℝ)/m)) := by gcongr
    _ = _ := by
      rw [prod_interpolated_powers (Finset.range m) ν c (fun k => 1-θ k) θ A B hA hB]
      have he : ((∏ k ∈ Finset.range m, c k^ν k)*A^(∑ k ∈ Finset.range m, (1-θ k)*ν k)*
          B^(∑ k ∈ Finset.range m, θ k*ν k))*
          ((2*Real.pi)^i*A^(1-(i:ℝ)/m)*B^((i:ℝ)/m))*
          ((2*Real.pi)^j*A^(1-(j:ℝ)/m)*B^((j:ℝ)/m)) =
          K*(A^(∑ k ∈ Finset.range m, (1-θ k)*ν k)*A^(1-(i:ℝ)/m)*A^(1-(j:ℝ)/m))*
            (B^(∑ k ∈ Finset.range m, θ k*ν k)*B^((i:ℝ)/m)*B^((j:ℝ)/m)) := by dsimp [K]; ring
      rw [he,← Real.rpow_add hA,← Real.rpow_add hA,← Real.rpow_add hB,← Real.rpow_add hB]
      rw [hα,hβ]

end NLS.ZakharovShabat
