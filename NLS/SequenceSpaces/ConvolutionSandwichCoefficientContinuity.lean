import NLS.SequenceSpaces.ConvolutionSandwich
import NLS.SequenceSpaces.CoefficientCompactness
import NLS.SequenceSpaces.Compact

/-! # Compact dependence of two-sided convolution on the potential

Finite cutoffs of both symbols see only finitely many potential coefficients.
Their uniform operator-norm approximation makes the potential-to-operator map
compact and continuous along bounded coefficientwise limits.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The convolution sandwich, viewed as a linear map from potentials to operators. -/
def convolutionSandwichPotentialCLM (a b : Coeff q) :
    Coeff p →L[ℂ] (Coeff p →L[ℂ] Coeff 1) :=
  ({ toFun := fun φ => convolutionSandwich a φ b
     map_add' := by
       intro φ ψ
       simp only [convolutionSandwich, map_add, ContinuousLinearMap.add_comp,
         ContinuousLinearMap.comp_add]
     map_smul' := by
       intro c φ
       simp only [convolutionSandwich, map_smul, ContinuousLinearMap.smul_comp,
         ContinuousLinearMap.comp_smul, RingHom.id_apply] } :
    Coeff p →ₗ[ℂ] (Coeff p →L[ℂ] Coeff 1)).mkContinuous (‖a‖*‖b‖) (by
      intro φ
      change ‖convolutionSandwich a φ b‖ ≤ _
      calc
        _ ≤ ‖a‖*‖φ‖*‖b‖ := norm_convolutionSandwich_le a φ b
        _ = (‖a‖*‖b‖)*‖φ‖ := by ring)

@[simp] theorem convolutionSandwichPotentialCLM_apply (a b : Coeff q) (φ : Coeff p) :
    convolutionSandwichPotentialCLM a b φ = convolutionSandwich a φ b := rfl

/-- The operator-valued potential map has the product bound of its two symbols. -/
theorem norm_convolutionSandwichPotentialCLM_le (a b : Coeff q) :
    ‖convolutionSandwichPotentialCLM (p := p) a b‖ ≤ ‖a‖*‖b‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro φ
  calc
    _ ≤ ‖a‖*‖φ‖*‖b‖ := norm_convolutionSandwich_le a φ b
    _ = (‖a‖*‖b‖)*‖φ‖ := by ring

/-- Uniform symbol cutoff error, independent of the potential. -/
theorem norm_convolutionSandwichPotentialCLM_cutoff_sub_le (a b : Coeff q) (A B : Finset ℤ) :
    ‖convolutionSandwichPotentialCLM (p := p) (truncate A a) (truncate B b) -
      convolutionSandwichPotentialCLM a b‖ ≤
      ‖a-truncate A a‖*‖b‖ + ‖a‖*‖b-truncate B b‖ := by
  have he : convolutionSandwichPotentialCLM (p := p) a b -
      convolutionSandwichPotentialCLM (truncate A a) (truncate B b) =
      convolutionSandwichPotentialCLM (a-truncate A a) b +
      convolutionSandwichPotentialCLM (truncate A a) (b-truncate B b) := by
    ext φ f j
    have ha : a = (a-truncate A a)+truncate A a := by abel
    have hb : b = (b-truncate B b)+truncate B b := by abel
    have h : convolutionSandwich a φ b =
        convolutionSandwich (a-truncate A a) φ b +
        (convolutionSandwich (truncate A a) φ (b-truncate B b) +
          convolutionSandwich (truncate A a) φ (truncate B b)) := by
      calc
        _ = convolutionSandwich (a-truncate A a) φ b + convolutionSandwich (truncate A a) φ b := by
          conv_lhs => rw [ha, convolutionSandwich_add_left]
        _ = _ := by
          conv_lhs => rhs; rw [hb, convolutionSandwich_add_right]
    have he' := congrArg (fun T : Coeff p →L[ℂ] Coeff 1 => T f j) h
    change convolutionSandwich a φ b f j - convolutionSandwich (truncate A a) φ (truncate B b) f j = _
    change convolutionSandwich a φ b f j = _ at he'
    simp only [add_apply, lp.coeFn_add, Pi.add_apply] at he'
    change _ = convolutionSandwich (a-truncate A a) φ b f j +
      convolutionSandwich (truncate A a) φ (b-truncate B b) f j
    linear_combination he'
  rw [norm_sub_rev (convolutionSandwichPotentialCLM (p := p) (truncate A a) (truncate B b))
    (convolutionSandwichPotentialCLM a b), he]
  calc
    _ ≤ ‖convolutionSandwichPotentialCLM (p := p) (a-truncate A a) b‖ +
        ‖convolutionSandwichPotentialCLM (p := p) (truncate A a) (b-truncate B b)‖ :=
      norm_add_le (convolutionSandwichPotentialCLM (p := p) (a-truncate A a) b)
        (convolutionSandwichPotentialCLM (p := p) (truncate A a) (b-truncate B b))
    _ ≤ ‖a-truncate A a‖*‖b‖ + ‖truncate A a‖*‖b-truncate B b‖ :=
      add_le_add (norm_convolutionSandwichPotentialCLM_le _ _) (norm_convolutionSandwichPotentialCLM_le _ _)
    _ ≤ _ := by
      gcongr
      exact norm_truncate_le (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ q from Fact.out))) A a

/-- A finite pair of symbol supports only uses their finite difference set
of potential frequencies. -/
theorem convolutionSandwichPotentialCLM_cutoff_eq_comp (a b : Coeff q) (A B : Finset ℤ) :
    convolutionSandwichPotentialCLM (p := p) (truncate A a) (truncate B b) =
      (convolutionSandwichPotentialCLM (truncate A a) (truncate B b)).comp
        (truncateCLM (A.biUnion fun j => B.image fun k => j-k)) := by
  classical
  ext φ f j
  change convolutionSandwich (truncate A a) φ (truncate B b) f j =
    convolutionSandwich (truncate A a) (truncate (A.biUnion fun j => B.image fun k => j-k) φ) (truncate B b) f j
  simp only [convolutionSandwich_apply]
  by_cases hj : j ∈ A
  · congr 1
    apply tsum_congr
    intro k
    by_cases hk : k ∈ B
    · have hm : j-k ∈ A.biUnion (fun j => B.image fun k => j-k) :=
        Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image.mpr ⟨k, hk, rfl⟩⟩
      simp [truncate_apply, hk, hm]
    · simp [truncate_apply, hk]
  · simp [truncate_apply, hj]

/-- At a finite conjugate exponent, simultaneous symbol cutoffs converge in
operator norm on the entire potential-to-operator map. -/
theorem tendsto_convolutionSandwichPotentialCLM_cutoff (hq : q ≠ ⊤) (a b : Coeff q) :
    Tendsto (fun A : Finset ℤ => convolutionSandwichPotentialCLM (p := p) (truncate A a) (truncate A b))
      atTop (𝓝 (convolutionSandwichPotentialCLM a b)) := by
  apply (tendsto_iff_norm_sub_tendsto_zero
    (f := fun A : Finset ℤ => convolutionSandwichPotentialCLM (p := p) (truncate A a) (truncate A b))
    (b := convolutionSandwichPotentialCLM (p := p) a b)).mpr
  have ha : Tendsto (fun A : Finset ℤ => ‖a-truncate A a‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using ((tendsto_const_nhds (x := a)).sub (tendsto_truncate hq a)).norm
  have hb : Tendsto (fun A : Finset ℤ => ‖b-truncate A b‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using ((tendsto_const_nhds (x := b)).sub (tendsto_truncate hq b)).norm
  apply squeeze_zero (fun A => norm_nonneg
    (convolutionSandwichPotentialCLM (p := p) (truncate A a) (truncate A b) -
      convolutionSandwichPotentialCLM (p := p) a b))
    (fun A => norm_convolutionSandwichPotentialCLM_cutoff_sub_le a b A A)
  simpa only [zero_mul, mul_zero, zero_add] using (ha.mul_const ‖b‖).add (hb.const_mul ‖a‖)

/-- Compactness concerns variation of the potential in the operator-norm topology. -/
theorem isCompactOperator_convolutionSandwichPotentialCLM (hq : q ≠ ⊤) (a b : Coeff q) :
    IsCompactOperator (convolutionSandwichPotentialCLM (p := p) a b) := by
  apply isCompactOperator_of_tendsto (tendsto_convolutionSandwichPotentialCLM_cutoff hq a b)
  apply Eventually.of_forall
  intro A
  have he := convolutionSandwichPotentialCLM_cutoff_eq_comp (p := p) a b A A
  rw [he]
  exact (isCompactOperator_truncateCLM (p := p) (A.biUnion fun j => A.image fun k => j-k)).clm_comp
    (convolutionSandwichPotentialCLM (p := p) (truncate A a) (truncate A b))

/-- Bounded coefficientwise limits of potentials give operator-norm limits
of the actual convolution sandwiches. -/
theorem tendsto_convolutionSandwich_of_bounded_coefficientwise
    (hq : q ≠ ⊤) (a b : Coeff q) {α : Type*} {l : Filter α}
    (φ : α → Coeff p) (ψ : Coeff p)
    (hb : Bornology.IsBounded (range φ))
    (ht : ∀ n : ℤ, Tendsto (fun k => φ k n) l (𝓝 (ψ n))) :
    Tendsto (fun k => convolutionSandwich a (φ k) b) l (𝓝 (convolutionSandwich a ψ b)) := by
  classical
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  let C := max M 0 + ‖ψ‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hdiff (k : α) : ‖φ k-ψ‖ ≤ C := by
    have hk := hM _ ⟨k, rfl⟩
    have hd := norm_sub_le (φ k) ψ
    dsimp [C]
    linarith [le_max_left M 0]
  let T := convolutionSandwichPotentialCLM (p := p) a b
  let Tcut (A : Finset ℤ) := convolutionSandwichPotentialCLM (p := p) (truncate A a) (truncate A b)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have happrox := (Metric.tendsto_nhds (u := Tcut) (a := T)).mp
    (tendsto_convolutionSandwichPotentialCLM_cutoff (p := p) hq a b)
    (ε/(2*C)) (by positivity)
  obtain ⟨A, hA⟩ := happrox.exists
  have hA' : ‖T-Tcut A‖ < ε/(2*C) := by
    rw [dist_eq_norm (Tcut A) T, norm_sub_rev (Tcut A) T] at hA
    exact hA
  let F := A.biUnion fun j => A.image fun k => j-k
  have hcut : Tendsto (fun k => Tcut A (φ k)) l (𝓝 (Tcut A ψ)) := by
    have he := convolutionSandwichPotentialCLM_cutoff_eq_comp (p := p) a b A A
    have he' (v : Coeff p) : Tcut A v = Tcut A (truncate F v) :=
      congrArg (fun U : Coeff p →L[ℂ] (Coeff p →L[ℂ] Coeff 1) => U v) he
    have H := ((Tcut A).continuous.tendsto (truncate F ψ)).comp
      (tendsto_truncate_of_coefficientwise φ ψ ht F)
    rw [← he' ψ] at H
    exact H.congr' (Eventually.of_forall fun k => (he' (φ k)).symm)
  have hsmall := Metric.tendsto_nhds.mp hcut (ε/2) (half_pos hε)
  filter_upwards [hsmall] with k hk
  change dist (T (φ k)) (T ψ) < ε
  have hnorm : ‖(T-Tcut A) (φ k-ψ)‖ < ε/2 := by
    calc
      _ ≤ ‖T-Tcut A‖*‖φ k-ψ‖ := (T-Tcut A).le_opNorm _
      _ ≤ ‖T-Tcut A‖*C := mul_le_mul_of_nonneg_left (hdiff k) (norm_nonneg (T-Tcut A))
      _ < (ε/(2*C))*C := mul_lt_mul_of_pos_right hA' hC
      _ = ε/2 := by field_simp
  have he : T (φ k)-T ψ = (T-Tcut A) (φ k-ψ) + (Tcut A (φ k)-Tcut A ψ) := by
    simp only [map_sub, sub_apply]
    abel
  rw [dist_eq_norm, he]
  rw [dist_eq_norm] at hk
  exact (norm_add_le _ _).trans_lt (by linarith)

end NLS.Coeff
