import NLS.ZakharovShabat.SourceAngularCosinePeriod

/-!
# Eta endpoint normalization and reflection of the cosine sheet

The actual cosine numerator is even. On the overlap of a convex angle
chart with its reflection, the primitive and its reflection sum to twice
the value at zero. The exact diagonal period therefore makes simultaneous
angle and root-sign reversal change eta by plus or minus two pi. The
terminal spectral point and the actual lifted root are unchanged.
This is compatibility of the two reflected local cosine sheets; general
spectral-path and gap-label gluing remain separate.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The diagonal representative on the reflected angle chart,
normalized at the left-endpoint angle minus pi. -/
def sourceAngularEtaReflectedCosineRepresentative (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (κ : ℂ) : ℂ × CoeffPair p → ℂ :=
  fun x => (κ * I) * sourceAngularCanonicalCosinePrimitive hp hp1 m m s (-x.1,x.2)

@[simp] theorem sourceAngularEtaReflectedCosineRepresentative_neg_pi
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (κ : ℂ) (ψ : CoeffPair p) :
    sourceAngularEtaReflectedCosineRepresentative hp hp1 m s κ (-(Real.pi : ℂ),ψ) = 0 := by
  simp only [sourceAngularEtaReflectedCosineRepresentative,neg_neg,
    sourceAngularCanonicalCosinePrimitive_pi,mul_zero]

/-- The reflected angle and reversed sign give exactly the same
normalized terminal value on the other covering chart. -/
theorem sourceAngularEtaReflectedCosineRepresentative_neg_neg
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (κ θ : ℂ) (ψ : CoeffPair p) :
    sourceAngularEtaReflectedCosineRepresentative hp hp1 m s (-κ) (-θ,ψ) =
      sourceAngularEtaCosineRepresentative hp hp1 m s κ (θ,ψ) := by
  simp only [sourceAngularEtaReflectedCosineRepresentative,sourceAngularEtaCosineRepresentative,neg_neg]

/-- Reflected angles have the same actual spectral cosine coordinate. -/
theorem sourceCanonicalCosinePoint_neg (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m : ℤ) (θ : ℂ) (ψ : CoeffPair p) :
    sourceCanonicalCosinePoint hp hp1 m (-θ,ψ) = sourceCanonicalCosinePoint hp hp1 m (θ,ψ) := by
  simp only [sourceCanonicalCosinePoint,cosineGapPoint,Complex.cos_neg]

/-- Reversing both the angle and sheet sign keeps the literal lifted
discriminant root, including at the singular endpoints. -/
theorem sourceAngularCosineLiftedRoot_neg_neg (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m : ℤ) (κ θ : ℂ) (ψ : CoeffPair p) :
    sourceAngularCosineLiftedRoot hp hp1 m (-κ) (-θ,ψ) =
      sourceAngularCosineLiftedRoot hp hp1 m κ (θ,ψ) := by
  simp only [sourceAngularCosineLiftedRoot,sourceCanonicalCosinePoint_neg,Complex.sin_neg]
  ring

namespace SourceAngularCanonicalCosineChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {W V : Set (CoeffPair p)}
  {Ω : Set ℂ} {c : ℤ → ℂ} {R : ℤ → ℝ}

/-- The reflected representative is jointly analytic on the entire
reflected chart, which contains the whole interval from minus pi to zero. -/
theorem analyticOnNhd_etaReflectedCosineRepresentative
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R) (κ : ℂ) :
    AnalyticOnNhd ℂ (sourceAngularEtaReflectedCosineRepresentative hp hp1 m s κ)
      (((fun θ : ℂ => -θ) ⁻¹' Ω) ×ˢ V) := by
  intro x hx
  exact analyticAt_const.mul ((D.primitive_analytic m (-x.1,x.2) ⟨hx.1,hx.2⟩).comp
    (f := fun x : ℂ × CoeffPair p => (-x.1,x.2)) (analyticAt_fst.neg.prod analyticAt_snd))

/-- The reflected normalization has the same regular angular
differential as the original chart with the same sheet sign. -/
theorem hasDerivAt_etaReflectedCosineRepresentative
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (κ θ : ℂ) (hθ : -θ ∈ Ω) :
    HasDerivAt (fun e => sourceAngularEtaReflectedCosineRepresentative hp hp1 m s κ (e,ψ))
      ((-κ * I) * sourceAngularGapNumerator hp hp1 m m s ψ
        (sourceCanonicalCosinePoint hp hp1 m (θ,ψ))) θ := by
  have h := ((D.primitive_derivative m ψ hψ (-θ) hθ).comp θ ((hasDerivAt_id θ).neg)).const_mul (κ * I)
  change HasDerivAt (fun e => sourceAngularEtaReflectedCosineRepresentative hp hp1 m s κ (e,ψ))
    ((κ * I) * (sourceAngularGapNumerator hp hp1 m m s ψ
      (sourceCanonicalCosinePoint hp hp1 m (-θ,ψ)) * (-1))) θ at h
  convert h using 1
  rw [sourceCanonicalCosinePoint_neg]
  ring

/-- Evenness of the actual cosine numerator gives the exact primitive
reflection identity on the overlap with the reflected angle chart. -/
theorem primitive_add_reflection
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (θ : ℂ)
    (hθ : θ ∈ Ω) (hnegθ : -θ ∈ Ω) :
    sourceAngularCanonicalCosinePrimitive hp hp1 n m s (θ,ψ) +
        sourceAngularCanonicalCosinePrimitive hp hp1 n m s (-θ,ψ) =
      2 * sourceAngularCanonicalCosinePrimitive hp hp1 n m s (0,ψ) := by
  let H : ℂ → ℂ := fun e => sourceAngularCanonicalCosinePrimitive hp hp1 n m s (e,ψ)
  let S := Ω ∩ (fun e : ℂ => -e) ⁻¹' Ω
  have hS : Convex ℝ S := D.angle_convex.inter
    (D.angle_convex.linear_preimage (-(LinearMap.id : ℂ →ₗ[ℝ] ℂ)))
  have h0Ω : (0 : ℂ) ∈ Ω := D.angle_segment (left_mem_segment ℝ _ _)
  have h0S : (0 : ℂ) ∈ S := ⟨h0Ω,show (-0 : ℂ) ∈ Ω by simpa only [neg_zero] using h0Ω⟩
  have hderiv (e : ℂ) (he : e ∈ S) : HasDerivAt (fun t => H t + H (-t)) 0 e := by
    have h := (D.primitive_derivative n ψ hψ e he.1).add
      ((D.primitive_derivative n ψ hψ (-e) he.2).comp e ((hasDerivAt_id e).neg))
    change HasDerivAt (fun t => H t + H (-t))
      (sourceAngularGapNumerator hp hp1 n m s ψ (sourceCanonicalCosinePoint hp hp1 m (e,ψ)) +
        sourceAngularGapNumerator hp hp1 n m s ψ (sourceCanonicalCosinePoint hp hp1 m (-e,ψ)) * (-1)) e at h
    simpa only [sourceCanonicalCosinePoint_neg,mul_neg,mul_one,add_neg_cancel] using h
  have hbound := hS.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun e he => (hderiv e he).hasDerivWithinAt)
    (fun _ _ => (by simp : ‖(0 : ℂ)‖ ≤ (0 : ℝ))) h0S (show θ ∈ S from ⟨hθ,hnegθ⟩)
  have hzero : (H θ + H (-θ)) - (H 0 + H (-0)) = 0 :=
    norm_eq_zero.mp (le_antisymm (by simpa only [zero_mul] using hbound) (norm_nonneg _))
  simpa only [neg_zero,← two_mul] using sub_eq_zero.mp hzero

/-- The diagonal period fixes the right-endpoint value on either eta
sheet, while the left anchor has its original zero normalization. -/
theorem etaCosineRepresentative_zero_angle
    (ψ : CoeffPair p) (hperiod : sourceAngularCanonicalCosinePrimitive hp hp1 m m s (0,ψ) =
      -I * (Real.pi : ℂ)) (κ : ℂ) :
    sourceAngularEtaCosineRepresentative hp hp1 m s κ (0,ψ) = -κ * (Real.pi : ℂ) := by
  rw [sourceAngularEtaCosineRepresentative,hperiod]
  calc
    _ = κ * (I * I) * (Real.pi : ℂ) := by ring
    _ = -κ * (Real.pi : ℂ) := by rw [I_mul_I]; ring

/-- The two reflected cosine sheets give eta values differing by
exactly twice the signed pi period. This preserves the terminal root. -/
theorem etaCosineRepresentative_reflection
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V)
    (hperiod : sourceAngularCanonicalCosinePrimitive hp hp1 m m s (0,ψ) = -I * (Real.pi : ℂ))
    (θ κ : ℂ) (hθ : θ ∈ Ω) (hnegθ : -θ ∈ Ω) :
    sourceAngularEtaCosineRepresentative hp hp1 m s (-κ) (-θ,ψ) =
      sourceAngularEtaCosineRepresentative hp hp1 m s κ (θ,ψ) + 2 * κ * (Real.pi : ℂ) := by
  let H : ℂ → ℂ := fun e => sourceAngularCanonicalCosinePrimitive hp hp1 m m s (e,ψ)
  have hsum := D.primitive_add_reflection ψ hψ m θ hθ hnegθ
  have hneg : H (-θ) = 2 * H 0 - H θ := by linear_combination hsum
  simp only [sourceAngularEtaCosineRepresentative,neg_neg]
  change κ * I * H (-θ) = (-κ * I) * H θ + 2 * κ * (Real.pi : ℂ)
  have hH₀ : H 0 = -I * (Real.pi : ℂ) := hperiod
  rw [hneg,hH₀]
  change κ * I * (2 * (-I * (Real.pi : ℂ)) - H θ) =
    (-κ * I) * H θ + 2 * κ * (Real.pi : ℂ)
  calc
    _ = (-κ * I) * H θ - 2 * κ * (I * I) * (Real.pi : ℂ) := by ring
    _ = _ := by rw [I_mul_I]; ring

/-- With either allowed sheet sign the reflected eta representatives
agree modulo two pi, and hence also modulo pi. -/
theorem etaCosineRepresentative_reflection_mod_two_pi
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V)
    (hperiod : sourceAngularCanonicalCosinePrimitive hp hp1 m m s (0,ψ) = -I * (Real.pi : ℂ))
    (θ κ : ℂ) (hθ : θ ∈ Ω) (hnegθ : -θ ∈ Ω) (hκ : κ = 1 ∨ κ = -1) :
    ∃ k : ℤ, sourceAngularEtaCosineRepresentative hp hp1 m s (-κ) (-θ,ψ) =
      sourceAngularEtaCosineRepresentative hp hp1 m s κ (θ,ψ) + (k : ℂ) * (2 * (Real.pi : ℂ)) := by
  have h := D.etaCosineRepresentative_reflection ψ hψ hperiod θ κ hθ hnegθ
  rcases hκ with rfl | rfl
  · exact ⟨1,by simpa only [Int.cast_one,mul_one,one_mul] using h⟩
  · refine ⟨-1,?_⟩
    simpa only [Int.cast_neg,Int.cast_one,mul_neg,mul_one,neg_mul,one_mul] using h

/-- On the two charts' overlap their left-endpoint normalizations
differ by twice the signed pi period. -/
theorem etaReflectedCosineRepresentative_eq_add_period
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V)
    (hperiod : sourceAngularCanonicalCosinePrimitive hp hp1 m m s (0,ψ) = -I * (Real.pi : ℂ))
    (θ κ : ℂ) (hθ : θ ∈ Ω) (hnegθ : -θ ∈ Ω) :
    sourceAngularEtaReflectedCosineRepresentative hp hp1 m s κ (θ,ψ) =
      sourceAngularEtaCosineRepresentative hp hp1 m s κ (θ,ψ) + 2 * κ * (Real.pi : ℂ) := by
  simpa only [sourceAngularEtaReflectedCosineRepresentative,sourceAngularEtaCosineRepresentative,neg_neg]
    using D.etaCosineRepresentative_reflection ψ hψ hperiod θ κ hθ hnegθ

/-- Either allowed sheet sign gives the same eta class modulo two pi
on the overlap of the original and reflected normalized charts. -/
theorem etaReflectedCosineRepresentative_eq_mod_two_pi
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V)
    (hperiod : sourceAngularCanonicalCosinePrimitive hp hp1 m m s (0,ψ) = -I * (Real.pi : ℂ))
    (θ κ : ℂ) (hθ : θ ∈ Ω) (hnegθ : -θ ∈ Ω) (hκ : κ = 1 ∨ κ = -1) :
    ∃ k : ℤ, sourceAngularEtaReflectedCosineRepresentative hp hp1 m s κ (θ,ψ) =
      sourceAngularEtaCosineRepresentative hp hp1 m s κ (θ,ψ) + (k : ℂ) * (2 * (Real.pi : ℂ)) := by
  simpa only [sourceAngularEtaReflectedCosineRepresentative,sourceAngularEtaCosineRepresentative,neg_neg]
    using D.etaCosineRepresentative_reflection_mod_two_pi ψ hψ hperiod θ κ hθ hnegθ hκ

/-- The reflected local normalizations in particular agree modulo pi,
the period used for source analyticity in Theorem 13.1(ii). -/
theorem etaReflectedCosineRepresentative_eq_mod_pi
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V)
    (hperiod : sourceAngularCanonicalCosinePrimitive hp hp1 m m s (0,ψ) = -I * (Real.pi : ℂ))
    (θ κ : ℂ) (hθ : θ ∈ Ω) (hnegθ : -θ ∈ Ω) (hκ : κ = 1 ∨ κ = -1) :
    ∃ k : ℤ, sourceAngularEtaReflectedCosineRepresentative hp hp1 m s κ (θ,ψ) =
      sourceAngularEtaCosineRepresentative hp hp1 m s κ (θ,ψ) + (k : ℂ) * (Real.pi : ℂ) := by
  obtain ⟨k,hk⟩ := D.etaReflectedCosineRepresentative_eq_mod_two_pi ψ hψ hperiod θ κ hθ hnegθ hκ
  refine ⟨2 * k,?_⟩
  rw [Int.cast_mul,Int.cast_ofNat]
  linear_combination hk

end SourceAngularCanonicalCosineChartData
end NLS.ZakharovShabat
