import NLS.KdV.PseudomeasureWideSolutionRegularity

/-! The exact complementary Q-equation, its unique full-H1 solution and
the identity Vv=KT h. This also records the stronger s+2,infinity realization. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

def EndpointComplementEquation (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) (n : ℕ) (z : ℂ)
    (q h : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (v : FourierLebesgueSpace (2:ℝ) 1 2) : Prop :=
  endpointHillH1Coordinates n v=0 ∧ ∀ k : ℤ, k.natAbs≠n →
    (z-(freeHillValue k:ℂ))*v.val (mode (-k))=(endpointH1Multiplication r hr hr1 q v).val k+h.val k

theorem endpointH1Multiplication_resolventFamily_wide (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 2≤n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) :
    endpointH1Multiplication r hr hr1 q (endpointH1ResolventFamily r hr1 n z a)=
      wideEndpointHillPerturbation SpectralWeight.one r hr hr1 n hn z hz q a := by
  rw [endpointH1ResolventFamily_eq_wide r hr1 n hn z hz]
  exact congrArg (fun T => T a) (endpointH1Multiplication_wideResolvent r hr hr1 n hn z hz q)

variable (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) (n : ℕ) (hn : 2≤n)
variable (z : ℂ) (hz : z ∈ wideHillStrip n)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
variable (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

include hn hz in
theorem endpointComplementEquation_free_reconstruct
    (h : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (v : FourierLebesgueSpace (2:ℝ) 1 2) (hv : EndpointComplementEquation r hr hr1 n z q h v) :
    v=endpointH1ResolventFamily r hr1 n z (endpointH1Multiplication r hr hr1 q v+h) := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  rw [endpointH1ResolventFamily_coefficient_wide r hr1 n hn z hz]
  by_cases hk : k.natAbs=n
  · rw [wideHillSymbol,if_pos hk,zero_mul]
    rcases (hill_resonance_iff n k).mp hk with rfl|rfl
    · exact congrArg Prod.fst hv.1
    · have he := congrArg Prod.snd hv.1
      change v.val (mode (-(-(n:ℤ))))=(0:ℂ) at he
      simpa only [neg_neg] using he
  · simp only [wideHillSymbol,if_neg hk,WeightedCoeff.add_val]
    rw [← hv.2 k hk,← mul_assoc,inv_mul_cancel₀ (wideHill_denominator_ne_zero n hn z hz k hk),one_mul]

include hn hz hs in
theorem endpointComplementEquation_unique
    (h : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (v : FourierLebesgueSpace (2:ℝ) 1 2) (hv : EndpointComplementEquation r hr hr1 n z q h v) :
    v=endpointResponseFamily r hr hr1 n (q,z) h := by
  have he := endpointComplementEquation_free_reconstruct r hr hr1 n hn z hz q h v hv
  have hV : endpointH1Multiplication r hr hr1 q v=
      wideEndpointHillPerturbation SpectralWeight.one r hr hr1 n hn z hz q
        (endpointH1Multiplication r hr hr1 q v+h) := by
    calc
      _ = endpointH1Multiplication r hr hr1 q
          (endpointH1ResolventFamily r hr1 n z (endpointH1Multiplication r hr hr1 q v+h)) :=
        congrArg (endpointH1Multiplication r hr hr1 q) he
      _ = _ := endpointH1Multiplication_resolventFamily_wide r hr hr1 n hn z hz q _
  have ha := wideEndpointHillTailInverse_unique SpectralWeight.one r hr hr1 n hn z hz q hs
    (endpointH1Multiplication r hr hr1 q v+h) h (by rw [← hV]; abel)
  rw [← endpointInverseFamily_eq_wide r hr hr1 n hn (q,z) hz hs] at ha
  rw [ha] at he
  exact he

include hn hz hs in
theorem endpointResponseFamily_complement_equation
    (h : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) :
    EndpointComplementEquation r hr hr1 n z q h (endpointResponseFamily r hr hr1 n (q,z) h) := by
  let a := endpointInverseFamily r hr hr1 n (q,z) h
  have hK : a-wideEndpointHillPerturbation SpectralWeight.one r hr hr1 n hn z hz q a=h := by
    simpa only [a,endpointInverseFamily_eq_wide r hr hr1 n hn (q,z) hz hs] using
      wideEndpointHillTailInverse_right SpectralWeight.one r hr hr1 n hn z hz q hs h
  constructor
  · have hc := congrArg (fun T => T h) (endpointResponseFamily_coordinates_wide r hr hr1 n hn z hz q)
    simpa only [ContinuousLinearMap.comp_apply,_root_.zero_apply] using hc
  · intro k hk
    change (z-(freeHillValue k:ℂ))*(endpointH1ResolventFamily r hr1 n z a).val (mode (-k))=_
    rw [endpointH1ResolventFamily_coefficient_wide r hr1 n hn z hz,wideHillSymbol,if_neg hk,
      ← mul_assoc,mul_inv_cancel₀ (wideHill_denominator_ne_zero n hn z hz k hk),one_mul]
    have he := congrArg (fun b : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ => b.val k) hK
    change a.val k-(wideEndpointHillPerturbation SpectralWeight.one r hr hr1 n hn z hz q a).val k=h.val k at he
    have hV := endpointH1Multiplication_resolventFamily_wide r hr hr1 n hn z hz q a
    change a.val k=(endpointH1Multiplication r hr hr1 q (endpointH1ResolventFamily r hr1 n z a)).val k+h.val k
    rw [hV]
    exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

include hn hz hs in
theorem existsUnique_endpointComplementEquation
    (h : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) :
    ∃! v : FourierLebesgueSpace (2:ℝ) 1 2, EndpointComplementEquation r hr hr1 n z q h v :=
  ⟨endpointResponseFamily r hr hr1 n (q,z) h,
    endpointResponseFamily_complement_equation r hr hr1 n hn z hz q hs h,
    fun v hv => endpointComplementEquation_unique r hr hr1 n hn z hz q hs h v hv⟩

include hn hz hs in
theorem endpointResponseFamily_potential_KT
    (h : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) :
    endpointH1Multiplication r hr hr1 q (endpointResponseFamily r hr hr1 n (q,z) h)=
      endpointInverseFamily r hr hr1 n (q,z)
        (wideEndpointHillPerturbation SpectralWeight.one r hr hr1 n hn z hz q h) := by
  let K := endpointInverseFamily r hr hr1 n (q,z)
  let T := wideEndpointHillPerturbation SpectralWeight.one r hr hr1 n hn z hz q
  have hright : K h-T (K h)=h := by
    simpa only [K,T,endpointInverseFamily_eq_wide r hr hr1 n hn (q,z) hz hs] using
      wideEndpointHillTailInverse_right SpectralWeight.one r hr hr1 n hn z hz q hs h
  have hleft : K (h-T h)=h := by
    simpa only [K,T,endpointInverseFamily_eq_wide r hr hr1 n hn (q,z) hz hs] using
      wideEndpointHillTailInverse_left SpectralWeight.one r hr hr1 n hn z hz q hs h
  rw [map_sub] at hleft
  have he : T (K h)=K (T h) := by
    have ha : K h=h+K (T h) := sub_eq_iff_eq_add.mp hleft
    have hb : K h=h+T (K h) := sub_eq_iff_eq_add.mp hright
    exact add_left_cancel (hb.symm.trans ha)
  change endpointH1Multiplication r hr hr1 q (endpointH1ResolventFamily r hr1 n z (K h))=_
  rw [endpointH1Multiplication_resolventFamily_wide r hr hr1 n hn z hz q]
  exact he

end NLS.KdV
