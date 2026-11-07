import NLS.SequenceSpaces.AnalyticAmplitudeSquareError
import NLS.ComplexAnalysis.AnalyticDomainPullback

/-! Original physical values and an exact source inclusion identify
squared amplitude germs on ONE complex source neighborhood. All source
spaces and physical representatives remain opaque in this proof. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.WeightedCoeff

theorem exists_physical_amplitude_square_pullback
    (v : Weight) (hv : ∀ j,v (-j)=v j)
    {Q I : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    (L : WeightedCoeff v 2 →L[ℂ] Q) (D : Set Q) (hD : IsOpen D)
    (A : Q → Coeff ⊤) (hAa : AnalyticOnNhd ℂ A D)
    (a : ℕ+ → ℝ) (d : ℕ+ → ℂ) (s : I → Q) (T : ℕ+ → I → ℂ)
    (hphysical : ∀ i,s i∈D → ∀ n : ℕ+,(A (s i) (n:ℤ)/(a n:ℂ))^2=d n*T n i)
    (hfiber : ∀ p : WeightedCoeff v 2,conjugateReflection v hv p=p → ∃ i,s i=L p)
    (V : Set (WeightedCoeff v 2)) (hV : IsOpen V)
    (q : WeightedCoeff v 2) (hqV : q∈V) (hqD : L q∈D) (hJq : conjugateReflection v hv q=q)
    (R : ℕ+ → WeightedCoeff v 2 → ℂ) (N : ℕ) (K : ℝ)
    (hd : ∀ n,d n=2*((Real.pi:ℂ)*(n:ℕ)))
    (hR : ∀ n : ℕ+,N≤(n:ℕ) → AnalyticOnNhd ℂ (R n) V ∧
      (∀ p∈V,(1+(n:ℝ))*‖d n*R n p-1‖≤K) ∧
      ∀ i,∀ p∈V,s i=L p → R n p=T n i) :
    ∃ U : Set (WeightedCoeff v 2),IsOpen U ∧ q∈U ∧ (∀ p∈U,L p∈D) ∧
      ∀ n : ℕ+,N≤(n:ℕ) → ∀ p∈U,(1+(n:ℝ))*‖(A (L p) (n:ℤ)/(a n:ℂ))^2-1‖≤K := by
  let W := L ⁻¹' D
  have he (n : ℕ+) (hn : N≤(n:ℕ)) (p) (hp : p∈V∩W) (hr : conjugateReflection v hv p=p) :
      (A (L p) (n:ℤ)/(a n:ℂ))^2=(2*((Real.pi:ℂ)*(n:ℕ)))*R n p := by
    obtain ⟨i,hi⟩ := hfiber p hr
    have hiD : s i∈D := hi ▸ hp.2
    calc
      _ = (A (s i) (n:ℤ)/(a n:ℂ))^2 := congrArg (fun z : Q => (A z (n:ℤ)/(a n:ℂ))^2) hi.symm
      _ = d n*T n i := hphysical i hiD n
      _ = (2*((Real.pi:ℂ)*(n:ℕ)))*R n p := by rw [hd n,(hR n hn).2.2 i p hp.1 hi]
  obtain ⟨U,hU,hqU,hUV,heU⟩ := exists_local_analytic_amplitude_square_error v hv V W hV
    (hD.preimage L.continuous) q hqV hqD hJq (fun p => A (L p))
    (NLS.ComplexAnalysis.analyticOnNhd_clm_preimage L A D hAa) a R N K
    (fun n hn => ⟨(hR n hn).1,by simpa only [←hd n] using (hR n hn).2.1⟩) he
  exact ⟨U,hU,hqU,(fun p hp => (hUV hp).2),heU⟩

end NLS.WeightedCoeff
