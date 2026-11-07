import NLS.KdV.PseudomeasureWideComplementEquation

/-! Complete complementary and inhomogeneous source assertions with the
printed sign (L-lambda)f=g and the stronger endpoint regularity. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

def EndpointComplementResult (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) (n : ℕ) (hn : 2≤n)
    (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q h : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) : Prop :=
  ∃ v : FourierLebesgueSpace (2:ℝ) 1 2,
    EndpointComplementEquation r hr hr1 n z q h v ∧
    (∀ w : FourierLebesgueSpace (2:ℝ) 1 2, EndpointComplementEquation r hr hr1 n z q h w → w=v) ∧
    (∀ w : FourierLebesgueSpace (2:ℝ) (2-r) ⊤,
      EndpointComplementEquation r hr hr1 n z q h (endpointSecondOrderH1Inclusion r hr1 w) → w.val=v.val) ∧
    (∃ v₂ : FourierLebesgueSpace (2:ℝ) (2-r) ⊤, v₂.val=v.val) ∧
    v=endpointResponseFamily r hr hr1 n (q,z) h ∧
    endpointH1Multiplication r hr hr1 q v=
      endpointInverseFamily r hr hr1 n (q,z)
        (wideEndpointHillPerturbation SpectralWeight.one r hr hr1 n hn z hz q h)

theorem endpointComplementResult (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) (n : ℕ) (hn : 2≤n)
    (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q h : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    EndpointComplementResult r hr hr1 n hn z hz q h := by
  refine ⟨endpointResponseFamily r hr hr1 n (q,z) h,
    endpointResponseFamily_complement_equation r hr hr1 n hn z hz q hs h,
    fun w hw => endpointComplementEquation_unique r hr hr1 n hn z hz q hs h w hw,
    ?_,
    endpointH1ResolventFamily_secondOrder_wide r hr1 n hn z hz (endpointInverseFamily r hr hr1 n (q,z) h),
    rfl,endpointResponseFamily_potential_KT r hr hr1 n hn z hz q hs h⟩
  intro w hw
  have he := endpointComplementEquation_unique r hr hr1 n hn z hz q hs h
    (endpointSecondOrderH1Inclusion r hr1 w) hw
  exact (endpointSecondOrderH1Inclusion_val r hr1 w).symm.trans (congrArg Subtype.val he)

def EndpointInhomogeneousResult (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) (n : ℕ) (z : ℂ)
    (q g : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (u : ℂ × ℂ) : Prop :=
  let f := endpointReconstructionFamily r hr hr1 n (q,z) u-endpointResponseFamily r hr hr1 n (q,z) g
  (singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f-
      z • singularHillDomainInclusion f=endpointHillHminusOne SpectralWeight.one r hr1 g ↔
    endpointReducedFamily r hr hr1 n (q,z) u=
      -hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n
        (endpointInverseFamily r hr hr1 n (q,z) g)) ∧
  ∃ f₂ : FourierLebesgueSpace (2:ℝ) (2-r) ⊤, f₂.val=f.val

private theorem source_pencil_sign {E : Type*} [AddCommGroup E] (a b c : E) :
    b-a=c ↔ a-b= -c := by
  constructor <;> intro h <;> have he := congrArg (fun x : E => -x) h <;>
    simpa only [neg_sub,neg_neg] using he

theorem endpointInhomogeneousResult (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) (n : ℕ) (hn : 2≤n)
    (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q g : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (u : ℂ × ℂ)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    EndpointInhomogeneousResult r hr hr1 n z q g u := by
  let f := endpointReconstructionFamily r hr hr1 n (q,z) u-endpointResponseFamily r hr hr1 n (q,z) g
  have h := endpointPhysicalPencil_reconstruction_iff_wide r hr hr1 n hn z hz q hs (-g) u
  have hform : (z • singularHillDomainInclusion f-
      singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f=
        -endpointHillHminusOne SpectralWeight.one r hr1 g) ↔
      endpointReducedFamily r hr hr1 n (q,z) u=
        -hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n
          (endpointInverseFamily r hr hr1 n (q,z) g) := by
    simpa only [f,map_neg,sub_eq_add_neg,endpointPhysicalPencilFamily,_root_.sub_apply,_root_.smul_apply,_root_.add_apply,_root_.neg_apply] using h
  refine ⟨(source_pencil_sign _ _ _).trans hform,?_⟩
  have hreg := endpointReconstruction_response_secondOrder_wide r hr hr1 n hn z hz q (-g) u
  simpa only [map_neg,sub_eq_add_neg] using hreg

/-- The printed sign convention also describes every original H1 solution. -/
def EndpointInhomogeneousFullResult (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) (n : ℕ) (z : ℂ)
    (q g : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) : Prop :=
  ∀ f : FourierLebesgueSpace (2:ℝ) 1 2,
    singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f-
      z • singularHillDomainInclusion f=endpointHillHminusOne SpectralWeight.one r hr1 g ↔
    f=endpointReconstructionFamily r hr hr1 n (q,z) (endpointHillH1Coordinates n f)-
        endpointResponseFamily r hr hr1 n (q,z) g ∧
      endpointReducedFamily r hr hr1 n (q,z) (endpointHillH1Coordinates n f)=
        -hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n
          (endpointInverseFamily r hr hr1 n (q,z) g)

theorem endpointInhomogeneousFullResult (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) (n : ℕ) (hn : 2≤n)
    (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q g : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    EndpointInhomogeneousFullResult r hr hr1 n z q g := by
  intro f
  have h := endpointPhysicalPencil_inhomogeneous_iff_wide r hr hr1 n hn z hz q hs (-g) f
  have hform : (z • singularHillDomainInclusion f-
      singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f=
        -endpointHillHminusOne SpectralWeight.one r hr1 g) ↔
      f=endpointReconstructionFamily r hr hr1 n (q,z) (endpointHillH1Coordinates n f)-
        endpointResponseFamily r hr hr1 n (q,z) g ∧
      endpointReducedFamily r hr hr1 n (q,z) (endpointHillH1Coordinates n f)=
        -hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n
          (endpointInverseFamily r hr hr1 n (q,z) g) := by
    simpa only [map_neg,sub_eq_add_neg,endpointPhysicalPencilFamily,_root_.sub_apply,_root_.smul_apply,
      _root_.add_apply,_root_.neg_apply] using h
  exact (source_pencil_sign _ _ _).trans hform

end NLS.KdV
