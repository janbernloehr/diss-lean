import NLS.Poisson.GardnerHamiltonianDirection

noncomputable section
set_option autoImplicit false
open Complex
namespace NLS.Poisson

/-- The positive 2*i signed complex matrix gives the canonical real
orientation X=(Z+W)/2, Y=i*(Z-W)/2, physically (Re Z,-Im Z). -/
theorem realCartesianMatrix_of_signed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (B : E →L[ℂ] E →L[ℂ] ℂ) (L W G H : E) (d : ℂ)
    (hLG : B L G = 0) (hLH : B L H = 2*I*d)
    (hWG : B W G = -(2*I)*d) (hWH : B W H = 0) :
    B ((1/2 : ℂ) • (L+W)) ((1/2 : ℂ) • (G+H)) = 0 ∧
    B ((1/2 : ℂ) • (L+W)) ((I/2) • (G-H)) = d ∧
    B ((I/2) • (L-W)) ((1/2 : ℂ) • (G+H)) = -d ∧
    B ((I/2) • (L-W)) ((I/2) • (G-H)) = 0 := by
  simp only [map_smul,smul_apply,smul_eq_mul,map_add,map_sub,add_apply,sub_apply,hLG,hLH,hWG,hWH]
  constructor
  · ring
  constructor
  · ring_nf
    simp only [I_sq]
    ring
  constructor
  · ring_nf
    simp only [I_sq]
    ring
  · ring

end NLS.Poisson
