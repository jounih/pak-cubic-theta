module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.NumberTheory.SumFourSquares
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-! Regression controls for the physical action argument. -/
public section
namespace CubicTheta
open Real

/-- The exact Gaussian control in the original temperature variable. The dual
exponentials have physical actions π² n² in the variable 1/t. -/
theorem square_physical_identity {t : ℝ} (ht : 0 < t) :
    (∑' n : ℤ, exp (-t*(n:ℝ)^2)) =
      1 / (t/π)^(1/2:ℝ) * ∑' n : ℤ, exp (-(π^2/t)*(n:ℝ)^2) := by
  convert Real.tsum_exp_neg_mul_int_sq (div_pos ht Real.pi_pos) using 2
  · funext n; congr 1; field_simp
  · congr 1; funext n; congr 1; field_simp

/-- Every nonfundamental square action collides with at most five strictly
smaller square actions. Zero summands may simply be deleted. -/
theorem square_collision_five (n : ℕ) (hn : 2 ≤ n) :
    ∃ a b c d : ℕ, a < n ∧ b < n ∧ c < n ∧ d < n ∧
       (n-1)^2 + a^2 + b^2 + c^2 + d^2 = n^2 := by
  obtain ⟨a,b,c,d,hs⟩ := Nat.sum_four_squares (2*n-1)
  have hpos : 1 ≤ 2*n := by omega
  have h1 := Nat.sub_add_cancel hpos
  have h2 := Nat.sub_add_cancel (show 1 ≤ n by omega)
  have bound (x : ℕ) (hx : x^2 ≤ 2*n-1) : x<n := by
    by_contra! h
    have hsq := Nat.pow_le_pow_left h 2
    nlinarith [Nat.zero_le ((n-1)*(n-1))]
  refine ⟨a,b,c,d,bound a (by omega),bound b (by omega),bound c (by omega),bound d (by omega),?_⟩
  nlinarith

/-- The cusp parametrization gives an exact singular-background test for a
first-order differential polynomial. Put u = exp(-p/2), y = u²+u³. -/
theorem cusp_separant_control (u : ℝ) (hu : 0 < u) :
    let y := u^2+u^3
    let z := -u^2-(3/2:ℝ)*u^3
    (3*y+2*z)^3-4*(y+z)^2 = 0 ∧
    0 < 6*(3*y+2*z)^2-8*(y+z) := by
  dsimp
  constructor
  · ring
  · convert (show 0 < 6*u^4+4*u^3 by positivity) using 1; ring

/-- Eliminate the independent variable as well as the exponential change of
coordinate: one more jet than the constant-field transcendence degree gives
an autonomous polynomial. The differential-field construction supplies the
dimension bound and the jet map. -/
theorem autonomous_relation_of_trdeg {E : Type} [Field E] [Algebra ℂ E]
    (d : ℕ) (bound : Algebra.trdeg ℂ E ≤ d) (jet : Fin (d+1) → E) :
    ∃ P : MvPolynomial (Fin (d+1)) ℂ, P ≠ 0 ∧ MvPolynomial.aeval jet P = 0 := by
  classical
  by_contra! h
  have hi : AlgebraicIndependent ℂ jet := algebraicIndependent_iff.mpr fun P hp ↦ by
    by_contra hn
    exact h P hn hp
  have hm := hi.cardinalMk_le_trdeg.trans bound
  simp at hm

end CubicTheta
