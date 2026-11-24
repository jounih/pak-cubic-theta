module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! The unconditional linear case of Pak's conjecture, directly on coefficients. -/
public section
namespace CubicTheta
open Finset Polynomial

/-- The coefficient of q^k in q^j P(q d/dq) H, where H = ∑ q^(m³). -/
noncomputable def cubeEulerCoeff (P : Polynomial ℂ) (j k : ℕ) : ℂ := by
  classical
  exact if ∃ t : ℕ, t^3 + j = k then P.eval ((k-j : ℕ) : ℂ) else 0

private theorem isolate_cube {m r i j t : ℕ} (hm : r < m) (hi : i ≤ r) (hj : j ≤ r)
    (h : t^3 + i = m^3 + j) : t = m ∧ i = j := by
  have ht : t = m := by
    rcases lt_trichotomy t m with hlt | heq | hgt
    · have hfar : t^3 + m ≤ m^3 := by
        obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le (show t+1 ≤ m by omega)
        rw [hd]; ring_nf; omega
      omega
    · exact heq
    · have hs : (m+1)^3 ≤ t^3 := Nat.pow_le_pow_left (by omega) 3
      have : m^3 + m < (m+1)^3 := by nlinarith
      omega
  exact ⟨ht, by simpa [ht] using h⟩

/-- Even eventual vanishing forces every Euler-polynomial coefficient to vanish.
Consequently a linear differential operator with polynomial coefficients cannot
map the cube series to a polynomial unless the operator itself is zero. -/
theorem no_eventual_linear_ode (r N : ℕ) (P : ℕ → Polynomial ℂ)
    (h : ∀ k ≥ N, ∑ i ∈ range (r+1), cubeEulerCoeff (P i) i k = 0) :
    ∀ j ≤ r, P j = 0 := by
  classical
  intro j hj
  let m (l : ℕ) := l + r + N + 1
  have roots (l : ℕ) : (P j).eval (((m l)^3 : ℕ) : ℂ) = 0 := by
    let k := (m l)^3 + j
    have hm : r < m l := by dsimp [m]; omega
    have hpos : 1 ≤ m l := by omega
    have hcube : m l ≤ (m l)^3 := by
      calc m l = (m l)^1 := by simp
           _ ≤ _ := Nat.pow_le_pow_right hpos (by decide : 1 ≤ 3)
    have hk : N ≤ k := by dsimp [m,k] at *; omega
    have hz := h k hk
    rw [sum_eq_single j] at hz
    · simpa [cubeEulerCoeff, k, show ∃ t, t^3 + j = (m l)^3 + j from ⟨m l,rfl⟩] using hz
    · intro i hi hne
      have hnot : ¬∃ t, t^3+i=k := by
        rintro ⟨t,ht⟩
        exact hne (isolate_cube hm (by simpa using hi) hj ht).2
      simp [cubeEulerCoeff, hnot]
    · simpa [mem_range] using (show ¬ j < r+1 → cubeEulerCoeff (P j) j k = 0 by omega)
  apply (P j).eq_zero_of_infinite_isRoot
  have inj : Function.Injective (fun l : ℕ ↦ (((m l)^3 : ℕ) : ℂ)) := by
    intro l l' heq
    change (((m l)^3 : ℕ) : ℂ) = (((m l')^3 : ℕ) : ℂ) at heq
    have hnat : (m l)^3 = (m l')^3 := by exact_mod_cast heq
    have hstrict : StrictMono (fun t : ℕ ↦ t^3) := fun _ _ hlt ↦ Nat.pow_lt_pow_left hlt (by decide)
    have hm := hstrict.injective hnat
    dsimp [m] at hm
    omega
  exact (Set.infinite_range_of_injective inj).mono (by rintro _ ⟨l,rfl⟩; exact roots l)

end CubicTheta
