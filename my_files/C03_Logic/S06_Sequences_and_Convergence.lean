import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_iff_left₀ _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn

  calc
    |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by
      congr
      ring
    _ ≤ |s n - a| + |t n - b| := by
      apply abs_add_le (s n - a) (t n - b)
    _ < ε/2 + ε/2 := by
      have h1 : |s n - a| < ε/2 := by
        have : n ≥ Ns := le_of_max_le_left hn
        exact hs n this
      have h2 : |t n - b| < ε/2 := by
        have : n ≥ Nt := le_of_max_le_right hn
        exact ht n this
      exact add_lt_add h1 h2
    _ = ε := by
      norm_num

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  · have acpos : 0 < |c| := abs_pos.mpr h
    intro ε εpos
    have : ε / |c| > 0 := by exact div_pos εpos acpos
    rcases cs (ε/|c|) this with ⟨N, hN⟩
    use N
    intro n hn

    calc
      |c * s n - c * a| = |c * (s n - a)| := by rw [← mul_sub]
      _ = |c| * |s n - a| := by exact abs_mul c (s n - a)
      _ < |c| * (ε/|c|) := by exact (mul_lt_mul_iff_of_pos_left acpos).mpr (hN n hn)
      _ = ε := by
        have : |c| ≠ 0 := by exact abs_ne_zero.mpr h
        exact mul_div_cancel₀ ε this

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, hN⟩
  use N, |a| + 1
  intro n hn
  calc
    |s n| = |s n - a + a| := by ring_nf
    _ ≤ |s n - a| + |a| := by exact abs_add_le (s n - a) a
    _ < 1 + |a| := by exact (add_lt_add_iff_right |a|).mpr (hN n hn)
    _ = |a| + 1 := by rw[add_comm]

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct (ε/B) pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n hn
  calc
    |s n * t n - 0| = |s n * t n| := by rw [sub_zero]
    _ = |s n| * |t n| := by exact abs_mul (s n) (t n)
    _ < B * (ε/B) := by
      have h0 : |s n| < B := by
        have : n ≥ N₀ := by exact le_of_max_le_left hn
        exact h₀ n this
      have h1 : |t n| < ε/B := by
        have : n ≥ N₁ := by exact le_of_max_le_right hn
        have : |t n - 0| < ε/B := by exact h₁ n this
        rw [← sub_zero (t n)]
        exact this
      exact mul_lt_mul_of_nonneg h0 h1 (abs_nonneg _) (abs_nonneg _)
    _ = ε := by
      have : B ≠ 0 := by
        symm
        exact ne_of_lt Bpos
      exact mul_div_cancel₀ ε this

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by exact abs_sub_pos.mpr abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    have : N ≥ Na := by exact le_max_left _ _
    exact hNa N this
  have absb : |s N - b| < ε := by
    have : N ≥ Nb := by exact le_max_right _ _
    exact hNb N this

  have h1 : |a - b| ≤ |s N - a| + |s N - b| := by
    calc
      |a - b| = |a - b + s N - s N| := by ring_nf
      _ = |(a - s N) + (s N - b)| := by ring_nf
      _ ≤ |a - s N| + |s N - b| := by exact abs_add_le _ _
      _ = |s N - a| + |s N - b| := by rw [abs_sub_comm]

  have h2 : |s N - a| + |s N - b| < |a - b| := by
    calc
      |s N - a| + |s N - b| < ε + ε := by exact add_lt_add absa absb
      _ = |a - b|/2 + |a-b|/2 := by dsimp
      _ = |a - b| := by exact add_halves _

  have : |a - b| < |a - b| := by exact lt_of_le_of_lt h1 h2
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
