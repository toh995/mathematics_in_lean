import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

example : min (min a b) c = min a (min b c) := by
  have h0 : min (min a b) c ≤ min a (min b c) := by
    have ha : min (min a b) c ≤ a := le_trans (min_le_left (min a b) c) (min_le_left a b)
    have hb : min (min a b) c ≤ b := le_trans (min_le_left (min a b) c) (min_le_right a b)
    have hc : min (min a b) c ≤ c := min_le_right (min a b) c
    apply le_min
    · apply ha
    · apply le_min hb hc

  have h1 : min a (min b c) ≤ min (min a b) c := by
    have ha : min a (min b c) ≤ a := min_le_left a (min b c)
    have hb : min a (min b c) ≤ b := le_trans (min_le_right a (min b c)) (min_le_left b c)
    have hc : min a (min b c) ≤ c := le_trans (min_le_right a (min b c)) (min_le_right b c)
    apply le_min
    · apply le_min ha hb
    · apply hc

  apply le_antisymm h0 h1


theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · apply add_le_add_left (min_le_left a b)
  · apply add_le_add_left (min_le_right a b)

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  · have h : min (a + c) (b + c) + (-c) ≤ min (a + c + (-c)) (b + c + (-c)) := by
      apply le_min
      · apply add_le_add_left (min_le_left (a+c) (b+c))
      · apply add_le_add_left (min_le_right (a+c) (b+c))
    repeat rw[add_neg_cancel_right] at h
    linarith

#check (abs_add_le : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have h : |(a - b) + b| ≤ |a - b| + |b| := by apply abs_add_le
  rw [sub_add_cancel] at h
  linarith
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  have h0 : x ∣ y * (x * z) := by
    have h : y * (x * z) = x * (y * z) := by ring
    rw[h]
    apply dvd_mul_right
  have h1 : ∀ n : ℕ, n ∣ n^2 := by
    intro n
    apply dvd_mul_left
  have h2 : x ∣ w^2 := by
    apply dvd_trans h (h1 w)

  apply dvd_add (dvd_add h0 (h1 x)) h2
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  have h : ∀ n m : ℕ, Nat.gcd n m ∣ Nat.gcd m n := by
    intro n m
    have h1 : Nat.gcd n m ∣ m := Nat.gcd_dvd_right n m
    have h2 : Nat.gcd n m ∣ n := Nat.gcd_dvd_left n m
    apply Nat.dvd_gcd h1 h2

  apply Nat.dvd_antisymm (h m n) (h n m)
end
