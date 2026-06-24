import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  have h : ∀ a b : α, a ⊓ b ≤ b ⊓ a := by
    intro a b
    apply le_inf inf_le_right inf_le_left
  apply le_antisymm (h x y) (h y x)

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  have h1 : x ⊓ y ⊓ z ≤ x ⊓ (y ⊓ z) := by
    have g1 : x ⊓ y ⊓ z ≤ x := by
      trans (x ⊓ y)
      · apply inf_le_left
      · apply inf_le_left
    have g2 : x ⊓ y ⊓ z ≤ y ⊓ z := by
      apply le_inf
      · trans (x ⊓ y)
        · apply inf_le_left
        · apply inf_le_right
      · apply inf_le_right
    apply le_inf g1 g2
  have h2 : x ⊓ (y ⊓ z) ≤ x ⊓ y ⊓ z:= by
    have g1 : x ⊓ (y ⊓ z) ≤ x ⊓ y := by
      apply le_inf
      · apply inf_le_left
      · trans (y ⊓ z)
        · apply inf_le_right
        · apply inf_le_left
    have g2 : x ⊓ (y ⊓ z) ≤ z := by
      trans (y ⊓ z)
      · apply inf_le_right
      · apply inf_le_right
    apply le_inf g1 g2
  apply le_antisymm h1 h2

example : x ⊔ y = y ⊔ x := by
  have h : ∀ a b : α, a ⊔ b ≤ b ⊔ a := by
    intro a b
    apply sup_le le_sup_right le_sup_left
  apply le_antisymm (h x y) (h y x)

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  have h1 : x ⊔ y ⊔ z ≤ x ⊔ (y ⊔ z) := by
    have g1 : x ⊔ y ≤ x ⊔ (y ⊔ z) := by
      apply sup_le
      · apply le_sup_left
      · trans (y ⊔ z)
        · apply le_sup_left
        · apply le_sup_right
    have g2 : z ≤ x ⊔ (y ⊔ z) := by
      trans (y ⊔ z)
      · apply le_sup_right
      · apply le_sup_right
    apply sup_le g1 g2
  have h2 : x ⊔ (y ⊔ z) ≤ x ⊔ y ⊔ z := by
    have g1 : x ≤ x ⊔ y ⊔ z := by
      trans (x ⊔ y)
      · apply le_sup_left
      · apply le_sup_left
    have g2 : y ⊔ z ≤ x ⊔ y ⊔ z := by
      apply sup_le
      · trans (x ⊔ y)
        · apply le_sup_right
        · apply le_sup_left
      · apply le_sup_right
    apply sup_le g1 g2
  apply le_antisymm h1 h2

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  have h1 : x ⊓ (x ⊔ y) ≤ x := inf_le_left
  have h2 : x ≤ x ⊓ (x ⊔ y) := by
    have g1 : x ≤ x := by apply le_refl
    have g2 : x ≤ x ⊔ y := le_sup_left
    apply le_inf g1 g2
  apply le_antisymm h1 h2

theorem absorb2 : x ⊔ x ⊓ y = x := by
  have h1 : x ⊔ x ⊓ y ≤ x := by
    apply sup_le
    · apply le_refl
    · apply inf_le_left
  have h2 : x ≤ x ⊔ x ⊓ y := le_sup_left
  apply le_antisymm h1 h2

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h, inf_comm (a ⊔ b) a, absorb1, inf_comm (a ⊔ b) c, h, ← sup_assoc, inf_comm c a, absorb2, inf_comm]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h, sup_comm (a ⊓ b) a, absorb2, sup_comm (a ⊓ b) c, h, ← inf_assoc, sup_comm c a, absorb1, sup_comm]

end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_right : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

theorem aux1 (h : a ≤ b) : 0 ≤ b - a := by
  rw [← sub_self a]
  apply sub_le_sub_right
  exact h

theorem aux2 (h: 0 ≤ b - a) : a ≤ b := by
  calc
    a = 0 + a := by
      symm
      apply zero_add
    _ ≤ (b - a) + a := by
      apply add_le_add_left h
    _ = b := by
      apply sub_add_cancel b a

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h1 : 0 ≤ (b - a) * c := by
    apply mul_nonneg
    · apply aux1 a b h
    · exact h'
  have h2 : 0 ≤ b*c - a*c := by
    rw [sub_mul] at h1
    exact h1
  apply aux2 (a * c) (b * c) h2

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h : 0 ≤ dist x y + dist x y := by
    calc
      0 = dist x x := by
        symm
        apply dist_self
      _ ≤ dist x y + dist y x := by apply dist_triangle
      _ = dist x y + dist x y := by rw [dist_comm]
  linarith

end
