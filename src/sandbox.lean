import group_theory.group_action group_theory.quotient_group
import group_theory.order_of_element data.zmod.basic

open equiv fintype finset mul_action function
open equiv.perm is_subgroup list quotient_group
universes u v w
variables {G : Type u} {α : Type v} {β : Type w} [group G]


namespace mul_action
variables [mul_action G α]

variable a : α
variable z : α
variable x : G
variable hz : z ∈ orbit G a
variable hz₁ : ∀ (y : orbit G a), y = ⟨z, hz⟩

#check (subtype.mk.inj (hz₁ ⟨x • a, mem_orbit a x⟩))
#check (hz₁ ⟨x • a, mem_orbit _ _⟩)
#check mem_orbit
definition l : {x : α  // x ∈ orbit G a} := ⟨z, hz⟩ 
#check @subtype.mk.inj
#check {x : α  // x ∈ orbit G a}

end mul_action
