import group_theory.group_action group_theory.quotient_group
import group_theory.order_of_element data.zmod.basic
import group_theory.coset
open equiv fintype finset mul_action function
open equiv.perm is_subgroup list quotient_group
universes u v w
variables {G : Type u} {α : Type v} {β : Type w} [group G]

local attribute [instance, priority 10] subtype.fintype set_fintype classical.prop_decidable

namespace mul_action
variables [mul_action G α]

lemma mem_fixed_points_iff_card_orbit_eq_one {a : α}
  [fintype (orbit G a)] : a ∈ fixed_points G α ↔ card (orbit G a) = 1 :=
begin
  rw [fintype.card_eq_one_iff, mem_fixed_points],
  split,
  { assume h,
    existsi (⟨a, mem_orbit_self _⟩ : {j //  j ∈ orbit G a}),
    exact   λ ⟨b, ⟨x, hx⟩⟩, subtype.eq $ by simp [h x, hx.symm] },
  { assume h x,
    rcases h with ⟨⟨z, hz⟩, hz₁⟩,
    exact calc x • a = z : subtype.mk.inj (hz₁ ⟨x • a, mem_orbit _ _⟩)
      ... = a : (subtype.mk.inj (hz₁ ⟨a, mem_orbit_self _⟩)).symm }
end

#check @subtype.mk.inj
#check mem_orbit_self

lemma card_modeq_card_fixed_points [fintype α] [fintype G] [fintype (fixed_points G α)]
  {p n : ℕ} (hp : nat.prime p) (h : card G = p ^ n) : card α ≡ card (fixed_points G α) [MOD p] :=
calc card α = card (Σ y : quotient (orbit_rel G α), {x // quotient.mk' x = y}) :
  card_congr (sigma_preimage_equiv (@quotient.mk' _ (orbit_rel G α))).symm
... = univ.sum (λ a : quotient (orbit_rel G α), card {x // quotient.mk' x = a}) : card_sigma _
... ≡ (@univ (fixed_points G α) _).sum (λ _, 1) [MOD p] :
begin
  rw [← zmodp.eq_iff_modeq_nat hp, sum_nat_cast, sum_nat_cast],
  refine eq.symm (sum_bij_ne_zero (λ a _ _, quotient.mk' a.1)
    (λ _ _ _, mem_univ _)
    (λ a₁ a₂ _ _ _ _ h,
      subtype.eq ((mem_fixed_points' α).1 a₂.2 a₁.1 (quotient.exact' h)))
      (λ b, _)
      (λ a ha _, by rw [← mem_fixed_points_iff_card_orbit_eq_one.1 a.2];
        simp only [quotient.eq']; congr)),
  { refine quotient.induction_on' b (λ b _ hb, _),
    have : card (orbit G b) ∣ p ^ n,
    { rw [← h, fintype.card_congr (orbit_equiv_quotient_stabilizer G b)];
      exact card_quotient_dvd_card _ },
    rcases (nat.dvd_prime_pow hp).1 this with ⟨k, _, hk⟩,
    have hb' :¬ p ^ 1 ∣ p ^ k,
    { rw [nat.pow_one, ← hk, ← nat.modeq.modeq_zero_iff, ← zmodp.eq_iff_modeq_nat hp,
        nat.cast_zero, ← ne.def],
      exact eq.mpr (by simp only [quotient.eq']; congr) hb },
    have : k = 0 := nat.le_zero_iff.1 (nat.le_of_lt_succ (lt_of_not_ge (mt (nat.pow_dvd_pow p) hb'))),
    refine ⟨⟨b, mem_fixed_points_iff_card_orbit_eq_one.2 $ by rw [hk, this, nat.pow_zero]⟩, mem_univ _,
      by simp [zero_ne_one], rfl⟩ }
end
... = _ : by simp; refl

end mul_action

lemma quotient_group.card_preimage_mk [fintype G] (s : set G) [is_subgroup s]
  (t : set (quotient s)) : fintype.card (quotient_group.mk ⁻¹' t) =
  fintype.card s * fintype.card t :=
by rw [← fintype.card_prod, fintype.card_congr
  (preimage_mk_equiv_subgroup_times_set _ _)]

namespace sylow

open nat

def dlogn (p : ℕ) : ℕ → ℕ
| 0     := 0
| (a+1) := if h : p > 1 then
  have (a + 1) / p < a + 1, from div_lt_self dec_trivial h,
    if p ∣ (a + 1) then dlogn ((a + 1) / p) + 1 else 0
  else 0

lemma dlogn_dvd {p : ℕ} : ∀ a, p > 1 → p ^ dlogn p a ∣ a
| 0     := λ _, dvd_zero _
| (a+1) := λ h,
have (a + 1) / p < a + 1, from div_lt_self dec_trivial h,
begin
  rw [dlogn, if_pos h],
  split_ifs with hd,
  { rw nat.pow_succ,
    conv { to_rhs, rw ← nat.div_mul_cancel hd },
    exact mul_dvd_mul (dlogn_dvd _ h) (dvd_refl _) },
  { simp }
end

lemma not_dvd_of_gt_dlogn {p : ℕ} : ∀ {a m}, a > 0 → p > 1 → m > dlogn p a → ¬p ^ m ∣ a
| 0     := λ m h, (lt_irrefl _ h).elim
| (a+1) := λ m h hp hm ,
have (a + 1) / p < a + 1, from div_lt_self dec_trivial hp,
begin
  rw [dlogn, if_pos hp] at hm,
  split_ifs at hm with hd,
  { have hmsub : succ (m - 1) = m := 
      succ_sub (show 1 ≤ m, from (lt_of_le_of_lt (nat.zero_le _) hm)) ▸ 
      (succ_sub_one m).symm,
    have := @not_dvd_of_gt_dlogn ((a + 1) / p) (m - 1)
      (pos_of_mul_pos_left (by rw nat.mul_div_cancel' hd; exact nat.succ_pos _) (nat.zero_le p))
      hp (lt_of_succ_lt_succ (hmsub.symm ▸ hm)),
    rwa [← nat.mul_dvd_mul_iff_right (lt_trans dec_trivial hp), nat.div_mul_cancel hd,
      ← nat.pow_succ, hmsub] at this },
  { assume h,
    exact hd (calc p = p ^ 1 : (nat.pow_one _).symm
      ... ∣ p ^ m : nat.pow_dvd_pow p hm
      ... ∣ a + 1 : h) }
end

lemma pow_dvd_of_dvd_mul {p : ℕ} : ∀ {m n k : ℕ} (hp : prime p) (hd : p ^ m ∣ n * k) (hk : ¬p ∣ k),
  p ^ m ∣ n
| 0     := by simp
| (m+1) := λ n k hp hd hk,
have hpnk : p ∣ n * k := calc p = p ^ 1 : by rw nat.pow_one
  ... ∣ p ^ (m + 1) : nat.pow_dvd_pow _ (succ_pos _)
  ... ∣ n * k : by assumption,
have hpn : p ∣ n := or.resolve_right (hp.dvd_mul.1 hpnk) hk,
have p ^ m ∣ (n / p) * k := nat.dvd_of_mul_dvd_mul_right hp.pos $
  by rwa [mul_right_comm, nat.div_mul_cancel hpn, ← nat.pow_succ],
by rw [nat.pow_succ, ← nat.div_mul_cancel hpn];
  exact mul_dvd_mul_right (pow_dvd_of_dvd_mul hp this hk) _

lemma eq_dlogn_of_dvd_of_succ_not_dvd {a p n : ℕ} (hp : 1 < p) (h₁ : p ^ n ∣ a) (h₂ : ¬p ^ succ n ∣ a) : 
  n = dlogn p a :=
have ha : 0 < a := nat.pos_of_ne_zero (λ h, by simpa [h] using h₂),
le_antisymm (le_of_not_gt $ λ h, not_dvd_of_gt_dlogn ha hp h h₁)
  (le_of_not_gt $ λ h, h₂ $ calc p ^ succ n ∣ p ^ dlogn p a : nat.pow_dvd_pow _ h
    ... ∣ _ : dlogn_dvd _ hp)

lemma dlogn_eq_of_not_dvd {a b p  : ℕ} (hp : prime p) (hpb : ¬p ∣ b) : dlogn p a = dlogn p (a * b) :=
if ha : a = 0 then by simp [ha, dlogn] else
eq_dlogn_of_dvd_of_succ_not_dvd hp.1 (dvd.trans (dlogn_dvd _ hp.1) (dvd_mul_right _ _))
  (λ h, not_dvd_of_gt_dlogn (nat.pos_of_ne_zero ha)
  hp.1 (lt_succ_self _) (pow_dvd_of_dvd_mul hp h hpb))

lemma not_dvd_div_dlogn {p a : ℕ} (ha : a > 0) (hp : p > 1) : ¬p ∣ a / (p ^ dlogn p a) :=
by rw [← nat.mul_dvd_mul_iff_left (nat.pos_pow_of_pos (dlogn p a) (lt_trans dec_trivial hp)),
    nat.mul_div_cancel' (dlogn_dvd _ hp), ← nat.pow_succ];
  exact not_dvd_of_gt_dlogn ha hp (lt_succ_self _)

open nat.prime

def left_cosets [group α] (s : set α) [is_subgroup s] : Type* := quotient (left_rel s)

local attribute [instance] left_rel set_fintype
open is_subgroup is_submonoid is_group_hom

#check mul_left_cosets

namespace fintype

instance quotient_fintype {α : Type*} [fintype α] (s : setoid α)
  [decidable_eq (quotient s)] : fintype (quotient s) :=
fintype.of_surjective quotient.mk (λ x, quotient.induction_on x (λ x, ⟨x, rfl⟩))

end fintype

local attribute [instance, priority 0] set_fintype classical.prop_decidable

noncomputable instance [fintype G] (H : set G) [is_subgroup H] :  fintype (left_cosets H) := fintype.quotient_fintype (left_rel H)

class is_sylow [fintype G] (H : set G) {p : ℕ} (hp : prime p) extends is_subgroup H : Prop := 
(card_eq : card H = p ^ dlogn p (card G))

lemma card_sylow [fintype G] (H : set G) [f : fintype H] {p : ℕ} (hp : prime p) [is_sylow H hp] :
  card H = p ^ dlogn p (card G) := 
by rw ← is_sylow.card_eq H hp; congr

def conjugate_set (x : G) (H : set G) : set G :=
(λ n, x⁻¹ * n * x) ⁻¹' H

lemma conjugate_set_eq_image (H : set G) (x : G) :
  conjugate_set x H = (λ n, x * n * x⁻¹) '' H :=
eq.symm (congr_fun (set.image_eq_preimage_of_inverse 
  (λ _, by simp [mul_assoc]) (λ _, by simp [mul_assoc])) _)

lemma conjugate_set_eq_preimage (H : set G) (x : G) :
  conjugate_set x H = (λ n, x⁻¹ * n * x) ⁻¹' H := rfl

def mul_left_cosets (L₁ L₂ : set G) [is_subgroup L₂] [is_subgroup L₁]
  (x : L₂) (y : left_cosets L₁) : left_cosets L₁ :=
quotient.lift_on y (λ y, ⟦(x : G) * y⟧) 
  (λ a b (hab : _ ∈ L₁), quotient.sound 
    (show _ ∈ L₁, by rwa [mul_inv_rev, ← mul_assoc, mul_assoc (a⁻¹), inv_mul_self, mul_one]))

instance (L₁ L₂ : set G)  [is_subgroup L₁ ] [is_subgroup L₂] : mul_action L₂ (left_cosets L₁) :=
{ smul := mul_left_cosets L₁ L₂,
  one_smul := λ a, quotient.induction_on' a (λ a, quotient_group.eq.2
    (by simp [is_submonoid.one_mem])),
  mul_smul := λ x y a, quotient.induction_on' a (λ a, quotient_group.eq.2
    (by simp [mul_inv_rev, is_submonoid.one_mem, mul_assoc])) }

namespace hidden
variables (L₁ : set G) (L₂ : set G)
variables [is_subgroup L₁ ] [is_subgroup L₂]
variables [fintype (left_cosets L₁)] [is_subgroup L₂]

#check card (fixed_points (L₂) (left_cosets L₁))
end hidden

#check is_subgroup.group_equiv_quotient_times_subgroup

lemma card_eq_card_cosets_mul_card_subgroup [fintype G] (H : set G) [is_subgroup H] : 
  card G = card (left_cosets H) * card H :=
by rw ← card_prod;
  exact card_congr (is_subgroup.group_equiv_quotient_times_subgroup _)

namespace set

--Braucht man hier wirklich Classical?
lemma eq_of_card_eq_of_subset {s t : set α} [fintype s] [fintype t]
  (hcard : card s = card t) (hsub : s ⊆ t) : s = t :=
classical.by_contradiction (λ h, lt_irrefl (card t)
  (have card s < card t := set.card_lt_card ⟨hsub, h⟩,
    by rwa hcard at this))

end set

lemma conj_inj_left {x : G} : injective (λ (n : G), x * n * x⁻¹) :=
λ a b h, (mul_left_inj x).1 $ (mul_right_inj (x⁻¹)).1 h

open mul_action


lemma sylow_2 [fintype G] {p : ℕ} (hp : nat.prime p)
  (H K : set G) [is_sylow H hp] [is_sylow K hp] :
  ∃ g : G, H = conjugate_set g K :=

--1. Schritt: Index von K berechnen

have hs : card (left_cosets K) = card G / (p ^ dlogn p (card G)) := 
  (nat.mul_right_inj (pos_pow_of_pos (dlogn p (card G)) hp.pos)).1
  $ by rw [← card_sylow K hp, ← card_eq_card_cosets_mul_card_subgroup, card_sylow K hp, 
    nat.div_mul_cancel (dlogn_dvd _ hp.1)],

--2. Schritt:  Index == |FixPunkte| mod p

have hmodeq : card (left_cosets K) ≡ card (fixed_points H (left_cosets K)) [MOD p] := card_modeq_card_fixed_points hp (card_sylow H hp),

have hmodeq2 : card G / (p ^ dlogn p (card G)) ≡ card (fixed_points H (left_cosets K)) [MOD p] := eq.subst hs hmodeq,

--3. Schritt: 0 < |FixedPoints|

have hfixed : 0 < card (fixed_points H (left_cosets K)) := nat.pos_of_ne_zero 
  (λ h, (not_dvd_div_dlogn (fintype.card_pos_iff.2 ⟨(1 : G)⟩) hp.1) 
    $ by rwa [h, nat.modeq.modeq_zero_iff] at hmodeq2),

--4. Schritt: 

let ⟨⟨x, hx⟩⟩ := fintype.card_pos_iff.1 hfixed in
begin
  haveI : is_subgroup K := by apply_instance, --K is sylow -> K is subgroup (Instanzen) (K ist nur Teilmenge von G)
  -- |- ∃ (g : G), H = conjugate_set g K
  revert hx,
  -- |- x ∈ fixed_points (mul_left_cosets K H) → (∃ (g : G), H = conjugate_set g K)
  refine quotient.induction_on x
    (λ x hx, ⟨x, set.eq_of_card_eq_of_subset _ _⟩),
  { -- |- card ↥H = card ↥(conjugate_set x K)
    rw [conjugate_set_eq_image, set.card_image_of_injective _ conj_inj_left,
    card_sylow K hp, card_sylow H hp] },
  { -- |- H ⊆ conjugate_set x K
    assume y hy,
    have : (y⁻¹ * x)⁻¹ * x ∈ K := quotient.exact ((mem_fixed_points' (left_cosets K)).1 hx ⟦y⁻¹ * x⟧ ⟨⟨y⁻¹, inv_mem hy⟩, rfl⟩),
    simp [conjugate_set_eq_preimage, set.preimage, mul_inv_rev, *, mul_assoc] at * }
end

end sylow

--quotient.exact (mem_fixed_points'.1 hx ⟦y⁻¹ * x⟧ ⟨⟨y⁻¹, inv_mem hy⟩, rfl⟩)