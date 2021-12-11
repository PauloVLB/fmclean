lemma lt_aux_two (a b : mynat) : succ a ≤ b → a ≤ b ∧ ¬ (b ≤ a) :=
begin
intro sab,
split,
cases sab with c hc,
rw hc,
rw succ_add,
rw ← add_succ,
use succ c,
refl,
intro nba,
have saa := le_trans (succ a) b a sab nba,
exact not_succ_le_self a saa,


end