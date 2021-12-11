lemma lt_aux_one (a b : mynat) : a ≤ b ∧ ¬ (b ≤ a) → succ a ≤ b :=
begin
intro h,
cases h with ab nba,
cases ab with c hc,
cases c with n,
rw add_zero at hc,
rw hc,
exfalso,
apply nba,
rw hc,
exact le_refl a,
rw hc,
rw add_succ,
rw ← succ_add,
use n,
refl,



end