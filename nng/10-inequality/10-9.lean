theorem le_total (a b : mynat) : a ≤ b ∨ b ≤ a :=
begin
induction b with h hd,
right,
exact zero_le a,
cases hd with ah ha,
left,
have als := le_succ a h ah,
exact als,
cases ha with c hc,
cases c with c1,
left,
rw add_zero at hc,
rw hc,
apply le_succ,
exact le_refl h,
right,
use c1,
rw succ_add,
exact hc,


end