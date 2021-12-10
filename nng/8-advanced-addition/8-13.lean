lemma ne_succ_self (n : mynat) : n ≠ succ n :=
begin
intro h,
induction n with h hd,
apply zero_ne_succ 0,
exact h,
have hh := succ_inj h,
exact hd hh,
end