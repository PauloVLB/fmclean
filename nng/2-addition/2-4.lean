lemma add_comm (a b : mynat) : a + b = b + a :=
begin
induction a with h hd,
rw zero_add,
rw add_zero,
refl,
rw succ_add,
rw add_succ,
rw hd,
refl,

end