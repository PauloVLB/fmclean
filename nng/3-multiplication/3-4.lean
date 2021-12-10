lemma mul_add (t a b : mynat) : t * (a + b) = t * a + t * b :=
begin
induction b with h hd,
rw add_zero,
rw mul_zero,
rw add_zero,
refl,
rw add_succ,
rw mul_succ,
rw hd,
rw mul_succ,
rw add_assoc,
refl,


end