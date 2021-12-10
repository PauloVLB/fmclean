lemma pow_add (a m n : mynat) : a ^ (m + n) = a ^ m * a ^ n :=
begin
induction n with h hd,
rw add_zero,
rw pow_zero,
rw mul_one,
refl,
rw add_succ,
rw pow_succ,
rw pow_succ,
rw hd,
rw mul_assoc,
refl,
end