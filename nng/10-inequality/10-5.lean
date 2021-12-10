theorem le_trans (a b c : mynat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
begin
cases hab with d hd,
cases hbc with e he,
rw he,
rw hd,
use d + e,
rw add_assoc,
refl,


end