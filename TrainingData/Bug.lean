def fun1 (x : Nat) : Nat :=
  aux1 x
where
aux1 (y : Nat) : Nat := y -- Indentation here changes parsing (??)

/-- Doc comment (everything works fine without it) -/
def fun2 (x : Nat) : Nat := x
